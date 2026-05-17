import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Utils
import PyAstLean.PyGens.Assign
import PyAstLean.PyGens.ControlFlow
import PyAstLean.PyGens.ListComp
import PyAstLean.PyGens.Match
import PyAstLean.PyGens.Exceptions

open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

/-!
  Translates Python function definitions and the remaining module-level glue.
  Feature-specific statement lowering lives in the smaller files under `PyGens/`.
-/

@[pygen "Module"]
def moduleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let some first := bodyElems[0]? | throwError "Cannot translate an empty module to a term."
        unless bodyElems.size == 1 do
          throwError "Module-to-term translation requires exactly one top-level statement."
        withFreshVariables do
          getCode first `term
    | `command, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let mut cmds : Array (TSyntax `command) := #[]
        for elem in bodyElems do
          let elemStx ← withFreshVariables do
            getCode elem `command
          cmds := cmds.push elemStx
        return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
    | _, _ => throwError s!"Unsupported syntax category for Module node"

/-- Map a simple Python annotation JSON node to a Lean type term when we know a direct runtime type. -/
partial def functionArgTypeSyntax? (annotationJson : Json) : PygenM (Option (TSyntax `term)) := do
  let .ok nodeType := annotationJson.getObjValAs? String "node_type" | throwError
    s!"Function argument annotation is missing a 'node_type' field: {annotationJson}"
  match nodeType with
  | "Name" =>
      let .ok id := annotationJson.getObjValAs? String "id" | throwError
        s!"Function argument annotation is missing an 'id' field: {annotationJson}"
      match id with
      | "int" | "Int" => return some (mkIdent ``Int)
      | "bool" | "Bool" => return some (mkIdent ``Bool)
      | "str" | "String" => return some (mkIdent ``String)
      | "float" | "Float" => return some (mkIdent ``Rat)
      | "Any" => return none -- let Lean handle the type inference for now
      | _ => return none
  | "Subscript" =>
      let .ok valueJson := annotationJson.getObjValAs? Json "value" | throwError
        s!"Function argument subscript annotation is missing a 'value' field: {annotationJson}"
      let .ok sliceJson := annotationJson.getObjValAs? Json "slice" | throwError
        s!"Function argument subscript annotation is missing a 'slice' field: {annotationJson}"
      match valueJson.getObjValAs? String "node_type", valueJson.getObjValAs? String "id" with
      | .ok "Name", .ok "list" =>
          match ← functionArgTypeSyntax? sliceJson with
          | some elemTy => return some (← `(List $elemTy))
          | none => return none
      | .ok "Name", .ok "dict" =>
          match sliceJson.getObjValAs? String "node_type" with
          | .ok "Tuple" =>
              let .ok elts := sliceJson.getObjValAs? (Array Json) "elts" | throwError
                s!"Dictionary annotation tuple is missing an 'elts' field: {sliceJson}"
              match elts[0]?, elts[1]? with
              | some keyJson, some valJson =>
                  match ← functionArgTypeSyntax? keyJson, ← functionArgTypeSyntax? valJson with
                  | some keyTy, some valTy => return some (← `(Std.HashMap $keyTy $valTy))
                  | _, _ => return none
              | _, _ => return none
          | _ => return none
      | _, _ => return none
  | _ => return none

/-- Read Python function parameters as Lean idents plus any simple type annotations we can preserve. -/
def functionArgInfos (json : Json) : PygenM (Array (TSyntax `ident × Option (TSyntax `term))) := do
  let .ok args := json.getObjVal? "args" | throwError
    s!"FuncDef node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
    s!"FuncDef args does not have an 'args' field or it is not a JSON value: {args}"
  let mut argInfos := #[]
  for arg in argsArray do
    let .ok argName := arg.getObjValAs? String "arg" | throwError
      s!"FuncDef argument does not have an 'arg' field or it is not a string: {arg}"
    let annotation? := jsonFieldOption arg "annotation"
    let ty? ← match annotation? with
      | some annotationJson => functionArgTypeSyntax? annotationJson
      | none => pure none
    argInfos := argInfos.push (mkIdent argName.toName, ty?)
  return argInfos

def functionBodyElems (json : Json) : PygenM (Array Json) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"FuncDef node does not have a 'body' field or it is not a JSON value: {json}"
  return bodyElems

/-- Check whether a JSON subtree references a given variable name. -/
partial def jsonReferencesName (json : Json) (target : String) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
    | .ok "Name", .ok id => id == target
    | _, _ => false
  if directMatch then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonReferencesName elem target)
    | .obj fields => fields.toList.any (fun (_, value) => jsonReferencesName value target)
    | _ => false

/-- Build the Lean value for a Python function body, using a pure term when possible and
falling back to `do` notation for effectful bodies. This helper is reused for top-level
definitions, nested local functions, and `Head_FunctionDef` threading. -/
def functionValueSyntax (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (bodyElems : Array Json) :
    PygenM (TSyntax `term) := do
  let usesExceptions := bodyNeedsExceptionMonad bodyElems
  let mkLambda (body : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut result := body
    for (argIdent, ty?) in argInfos.toList.reverse do
      result ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $result)
        | none => `(fun $argIdent ↦ $result)
    pure result
  if usesExceptions then
    let bodyStxArray ← monadicFunctionBodySyntax bodyElems
    let exceptIdent := mkIdent ``PyAstLean.PyExcept
    let exceptBody ← `(((do
          $[$bodyStxArray:doElem]*) : $exceptIdent _))
    if argInfos.isEmpty then
      pure exceptBody
    else
      mkLambda exceptBody
  else
    try
      let bodyStx ← pureFunctionBodySyntax bodyElems
      if argInfos.isEmpty then
        pure bodyStx
      else
        mkLambda bodyStx
    catch e =>
      IO.eprintln s!"Could not generate pure function term: {← e.toMessageData.toString}"
      let bodyStxArray ← monadicFunctionBodySyntax bodyElems
      let idRunIdent := mkIdent ``Id.run
      if argInfos.isEmpty then
        `($idRunIdent do
            $[$bodyStxArray:doElem]*)
      else
        mkLambda (← `($idRunIdent do
            $[$bodyStxArray:doElem]*))

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        let valueStx ← functionValueSyntax argInfos bodyElems
        `(def $nameIdent := $valueStx)
    | `term, json => do
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        functionValueSyntax argInfos bodyElems
    | `doElem, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        let valueStx ← functionValueSyntax argInfos bodyElems
        `(doElem| let $nameIdent := $valueStx)
    | kind, _ => throwError s!"Unsupported syntax category `{kind}` for FuncDef node"

@[pygen "Head_Assign"]
def assignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assign node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        `(let $nameIdent := $valueStx
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_Assign node"

@[pygen "Head_AnnAssign"]
def annAssignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
              s!"AnnAssign node does not have a 'rest' field or it is not a JSON value: {json}"
            let splitRest ← splitList rest
            withoutCheck do
              getCode splitRest `term
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Head_Assign")]
            let json := targetJson.mergeObj json
            assignHeadSyntax `term json
    | _, _ => throwError s!"Unsupported syntax category for Head_AnnAssign node"

@[pygen "Head_Pass"]
def passHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Pass node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        withoutCheck do
          getCode splitRest `term
    | _, _ => throwError s!"Unsupported syntax category for Head_Pass node"

@[pygen "Head_FunctionDef"]
def functionDefHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"FuncDef node does not have a 'rest' field or it is not a JSON value: {json}"
        let valueStx ← functionValueSyntax argInfos bodyElems
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        `(let $nameIdent := $valueStx
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_FunctionDef node"

@[pygen "Head_If"]
def ifHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"If node does not have a 'rest' field or it is not a JSON value: {json}"
        if !rest.isEmpty &&
            (!statementListDefinitelyReturns bodyElems.toList ||
              !statementListDefinitelyReturns orelseElems.toList) then
          throwError
            "If branches that fall through into later statements require monadic lowering."
        let testStx ← getCode testJson `term
        let thenBranch ← withoutCheck do
          let splitThen ← splitList (bodyElems.toList ++ rest)
          getCode splitThen `term
        let elseTail := if orelseElems.isEmpty then rest else orelseElems.toList ++ rest
        let elseBranch ← withoutCheck do
          let splitElse ← splitList elseTail
          getCode splitElse `term
        `(if $testStx then $thenBranch else $elseBranch)
    | _, _ => throwError s!"Unsupported syntax category for Head_If node"

@[pygen "Head_Match"]
def matchHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok subjectJson := json.getObjValAs? Json "subject" | throwError
          s!"Match node does not have a 'subject' field or it is not a JSON value: {json}"
        let .ok casesJson := json.getObjValAs? (Array Json) "cases" | throwError
          s!"Match node does not have a 'cases' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Match node does not have a 'rest' field or it is not a JSON value: {json}"
        let subjectTerm ← getCode subjectJson `term
        matchCaseTermSyntax subjectTerm casesJson.toList rest
    | _, _ => throwError s!"Unsupported syntax category for Head_Match node"

@[pygen "Head_Return"]
def returnHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← withoutCheck do
          getCode value `term
        return valueStx
    | _, _ => throwError s!"Unsupported syntax category for Head_Return node"

def f := fun n =>
      let x := n -ₚ 1
      let y := x *ₚ 2
      x +ₚ y

def f' := fun n =>
    Id.run do
      let mut x := n -ₚ 1
      let y := x *ₚ 2
      x := y -ₚ 1
      return x +ₚ y

def sumToNWithRec (n: Nat) : Nat :=
  let rec sumToN (n: Nat) :=
    match n with
    | 0 => 0
    | m + 1 =>  sumToN m + (m + 1)
  sumToN n

def sumToNWithRec' (n: Nat)  := Id.run do
    let mut sum := 0
    let mut i := 0
    while i < n do
      sum := sum + (i + 1)
      i := i + 1
    return sum

end PyAstLean
