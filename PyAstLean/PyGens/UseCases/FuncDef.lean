import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Core.Utils
import PyAstLean.PyGens.Core.Assign
import PyAstLean.PyGens.UseCases.ControlFlow
import PyAstLean.PyGens.UseCases.ListComp
import PyAstLean.PyGens.UseCases.Match
import PyAstLean.PyGens.UseCases.Exceptions

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
          cmds := appendCommandSyntax cmds elemStx
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
      | "float" | "Float" => return some (mkIdent ``Float)
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

/-- Read a Python function return annotation when it maps cleanly to a Lean runtime type. -/
def functionReturnTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match jsonFieldOption json "returns" with
  | some returnJson => functionArgTypeSyntax? returnJson
  | none => pure none

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

/-- Does assigning to this target node mutate the variable `name`? Covers a bare `Name`, tuple/
list unpacking, `Starred`, and a `Subscript`/`Attribute` whose base (recursively) is `name`
(`a[i] = …` reassigns the immutable-value container `a`, so it mutates `a`). -/
partial def assignTargetMutatesName (target : Json) (name : String) : Bool :=
  match target.getObjValAs? String "node_type" with
  | .ok "Name" => target.getObjValAs? String "id" == .ok name
  | .ok "Tuple" | .ok "List" =>
      match target.getObjValAs? (Array Json) "elts" with
      | .ok elts => elts.any (fun e => assignTargetMutatesName e name)
      | _ => false
  | .ok "Starred" | .ok "Subscript" | .ok "Attribute" =>
      (target.getObjVal? "value").toOption.any (fun v => assignTargetMutatesName v name)
  | _ => false

/-- Python list/set/dict methods that mutate their receiver in place. Codegen lowers each as a
reassignment of the (immutable-value) receiver, so a parameter used as the receiver of one of
these must be shadowed by `let mut`. Over-inclusion is harmless (an unused shadow). -/
def inPlaceMutatingMethods : List String :=
  [ "append", "extend", "insert", "remove", "pop", "clear", "sort", "reverse",
    "add", "discard", "update", "setdefault", "popitem",
    "intersection_update", "difference_update", "symmetric_difference_update",
    "appendleft", "popleft", "appendright" ]

/-- Is `name` mutated (an `=`, augmented `op=`, annotated assignment, or `for` target — including
unpacking and subscript-assignment) anywhere in this subtree, without descending into a nested
function/lambda/class scope (which rebinds the name in a separate scope)? Used to decide which
function parameters must be shadowed by `let mut` so the monadic body can reassign them. -/
partial def jsonMutatesName (json : Json) (name : String) : Bool :=
  match json with
  | .arr elems => elems.toList.any (fun e => jsonMutatesName e name)
  | .obj fields =>
      match json.getObjValAs? String "node_type" with
      | .ok "FunctionDef" | .ok "AsyncFunctionDef" | .ok "Lambda" | .ok "ClassDef" => false
      | nodeType =>
          let mutatedHere :=
            match nodeType with
            | .ok "Assign" | .ok "AugAssign" | .ok "AnnAssign" | .ok "For" =>
                (json.getObjVal? "target").toOption.any (fun t => assignTargetMutatesName t name)
            | .ok "Delete" =>
                -- `del name[i]` rebuilds and reassigns the container, so it mutates `name`.
                match (json.getObjVal? "targets").toOption.bind (·.getArr?.toOption) with
                | some targets => targets.any (fun t => assignTargetMutatesName t name)
                | none => false
            | .ok "Call" =>
                -- An in-place mutating method (`name.append(x)`, `name.add(x)`, …) is lowered as a
                -- reassignment of the receiver, so it mutates `name`.
                match (json.getObjVal? "func").toOption with
                | some funcJson =>
                    funcJson.getObjValAs? String "node_type" == .ok "Attribute"
                      && (match funcJson.getObjValAs? String "attr" with
                          | .ok m => inPlaceMutatingMethods.contains m
                          | _ => false)
                      && (funcJson.getObjVal? "value").toOption.any
                          (fun recv => assignTargetMutatesName recv name)
                | none => false
            | _ => false
          mutatedHere || fields.toList.any (fun (_, v) => jsonMutatesName v name)
  | _ => false

/-- Build the Lean value for a Python function body, using a pure term when possible and
falling back to `do` notation for effectful bodies. This helper is reused for top-level
definitions, nested local functions, and `Head_FunctionDef` threading.

The body is lowered against a fresh variable set (`withFreshVariables`) so locals declared
inside a nested function do not leak into the enclosing scope's `let`/`let mut` tracking — a
leak would otherwise cause a later same-named outer assignment to be emitted as a reassignment
of a variable that was never declared `let mut`. -/
def functionValueSyntax (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (bodyElems : Array Json) :
    PygenM (TSyntax `term) := withFreshVariables do
  let usesExceptions := bodyNeedsExceptionMonad bodyElems
  let usesIO := !usesExceptions && bodyNeedsIOMonad bodyElems
  let mkLambda (body : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut result := body
    for (argIdent, ty?) in argInfos.toList.reverse do
      result ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $result)
        | none => `(fun $argIdent ↦ $result)
    pure result
  -- A Lean function parameter is an immutable binder, but Python lets a body reassign or
  -- augment its parameters (`i -= 1`, `a[k] = v`). For each mutated parameter, register it and
  -- emit a `let mut p := p` shadow at the top of the (monadic) body, then reassignments resolve
  -- against the mutable shadow. Pure bodies never mutate, so this prelude is empty for them.
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  if usesExceptions then
    let bodyStxArray ← monadicFunctionBodySyntax bodyElems
    let exceptIdent := mkIdent ``PyAstLean.PyExcept
    let exceptBody ← `(((do
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*) : $exceptIdent _))
    if argInfos.isEmpty then
      pure exceptBody
    else
      mkLambda exceptBody
  else if usesIO then
    let bodyStxArray ← monadicFunctionBodySyntax bodyElems
    let ioIdent := mkIdent ``IO
    let ioBody ← `(((do
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*) : $ioIdent _))
    if argInfos.isEmpty then
      pure ioBody
    else
      mkLambda ioBody
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
            $[$paramPrelude:doElem]*
            $[$bodyStxArray:doElem]*)
      else
        mkLambda (← `($idRunIdent do
            $[$paramPrelude:doElem]*
            $[$bodyStxArray:doElem]*))

/-- Build a lambda-wrapped monadic body term without adding an inner effect cast. -/
def functionMonadicValueNoCast (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let mut result ← `(do
    $[$bodyStxArray:doElem]*)
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- Build a function type like `A → B → IO _` when every argument type is known. -/
def functionArrowTypeSyntax? (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (codomain : TSyntax `term) : PygenM (Option (TSyntax `term)) := do
  let mut result := codomain
  for (_, ty?) in argInfos.toList.reverse do
    match ty? with
    | some ty =>
        result ← `($ty → $result)
    | none =>
        return none
  return some result

/--
For top-level effectful defs, prefer putting the effect in the signature instead of on
the body cast when the argument types are known.
-/
def functionCommandWithEffectSignature? (nameIdent : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (json : Json) :
    PygenM (Option (TSyntax `command)) := do
  let bodyElems ← functionBodyElems json
  let returnTy? ← functionReturnTypeSyntax? json
  if bodyNeedsIOMonad bodyElems then
    match returnTy? with
    | none => return none
    | some retTy =>
        let ioIdent := mkIdent ``IO
        let codomain ← `($ioIdent $retTy)
        match ← functionArrowTypeSyntax? argInfos codomain with
        | some fullTy =>
            let valueStx ← functionMonadicValueNoCast argInfos bodyElems
            return some (← `(command| def $nameIdent : $fullTy := $valueStx))
        | none =>
            return none
  else if bodyNeedsExceptionMonad bodyElems then
    match returnTy? with
    | none => return none
    | some retTy =>
        let exceptIdent := mkIdent ``PyAstLean.PyExcept
        let codomain ← `($exceptIdent $retTy)
        match ← functionArrowTypeSyntax? argInfos codomain with
        | some fullTy =>
            let valueStx ← functionMonadicValueNoCast argInfos bodyElems
            return some (← `(command| def $nameIdent : $fullTy := $valueStx))
        | none =>
            return none
  else
    return none

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let cmd ← match ← functionCommandWithEffectSignature? nameIdent argInfos json with
          | some cmd => pure cmd
          | none =>
              let bodyElems ← functionBodyElems json
              let valueStx ← functionValueSyntax argInfos bodyElems
              -- take care of recursion function Type
              if bodyElems.any (jsonReferencesName · name) then
                match ← functionReturnTypeSyntax? json with
                | some retTy =>
                    match ← functionArrowTypeSyntax? argInfos retTy with
                    | some fullTy => `(partial def $nameIdent : $fullTy := $valueStx)
                    | none => `(partial def $nameIdent := $valueStx)
                | none => `(partial def $nameIdent := $valueStx)
              else
                `(def $nameIdent := $valueStx)
        -- Python's leading-underscore convention (`def _foo`) maps to a Lean `private def`.
        applyPrivacy name cmd
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
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assign node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        match ← tupleAssignTargetNames? target with
        | some idents => do
            let n := idents.size
            let valueStx ← getCode value `term
            let unpackTmpIdent := mkIdent (← freshName `__unpack_pair)
            -- A `Tuple` literal or a tuple-returning function call both produce a `Prod` (use
            -- `Prod.fst`/`Prod.snd`); list-returning RHSs are pre-split into subscripts and never
            -- reach native unpacking (see Core/Assign.lean for the same reasoning).
            let isTuple := jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            let mut result := tailCode
            for i in (List.range n).reverse do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              result ← `(let $(idents[i]!) := $acc
                $result)
            `(let $unpackTmpIdent := $valueStx
              $result)
        | none => do
            let nameIdent ← getCode target `ident
            let valueStx ← getCode value `term
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
