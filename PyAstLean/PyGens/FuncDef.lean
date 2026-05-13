import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

/-!
  Translates a Python function definition to a Lean function definition. For now, this is a very basic implementation that only handles simple function definitions with no parameters and a single return statement. The main function is `funcDefSyntax`, which takes a JSON object representing a Python function definition and returns the corresponding Lean syntax.
-/

/-!
## Function definitions

A sample Python AST:

```python
Module(body=[FunctionDef(name='f', args=arguments(posonlyargs=[], args=[arg(arg='n')], kwonlyargs=[], kw_defaults=[], defaults=[]), body=[Assign(targets=[Name(id='m', ctx=Store())], value=BinOp(left=Name(id='n', ctx=Load()), op=Add(), right=Constant(value=1))), Return(value=Name(id='m', ctx=Load()))], decorator_list=[], type_params=[])], type_ignores=[])
```

For the definition:

```python
def f(n):
    m = n + 1
    return m
```
-/

def withFreshVariables {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField
    (·.varNames)
    (fun st varNames => { st with varNames := varNames })
    (HashSet.emptyWithCapacity 100)
    x

def isMainGuardTest (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Compare" =>
      match json.getObjValAs? String "op", json.getObjValAs? Json "left", json.getObjValAs? Json "right" with
      | .ok "eq", .ok leftJson, .ok rightJson =>
          match leftJson.getObjValAs? String "node_type", leftJson.getObjValAs? String "id",
              rightJson.getObjValAs? String "node_type", rightJson.getObjValAs? Json "value" with
          | .ok "Name", .ok "__name__", .ok "Constant", .ok (.str "__main__") => true
          | _, _, _, _ => false
      | _, _, _ => false
  | _ => false

def rangeIterSyntax (iterJson : Json) : PygenM (TSyntax `term) := do
  let .ok iterNodeType := iterJson.getObjValAs? String "node_type" | throwError
    s!"For iterator is missing a node_type field: {iterJson}"
  if iterNodeType == "Call" then
    let .ok funcJson := iterJson.getObjValAs? Json "func" | throwError
      s!"Call iterator is missing a func field: {iterJson}"
    let .ok funcNodeType := funcJson.getObjValAs? String "node_type" | throwError
      s!"Call iterator function is missing a node_type field: {funcJson}"
    if funcNodeType == "Name" then
      let .ok funcName := funcJson.getObjValAs? String "id" | throwError
        s!"Call iterator function is missing an id field: {funcJson}"
      if funcName == "range" then
        let .ok argsJson := iterJson.getObjValAs? Json "args" | throwError
          s!"Call iterator is missing an args field: {iterJson}"
        match argsJson with
        | .arr arr =>
            match arr.size with
            | 1 =>
                let stopCode ← getCode arr[0]! `term
                let pyRangeIdent := mkIdent ``pyRange
                `($pyRangeIdent $stopCode)
            | _ => throwError "Only range(stop) is supported for for-loops right now."
        | _ => throwError s!"Call iterator args field is not an array: {argsJson}"
      else
        getCode iterJson `term
    else
      getCode iterJson `term
  else
    getCode iterJson `term

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

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(def $nameIdent := $valueStx)
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        if ← hasVar nameIdent.getId then
            `(doElem| $nameIdent:ident := $valueStx)
        else
            -- IO.eprintln s!"Variable `{nameIdent.getId}` not found in context, treating as new variable declaration; variables: {(← get).varNames.toList}"  -- Debugging output
            let stx ← `(doElem| let mut $nameIdent:ident := $valueStx)
            addVar nameIdent.getId
            -- IO.eprintln s!"Added variable `{nameIdent.getId}` to context, check: {← hasVar nameIdent.getId}"  -- Debugging output
            return stx
    | _, _ => throwError s!"Unsupported syntax category for Assign node"

/--
`AnnAssign` represents Python's annotated assignment syntax (`x : T = v` or `x : T`).
The remaining declaration-only form is currently treated as a no-op in `do` blocks, and
rejected at top level until the backend grows explicit type-directed declarations.
-/
@[pygen "AnnAssign"]
def annAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            throwError "Declaration-only annotated assignments are not yet supported at top level."
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `command json
    | `doElem, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            `(doElem| let _ := ())
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `doElem json
    | _, _ => throwError s!"Unsupported syntax category for AnnAssign node"

@[pygen "Return"]
def returnSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(doElem| return $valueStx)
    | _, _ => throwError s!"Unsupported syntax category for Return node"

/-- `Pass` is a statement-level no-op in Python, so we lower it to an empty command
or a trivial `do` element. -/
@[pygen "Pass"]
def passSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| let _ := ())
    | _, _ => throwError s!"Unsupported syntax category for Pass node"

@[pygen "Continue"]
def continueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| continue)
    | _, _ => throwError s!"Unsupported syntax category for Continue node"

@[pygen "Break"]
def breakSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| break)
    | _, _ => throwError s!"Unsupported syntax category for Break node"

@[pygen "While"]
def whileSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok test := json.getObjVal? "test" | throwError
          s!"While node does not have a 'test' field or it is not a JSON value: {json}"
        let testStx ← getCode test `term
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"While node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"While node does not have an 'orelse' field or it is not a JSON array: {json}"
        unless orelseElems.isEmpty do
          throwError "Python while-else blocks are not supported."
        let mut bodyStxArray := #[]
        for elem in bodyElems do
            let elemStx ← getCode elem `doElem
            bodyStxArray := bodyStxArray.push elemStx
        `(doElem| while $testStx do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for While node"

@[pygen "AugAssign"]
def augAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"AugAssign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok op := json.getObjValAs? String "op" | throwError
          s!"AugAssign node does not have an 'op' field or it is not a string: {json}"
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"AugAssign node does not have a 'value' field or it is not a JSON value: {json}"
        let targetIdent ← getCode targetJson `ident
        let valueCode ← getCode valueJson `term
        let updated ← match op with
          | "add" => `($targetIdent +ₚ $valueCode)
          | "sub" => `($targetIdent -ₚ $valueCode)
          | "mul" => `($targetIdent *ₚ $valueCode)
          | _ => throwError s!"Unsupported augmented assignment operator: {op}"
        `(doElem| $targetIdent:ident := $updated)
    | _, _ => throwError s!"Unsupported syntax category for AugAssign node"

@[pygen "For"]
def forSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"For node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok iterJson := json.getObjValAs? Json "iter" | throwError
          s!"For node does not have an 'iter' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"For node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"For node does not have an 'orelse' field or it is not a JSON array: {json}"
        unless orelseElems.isEmpty do
          throwError "Python for-else blocks are not supported."
        let targetIdent ← getCode targetJson `ident
        let iterCode ← rangeIterSyntax iterJson
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        `(doElem| for $targetIdent:ident in $iterCode do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for For node"

@[pygen "If"]
def ifSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        let testStx ← getCode testJson `term
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        let mut orelseStxArray := #[]
        for elem in orelseElems do
          let elemStx ← getCode elem `doElem
          orelseStxArray := orelseStxArray.push elemStx
        if orelseStxArray.isEmpty then
          `(doElem| if $testStx then
              $[$bodyStxArray:doElem]*
          -- add `else pure ()` for monadic
            else
              pure ()
          )
        else
          `(doElem| if $testStx then
              $[$bodyStxArray:doElem]*
            else
              $[$orelseStxArray:doElem]*)
    | `command, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        unless isMainGuardTest testJson do
          throwError "Only top-level `if __name__ == \"__main__\":` blocks are supported."
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        let mainIdent := mkIdent `main
        let idRunIdent := mkIdent ``Id.run
        `(command| def $mainIdent := $idRunIdent do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for If node"

/--
Reformat a list of Json to an object with `node_type` the `node_type` of the original list's first element with "Head_" prefixed, and `args` the original list. This is needed to handle the case where the body of a function definition is a list of statements, which is represented as a JSON array in the input, but we want to treat it as a single JSON object with a specific `node_type` in our code generation. We use this to try to generate *pure* code, i.e., not Monadic code.
-/
def splitList : List Json -> PygenM Json
| [] => throwError "Cannot split an empty list"
| (first :: rest) => do
    let .ok nodeType := first.getObjValAs? String "node_type" | throwError
      s!"First element of list does not have a 'node_type' field or it is not a string: {first}"
    let newNodeType := "Head_" ++ nodeType
    let newJson := first.mergeObj (Json.mkObj [("node_type", newNodeType), ("rest", toJson rest)])
    return newJson

def pureFunctionBodySyntax (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let spl ← splitList bodyElems.toList
  withoutCheck do
    getCode spl `term

def monadicFunctionBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  for elem in bodyElems do
    let elemStx ← withoutCheck do
      getCode elem `doElem
    bodyStxArray := bodyStxArray.push elemStx
  return bodyStxArray

def functionArgIdents (json : Json) : PygenM (Array (TSyntax `ident)) := do
  let .ok args := json.getObjVal? "args" | throwError
    s!"FuncDef node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
    s!"FuncDef args does not have an 'args' field or it is not a JSON value: {args}"
  let mut argIdents := #[]
  for arg in argsArray do
    let .ok argName := arg.getObjValAs? String "arg" | throwError
      s!"FuncDef argument does not have an 'arg' field or it is not a string: {arg}"
    argIdents := argIdents.push (mkIdent argName.toName)
  return argIdents

def functionBodyElems (json : Json) : PygenM (Array Json) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"FuncDef node does not have a 'body' field or it is not a JSON value: {json}"
  return bodyElems

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argIdents ← functionArgIdents json
        let bodyElems ← functionBodyElems json
        try
          -- Attempt to generate pure code by treating the body as a single unit and generating syntax for it directly, which will allow us to generate non-monadic code if the body is simple enough (e.g., a single return statement). If this fails, we will fall back to generating monadic code by generating syntax for each element of the body separately.
          let bodyStx ← pureFunctionBodySyntax bodyElems
          let t ← `(def $nameIdent := fun $argIdents* ↦ $bodyStx)
          return t
        catch e =>
          IO.eprintln s!"Could not generate pure function: {← e.toMessageData.toString}"
        let bodyStxArray ← monadicFunctionBodySyntax bodyElems
        let idRunIdent := mkIdent ``Id.run
        if argIdents.isEmpty then
          `(def $nameIdent := $idRunIdent do
              $[$bodyStxArray:doElem]*)
        else
          let cmd ← `(def $nameIdent := fun $argIdents* ↦ $idRunIdent do
              $[$bodyStxArray:doElem]*)
          -- IO.eprintln s!"Generated (monadic) syntax for FunctionDef node: \n{← PrettyPrinter.ppCommand cmd}" -- Debugging output
          return cmd
    | `term, json => do
        let argIdents ← functionArgIdents json
        let bodyElems ← functionBodyElems json
        try
          let bodyStx ← pureFunctionBodySyntax bodyElems
          `(fun $argIdents* ↦ $bodyStx)
        catch e =>
          IO.eprintln s!"Could not generate pure function term: {← e.toMessageData.toString}"
          let bodyStxArray ← monadicFunctionBodySyntax bodyElems
          let idRunIdent := mkIdent ``Id.run
          `(fun $argIdents* ↦ $idRunIdent do
              $[$bodyStxArray:doElem]*)
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

@[pygen "Head_Return"]
def returnHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ←
          withoutCheck do
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

-- #check sumToNWithRec'
-- #check Id.run
-- #print Id.run
-- #print Id
