import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic

open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

def withFreshVariables {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField
    (·.varNames)
    (fun st varNames => { st with varNames := varNames })
    (HashSet.emptyWithCapacity 100)
    x

/-- Pick a fresh local name for generated bindings. -/
partial def freshName (base : Name) (idx : Nat := 0) : PygenM Name := do
  let candidate :=
    if idx == 0 then base else base.appendIndexAfter idx
  if ← hasVar candidate then
    freshName base (idx + 1)
  else
    addVar candidate
    pure candidate

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

/-- Reusable syntax nodes for boolean literals in generated terms. -/
def trueTerm : TSyntax `term := mkIdent ``true

def falseTerm : TSyntax `term := mkIdent ``false

/-- Read the `node_type` tag from a JSON AST node when present. -/
def jsonNodeType? (json : Json) : Option String :=
  json.getObjValAs? String "node_type" |>.toOption

/--
Reformat a list of Json to an object with `node_type` the `node_type` of the original list's
first element with "Head_" prefixed, and `rest` the remaining statements.
-/
def splitList : List Json -> PygenM Json
| [] => throwError "Cannot split an empty list"
| (first :: rest) => do
    let .ok nodeType := first.getObjValAs? String "node_type" | throwError
      s!"First element of list does not have a 'node_type' field or it is not a string: {first}"
    let newNodeType := "Head_" ++ nodeType
    let newJson := first.mergeObj (Json.mkObj [("node_type", newNodeType), ("rest", toJson rest)])
    return newJson

/-- Try to compile a function body as one pure term by threading the remaining statements
through `Head_*` nodes. -/
def pureFunctionBodySyntax (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let spl ← splitList bodyElems.toList
  withoutCheck do
    getCode spl `term

mutual

/--
Check whether a statement list definitely returns on every path without needing any outer
continuation. This is used to decide whether nested control-flow can stay in the pure
threaded lowering, or whether we should fall back to the monadic statement path instead.
-/
partial def statementListDefinitelyReturns : List Json → Bool
| [] => false
| stmt :: rest =>
    if statementDefinitelyReturns stmt then
      true
    else
      statementListDefinitelyReturns rest

/-- Check whether one statement definitely returns on every path. -/
partial def statementDefinitelyReturns (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" => true
  | some "Raise" => true
  | some "If" =>
      match stmt.getObjValAs? (Array Json) "body", stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok orelseElems =>
          !orelseElems.isEmpty &&
            statementListDefinitelyReturns bodyElems.toList &&
            statementListDefinitelyReturns orelseElems.toList
      | _, _ => false
  | some "Try" =>
      match stmt.getObjValAs? (Array Json) "body",
          stmt.getObjValAs? (Array Json) "handlers",
          stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok handlerElems, .ok orelseElems =>
          let bodyReturns := statementListDefinitelyReturns (bodyElems.toList ++ orelseElems.toList)
          let handlersReturn :=
            handlerElems.toList.all fun handlerJson =>
              match handlerJson.getObjValAs? (Array Json) "body" with
              | .ok handlerBody => statementListDefinitelyReturns handlerBody.toList
              | .error _ => false
          bodyReturns && handlersReturn
      | _, _, _ => false
  | _ => false

end

/-- Compile a function body statement-by-statement into `doElem`s for the monadic fallback path. -/
def monadicFunctionBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  for elem in bodyElems do
    let elemStx ← withoutCheck do
      getCode elem `doElem
    bodyStxArray := bodyStxArray.push elemStx
    if statementDefinitelyReturns elem then
      break
  return bodyStxArray

/-- Build a Lean conjunction term. -/
def andTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs && $rhs)

/-- Build a Lean disjunction term. -/
def orTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs || $rhs)

/-- Read an optional JSON field and treat explicit `null` the same as an absent value. -/
def jsonFieldOption (json : Json) (field : String) : Option Json :=
  match json.getObjValAs? Json field |>.toOption with
  | some .null => none
  | other => other

/-- Recursively check whether a JSON subtree contains any node type from `targets`. -/
partial def jsonContainsNodeType (json : Json) (targets : List String) : Bool :=
  let currentMatches :=
    match json.getObjValAs? String "node_type" with
    | .ok nodeType => targets.contains nodeType
    | .error _ => false
  if currentMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonContainsNodeType elem targets)
    | .obj fields => fields.toList.any (fun (_, value) => jsonContainsNodeType value targets)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated exceptions. -/
partial def jsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesExceptionEffect value)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated `IO` effects. -/
partial def jsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesIOEffect value)
    | _ => false

/-- Detect whether a statement list uses translated exceptions and therefore should not run under `Id`. -/
def bodyNeedsExceptionMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesExceptionEffect

/-- Detect whether a statement list uses translated `IO` effects and therefore should run under `IO`. -/
def bodyNeedsIOMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesIOEffect

/-- Values using either translated exceptions or translated `IO` require monadic binding in `do`. -/
def jsonUsesMonadicEffect (json : Json) : Bool :=
  jsonUsesExceptionEffect json || jsonUsesIOEffect json

/-- Sequence a list of `doElem`s into one `doElem`, using `fallback` for the empty case. -/
def sequenceDoElems (elems : Array (TSyntax `doElem)) (fallback : TSyntax `doElem) :
    PygenM (TSyntax `doElem) := do
  if elems.isEmpty then
    return fallback
  `(doElem| do
    $[$elems:doElem]*)

/-- Emit an explicit no-op statement inside `do` notation. -/
def noopDoElemSyntax : PygenM (TSyntax `doElem) := do
  `(doElem| let _ := ())

end PyAstLean
