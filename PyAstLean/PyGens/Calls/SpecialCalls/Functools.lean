import Libraries.functools.FunctoolsDef
import PyAstLean.PyGens.Calls.CallEffects
import PyAstLean.PyGens.Calls.CallShared

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Internal alias for keyword argument objects in Python call JSON. -/
abbrev PyKeywordArgs := Std.TreeMap.Raw String Json compare

/-- Recognize both `functools.reduce(...)` and imported `reduce(...)` from `functools`. -/
def isFunctoolsReduceTarget (json : Json) : Bool :=
  match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
  | .ok "functools", .ok "reduce" => true
  | _, _ =>
      json.getObjValAs? String "node_type" == .ok "Attribute" &&
      json.getObjValAs? String "attr" == .ok "reduce" &&
      (json.getObjValAs? Json "value").toOption.any (fun valueJson =>
        valueJson.getObjValAs? String "node_type" == .ok "Name" &&
        valueJson.getObjValAs? String "id" == .ok "functools")

/-- Build the translated Lean term for a `functools.reduce` call. -/
def lowerFunctoolsReduceAppliedTerm (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (TSyntax `term) := do
  unless keyWordsMap.isEmpty do
    throwError "functools.reduce() keyword arguments are not supported yet."
  match argsArray.size with
  | 2 =>
      let pyReduceIdent := mkIdent ``Libraries.functools.pyReduce
      let elemTy? ← inferIterableElemTypeSyntax? argsArray[1]!
      let funcCode ← typedBinaryLambdaCode argsArray[0]! argsCodes[0]! elemTy?
      let adjustedCodes := #[funcCode, argsCodes[1]!]
      buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
        let f := resolvedArgs[0]!
        let xs := resolvedArgs[1]!
        `($pyReduceIdent $xs $f)
  | 3 =>
      let pyReduceIdent := mkIdent ``Libraries.functools.pyReduce
      let initTy? ← inferSimpleValueTypeSyntax? argsArray[2]!
      let funcCode ← typedBinaryLambdaCode argsArray[0]! argsCodes[0]! initTy?
      let adjustedCodes := #[funcCode, argsCodes[1]!, argsCodes[2]!]
      buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
        let f := resolvedArgs[0]!
        let xs := resolvedArgs[1]!
        let init := resolvedArgs[2]!
        `($pyReduceIdent $xs $f (some $init))
  | _ =>
      throwError "functools.reduce() expects two or three positional arguments."

/-- Term-level lowering hook for `functools` calls that need custom translation. -/
def lowerFunctoolsCallTerm? (funcJson : Json) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (Option (TSyntax `term)) := do
  if isFunctoolsReduceTarget funcJson then
    return some (← lowerFunctoolsReduceAppliedTerm argsArray argsCodes keyWordsMap)
  return none

/-- `doElem` lowering hook for `functools` calls that need custom translation. -/
def lowerFunctoolsCallDoElem? (funcJson : Json) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (Option (TSyntax `doElem)) := do
  if isFunctoolsReduceTarget funcJson then
    let t ← lowerFunctoolsReduceAppliedTerm argsArray argsCodes keyWordsMap
    if argsArray.toList.any basicJsonUsesMonadicEffect then
      return some (← `(doElem| let _ ← $t:term))
    else
      return some (← `(doElem| let _ := $t))
  return none

end PyAstLean
