import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Infer a simple runtime type from a value expression when the shape is obvious. -/
def inferSimpleValueTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match json.getObjValAs? String "node_type" with
  | .ok "Constant" =>
      let .ok value := json.getObjValAs? Json "value" | throwError
        s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
      match value with
      | .num (JsonNumber.mk _ exponent) =>
          if json.getObjValAs? String "python_literal_kind" == .ok "float" then
            return some (mkIdent ``Float)
          else if exponent == 0 then
            return some (mkIdent ``Int)
          else
            return some (mkIdent ``Rat)
      | .str _ => return some (mkIdent ``String)
      | .bool _ => return some (mkIdent ``Bool)
      | _ => return none
  | _ => return none

/-- Infer a simple iterable element type from obvious literal iterables. -/
def inferIterableElemTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match json.getObjValAs? String "node_type" with
  | .ok "List" => do
      let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
        s!"List node does not have an 'elts' field or it is not a JSON value: {json}"
      match eltsJson with
      | .arr arr =>
          match arr[0]? with
          | some first => inferSimpleValueTypeSyntax? first
          | none => return none
      | _ => return none
  | .ok "Tuple" => do
      let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
        s!"Tuple node does not have an 'elts' field or it is not a JSON value: {json}"
      match eltsJson with
      | .arr arr =>
          match arr[0]? with
          | some first => inferSimpleValueTypeSyntax? first
          | none => return none
      | _ => return none
  | .ok "Constant" => do
      let .ok value := json.getObjValAs? Json "value" | throwError
        s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
      match value with
      | .str _ => return some (mkIdent ``Char)
      | _ => return none
  | _ => return none

/-- Read the positional parameter names from a lambda node without depending on `FuncDef.lean`. -/
def lambdaArgIdents (json : Json) : PygenM (Array (TSyntax `ident)) := do
  let .ok argsJson := json.getObjValAs? Json "args" | throwError
    s!"Lambda node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := argsJson.getObjValAs? (Array Json) "args" | throwError
    s!"Lambda args does not have an 'args' field or it is not a JSON array: {argsJson}"
  argsArray.mapM fun argJson => do
    let .ok argName := argJson.getObjValAs? String "arg" | throwError
      s!"Lambda argument does not have an 'arg' field or it is not a string: {argJson}"
    pure (mkIdent argName.toName)

/--
Stamp a binary lambda with either concrete runtime types or `_` placeholders so overloaded
operators inside higher-order calls elaborate more predictably.
-/
def typedBinaryLambdaCode (funcJson : Json) (fallback : TSyntax `term)
    (paramTy? : Option (TSyntax `term)) : PygenM (TSyntax `term) := do
  unless funcJson.getObjValAs? String "node_type" == .ok "Lambda" do
    return fallback
  let argIdents ← lambdaArgIdents funcJson
  unless argIdents.size == 2 do
    return fallback
  let .ok bodyJson := funcJson.getObjValAs? Json "body" | throwError
    s!"Lambda node does not have a 'body' field or it is not a JSON value: {funcJson}"
  let bodyStx ← getCode bodyJson `term
  let arg0 := argIdents[0]!
  let arg1 := argIdents[1]!
  let paramTy ← match paramTy? with
    | some stx => pure stx
    | none => `(_)
  `(fun ($arg0 : $paramTy) ↦ fun ($arg1 : $paramTy) ↦ $bodyStx)

end PyAstLean
