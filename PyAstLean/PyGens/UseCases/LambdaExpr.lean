import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.UseCases.FuncDef

open Lean Meta Elab Term

namespace PyAstLean

/-- Detect lambdas that use their single argument like a pair via `[0]`/`[1]` subscripts. -/
partial def lambdaUsesPairSubscript (json : Json) (argName : String) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "node_type", json.getObjValAs? Json "value", json.getObjValAs? Json "slice" with
    | .ok "Subscript", .ok valueJson, .ok sliceJson =>
        match valueJson.getObjValAs? String "node_type", valueJson.getObjValAs? String "id",
            sliceJson.getObjValAs? String "node_type", sliceJson.getObjValAs? Json "value" with
        | .ok "Name", .ok id, .ok "Constant", .ok (.num (JsonNumber.mk mantissa exponent)) =>
            id == argName && exponent == 0 && (mantissa == 0 || mantissa == 1)
        | _, _, _, _ => false
    | _, _, _ => false
  if directMatch then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => lambdaUsesPairSubscript elem argName)
    | .obj fields => fields.toList.any (fun (_, value) => lambdaUsesPairSubscript value argName)
    | _ => false

@[pygen "Lambda"]
def lambdaStx : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok _ := json.getObjValAs? Json "args" | throwError
          s!"Lambda node does not have an 'args' field or it is not a JSON value: {json}"
        let .ok body := json.getObjValAs? Json "body" | throwError
          s!"Lambda node does not have a 'body' field or it is not a JSON value: {json}"
        let argInfos ← functionArgInfos json
        let bodyStx ← getCode body `term
        if argInfos.isEmpty then
          `(fun () ↦ $bodyStx)
        else if argInfos.size == 1 then
          let (argIdent, ty?) := argInfos[0]!
          match ty? with
          | some ty =>
              `(fun ($argIdent : $ty) ↦ $bodyStx)
          | none =>
              let argName := argIdent.getId.toString
              if lambdaUsesPairSubscript body argName then
                let alphaIdent := mkIdent `α
                let betaIdent := mkIdent `β
                let toStringIdent := mkIdent ``ToString
                let pairTy ← `($alphaIdent × $betaIdent)
                `(fun {α β} [$toStringIdent $alphaIdent] [$toStringIdent $betaIdent] ($argIdent : $pairTy) ↦
                    $bodyStx)
              else if !jsonReferencesName body argName then
                let unitIdent := mkIdent ``Unit
                `(fun ($argIdent : $unitIdent) ↦ $bodyStx)
              else
                `(fun $argIdent ↦ $bodyStx)
        else
          let mut result := bodyStx
          for (argIdent, ty?) in argInfos.toList.reverse do
            result ← match ty? with
              | some ty => `(fun ($argIdent : $ty) ↦ $result)
              | none => `(fun $argIdent ↦ $result)
          pure result
    | _, _ => throwError s!"Unsupported syntax category for Lambda node"

end PyAstLean
