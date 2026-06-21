import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.UseCases.FuncDef

open Lean Meta Elab Term

namespace PastaLean

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

/-- Mark every `pair[0]`/`pair[1]` subscript on `argName` in the body so the Subscript codegen
lowers it to `Prod.fst`/`Prod.snd` (the param is typed as a product `α × β`, which has no generic
`PyGetItem` instance). We stamp the *value* `Name` node with `_PastaLean_pair: true`. -/
partial def markPairSubscripts (json : Json) (argName : String) : Json :=
  let stamped : Json :=
    match json.getObjValAs? String "node_type", json.getObjValAs? Json "value", json.getObjValAs? Json "slice" with
    | .ok "Subscript", .ok valueJson, .ok sliceJson =>
        match valueJson.getObjValAs? String "node_type", valueJson.getObjValAs? String "id",
            sliceJson.getObjValAs? String "node_type", sliceJson.getObjValAs? Json "value" with
        | .ok "Name", .ok id, .ok "Constant", .ok (.num (JsonNumber.mk mantissa exponent)) =>
            if id == argName && exponent == 0 && (mantissa == 0 || mantissa == 1) then
              json.setObjVal! "value" (valueJson.setObjVal! "_PastaLean_pair" (Json.bool true))
            else json
        | _, _, _, _ => json
    | _, _, _ => json
  match stamped with
  | .arr elems => Json.arr (elems.map (fun elem => markPairSubscripts elem argName))
  | .obj fields => Json.obj (fields.map (fun _ value => markPairSubscripts value argName))
  | _ => stamped

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
                -- Re-lower the body with `pair[0]`/`pair[1]` marked so they emit `Prod.fst`/`Prod.snd`.
                let pairBodyStx ← getCode (markPairSubscripts body argName) `term
                let alphaIdent := mkIdent `α
                let betaIdent := mkIdent `β
                let toStringIdent := mkIdent ``ToString
                let pairTy ← `($alphaIdent × $betaIdent)
                `(fun {α β} [$toStringIdent $alphaIdent] [$toStringIdent $betaIdent] ($argIdent : $pairTy) ↦
                    $pairBodyStx)
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

end PastaLean
