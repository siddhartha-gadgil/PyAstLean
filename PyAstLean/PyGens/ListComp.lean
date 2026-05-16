import Mathlib
import PyAstLean.Codegen
open Lean Meta Elab Term Qq Std

namespace PyAstLean


@[pygen "ListComp"]
def listComp : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltjson := json.getObjValAs? Json "elt" | throwError
      s!"ListComp node missing 'elt' field or it is not a Json object : {json}"
    let .ok gensjson := json.getObjValAs? Json "generators" | throwError
      "ListComp node missing 'generators' field or it is not a Json array"
    let eltCode ← getCode eltjson `term
    let gensCodes ← match gensjson with
    | .arr arr => arr.mapM (fun json => getCode json `term)
    | _ => throwError "ListComp node 'generators' field is not a Json array"
    -- let gensCode := gensCodes[0]!
    -- IO.println s!"gensCodes: {gensCodes}"
    `(List.map (fun x => $eltCode) $(gensCodes[0]!))
  | _, _ => throwError "Expected ListComp node"

@[pygen "comprehension"]
def comprehension : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok targetjson := json.getObjValAs? Json "target" | throwError
    "comprehension node missing 'target' field or it is not a Json object"
    let .ok iterjson := json.getObjValAs? Json "iter" | throwError
    "comprehension node missing 'iter' field or it is not a Json object"
    let .ok ifsjson := json.getObjValAs? Json "ifs" | throwError
    "comprehension node missing 'ifs' field or it is not a Json array"
    let targetCode ← getCode targetjson `term
    let iterCode ← getCode iterjson `term
    let ifsCodes ← match ifsjson with
      | .arr arr => arr.mapM (fun json => getCode json `term)
      | _ => throwError "comprehension node 'ifs' field is not a Json array"
    let decidedIfs ←  ifsCodes.mapM (fun ifCode => `(decide $ifCode))
    `(List.filter (fun $targetCode => List.all [$decidedIfs,*] (fun ifCond => ifCond)) $iterCode)
  | _, _ => throwError "Expected comprehension node"

@[pygen "Range"]
def range : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok argsjson := json.getObjValAs? Json "args" | throwError
      "Range node missing 'args' field or it is not a Json array"
    let argsCodes ← match argsjson with
      | .arr arr => arr.mapM (fun json => getCode json `term)
      | _ => throwError "Range node 'args' field is not a Json array"
    match argsCodes.size with
    | 1 => `(pyRange $(argsCodes[0]!))
    | 2 => `(pyRange $(argsCodes[1]!) $(argsCodes[0]!))
    | 3 => `(pyRange $(argsCodes[1]!) $(argsCodes[0]!) $(argsCodes[1]!))
    | _ => throwError "Range node 'args' field must have 1, 2, or 3 elements"
  | _, _ => throwError "Expected Range node"

end PyAstLean
#print List.all
