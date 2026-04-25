import Mathlib
import PyAstLean.Codegen
open Lean Meta Elab Term Qq Std

namespace PyAstLean

def intToStx (n : Int) : MetaM <| TSyntax `term := do
  if n < 0 then
    let nStx := Syntax.mkNumLit (toString (-n))
    `(- $nStx:term)
  else
    return Syntax.mkNumLit (toString n)

def numToStx (mantissa : Int) (exponent : Nat) : MetaM <| TSyntax `term := do
  match exponent with
    | 0 => intToStx mantissa
    | k + 1 =>
      if mantissa % 10 = 0 then
        numToStx (mantissa / 10) k
      else
        let mantissaStx ← intToStx mantissa
        let exponentStx := Syntax.mkNumLit (toString <| (10).pow exponent)
        let ratIdent := mkIdent ``Rat
        `(($mantissaStx : $ratIdent) / $exponentStx)

@[pygen "Constant"]
def constantSyntax : (kind : SyntaxNodeKinds) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok value := json.getObjValAs? Json "value" | throwError
      s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
    match value with
    | .num (JsonNumber.mk mantissa exponent) => numToStx mantissa exponent
    | .str s => return Syntax.mkStrLit s
    | .bool b => do
        let trueStx := mkIdent ``true
        let falseStx := mkIdent ``false
        if b then `($trueStx) else `($falseStx)
    | _ => throwError s!"Unsupported constant value: {value}"
  | _, _ => throwError s!"Unsupported syntax category for Constant node"

def js₀ := json% {
  "node_type": "Constant",
  "value": 1
}

#eval py_term% js₀

#eval py_term% {
  "node_type": "Constant",
  "value": "Hello, World!"
}

#eval py_term% {
  "node_type": "Constant",
  "value": -1.5
}

-- Example
def onePlusTwoNode := json% {
    "node_type": "BinOp",
    "op": "add",
    "left": {
      "node_type": "Constant",
      "value": 1
    },
    "right": {
      "node_type": "Constant",
      "value": 2.5
    }
  }


end PyAstLean
