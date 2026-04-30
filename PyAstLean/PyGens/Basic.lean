import Mathlib
import PyAstLean.Codegen
open Lean Meta Elab Term Qq Std

namespace PyAstLean

def intToStx (n : Int) : MetaM <| TSyntax `term := do
  if n < 0 then
    let nStx := Syntax.mkNumLit (toString (-n))
    `(- $nStx:term)
  else
    let nStx := Syntax.mkNumLit (toString (n))
    let intIdent := mkIdent ``Int
    `(($nStx : $intIdent))

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
def constantSyntax : (kind : SyntaxNodeKind) → Json →
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

@[pygen "Name"]
def nameSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok id := json.getObjValAs? String "id" | throwError
      s!"Name node does not have an 'id' field or it is not a string: {json}"
    return mkIdent id.toName
  | `ident, json => do
    let .ok id := json.getObjValAs? String "id" | throwError
      s!"Name node does not have an 'id' field or it is not a string: {json}"
    return mkIdent id.toName
  | _, _ => throwError s!"Unsupported syntax category for Name node"

def js₀ := json% {
  "node_type": "Constant",
  "value": 1
}


class PyHAdd (α β : Type) (γ : outParam Type) where
  hAdd : α → β → γ

infix:65 " +ₚ " => PyHAdd.hAdd

@[default_instance]
instance {α β γ} [HAdd α β γ] : PyHAdd α β γ where
  hAdd := HAdd.hAdd

instance : PyHAdd String String String where
  hAdd := String.append

class PyHSub (α β : Type) (γ : outParam Type) where
  hSub : α → β → γ

infix:65 " -ₚ " => PyHSub.hSub

@[default_instance]
instance (priority:= low) {α β γ} [HSub α β γ] : PyHSub α β γ where
  hSub := HSub.hSub

@[default_instance]
instance (priority := high) : PyHSub Nat Nat Int where
  hSub := fun a b => (a :  Int) - (b : Int)

#eval 3 -ₚ 5

class PyHMul (α β : Type) (γ : outParam Type) where
  hMul : α → β → γ
infix:70 " *ₚ " => PyHMul.hMul

@[default_instance]
instance {α β γ} [HMul α β γ] : PyHMul α β γ where
  hMul := HMul.hMul

@[pygen "BinOp"]
def binOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"BinOp node does not have an 'op' field or it is not a string: {json}"
    let .ok leftJson := json.getObjValAs? Json "left" | throwError
      s!"BinOp node does not have a 'left' field or it is not a JSON value: {json}"
    let .ok rightJson := json.getObjValAs? Json "right" | throwError
      s!"BinOp node does not have a 'right' field or it is not a JSON value: {json}"
    let leftCode ←  getCode leftJson `term
    let rightCode ← getCode rightJson `term
    match op with
    | "add" => `($leftCode +ₚ $rightCode)
    | "sub" => `($leftCode -ₚ $rightCode)
    | "mul" => `($leftCode *ₚ $rightCode)
    | _ => throwError s!"Unsupported binary operator: {op}"
  | _, _ => throwError s!"Unsupported syntax category for BinOp node"

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
      "value": 2
    }
  }

@[pygen "Call"]
def callSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let funcCode ← getCode funcJson `term
    let mut t ← `($funcCode)
    let argsCodes ← match argsJson with
      | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    for argCode in argsCodes do
      t ←  `($t $argCode)
    let .ok keyWordsJson := json.getObjVal?  "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
    for (kwName, kwValueJson) in keyWordsMap.toList do
      let kwValueCode ← getCode kwValueJson `term
      let kwId := mkIdent kwName.toName
      t ← `($t ($kwId:ident := $kwValueCode))
    return t
  | _, _ => throwError s!"Unsupported syntax category for Call node"



@[pygen "Attribute"]
def attributeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    -- IO.eprintln s!"Generating code for Attribute node with JSON: {json}" -- Debugging output
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok attr := json.getObjValAs? String "attr" | throwError
      s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
    try
      let id ← getCode valueJson `ident
      return mkIdent <| id.getId ++ attr.toName
    catch _ => do
      -- IO.eprintln s!"Generating code for Attribute value: {valueJson} as value not a name" -- Debugging output
      let valueCode ←
          getCode valueJson `term
      -- IO.eprintln s!"Generated code for Attribute value: {valueCode} : {← `($valueCode)}" -- Debugging output
      let attrId := mkIdent attr.toName
      `($valueCode.$attrId)
  | `ident, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok attr := json.getObjValAs? String "attr" | throwError
      s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
    let id ← getCode valueJson `ident
    return mkIdent <| id.getId ++ attr.toName
  | _, _ => throwError s!"Unsupported syntax category for Attribute node"


def fn := fun n => show IO _ from  do
  let m := n + 1
  return m

def fnId := Id.run do
  let n := 3
  let m := n + 1
  return m

def n₀ : Id Nat := 3

@[pygen_transform term]
def elabCheckTerm : (stx : TSyntax `term) → PygenM (TSyntax `term)
  | codeStx => do
    unless ← isCheckEnabled do
      return codeStx
    try
      let cmd ← `(command| example := $codeStx)
      liftCommandElabM <| Command.elabCommand cmd
      IO.eprintln s!"Successfully elaborated term: {codeStx}"  -- Debugging output
      return codeStx
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString}"

@[pygen_transform term]
def addArrow : (stx : TSyntax `term) → PygenM (TSyntax `term)
  | codeStx => do
    unless ← isUseArrowEnabled do
      return codeStx
    try
      let e ← elabTerm codeStx none
      let eType ← inferType e
      if eType.isAppOf ``Id then
        `(← $codeStx)
      else
        return codeStx
    catch e =>
      trace[pyastlean.pygen.info] m!"addArrow transform failed for {codeStx} with error: {← e.toMessageData.toString}"
      return codeStx

@[pygen_transform command]
def elabCheckCmd : (stx : TSyntax `command) → PygenM (TSyntax `command)
  | cmd => do
    unless ← isCheckEnabled do
      return cmd
    try
      liftCommandElabM <| Command.elabCommand cmd
      IO.eprintln s!"Successfully elaborated command: {← PrettyPrinter.ppCommand cmd}"  -- Debugging output
      return cmd
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString}"

end PyAstLean
