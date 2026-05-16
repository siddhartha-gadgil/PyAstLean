import Mathlib
import PyAstLean.Codegen
open Lean Meta Elab Term Qq Std

namespace PyAstLean

#map_names [print → pyPrint]

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

@[pygen "List"]
def listSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"List node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"List node 'elts' field is not an array: {eltsJson}"
    `([$eltCodes,*])
  | _, _ => throwError s!"Unsupported syntax category for List node"

@[pygen "Tuple"]
def tupleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"Tuple node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"Tuple node 'elts' field is not an array: {eltsJson}"
    match eltCodes.size with
    | 0 => `(())
    | 1 => return eltCodes[0]!
    | 2 => `(($(eltCodes[0]!), $(eltCodes[1]!)))
    | _ => throwError "Tuple literals with more than two elements are not yet supported."
  | _, _ => throwError s!"Unsupported syntax category for Tuple node"

@[pygen "Dict"]
def dictSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok entriesJson := json.getObjValAs? Json "entries" | throwError
      s!"Dict node does not have an 'entries' field or it is not a JSON value: {json}"
    let entryCodes ← match entriesJson with
      | .arr arr => arr.mapM fun entryJson => do
          let .ok keyJson := entryJson.getObjValAs? Json "key" | throwError
            s!"Dict entry is missing a 'key' field: {entryJson}"
          let .ok valueJson := entryJson.getObjValAs? Json "value" | throwError
            s!"Dict entry is missing a 'value' field: {entryJson}"
          let keyCode ← getCode keyJson `term
          let valueCode ← getCode valueJson `term
          `(($keyCode, $valueCode))
      | _ => throwError s!"Dict node 'entries' field is not an array: {entriesJson}"
    let ofListIdent := mkIdent ``Std.HashMap.ofList
    `($ofListIdent [$entryCodes,*])
  | _, _ => throwError s!"Unsupported syntax category for Dict node"

@[pygen "FormattedValue"]
def formattedValueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    let toStringIdent := mkIdent ``toString
    `($toStringIdent $valueCode)
  | _, _ => throwError s!"Unsupported syntax category for FormattedValue node"

@[pygen "JoinedStr"]
def joinedStrSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesCodes ← match valuesJson with
      | .arr arr => arr.mapM (fun valueJson => getCode valueJson `term)
      | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
    let mut res : TSyntax `term ← `("")
    let appendIdent := mkIdent ``String.append
    for valueCode in valuesCodes do
      res ← `($appendIdent $res $valueCode)
    return res
  | _, _ => throwError s!"Unsupported syntax category for JoinedStr node"

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

@[default_instance]
instance (priority := high) : PyHAdd Rat Rat Rat where
  hAdd := fun a b => (a : Rat) + (b : Rat)

instance : PyHAdd String String String where
  hAdd := String.append

class PyHSub (α β : Type) (γ : outParam Type) where
  hSub : α → β → γ

infix:65 " -ₚ " => PyHSub.hSub

@[default_instance]
instance (priority:= low) {α β γ} [HSub α β γ] : PyHSub α β γ where
  hSub := HSub.hSub


instance (priority := high) : PyHSub Nat Nat Int where
  hSub := fun a b => (a :  Int) - (b : Int)

@[default_instance]
instance (priority := high) : PyHSub Rat Int Rat where
  hSub := fun a b => (a : Rat) - (b : Int)

#eval 3 -ₚ 5

class PyHMul (α β : Type) (γ : outParam Type) where
  hMul : α → β → γ
infix:70 " *ₚ " => PyHMul.hMul

@[default_instance]
instance {α β γ} [HMul α β γ] : PyHMul α β γ where
  hMul := HMul.hMul


instance : PyHMul String Nat String where
  hMul := fun s n => String.intercalate "" (List.replicate n s)


instance : PyHMul String Int String where
  hMul := fun s n => if n < 0 then
                        ""
                     else
                        let n := n.toNat
                        String.intercalate "" (List.replicate n s)

@[default_instance]
instance (priority := high) : PyHMul Rat Rat Rat where
  hMul := fun a b => (a : Rat) * (b : Rat)

class PyHPow (α β : Type) (γ : outParam Type) where
  hPow : α → β → γ
infix:80 " ^ₚ " => PyHPow.hPow

class PyModulo (α β : Type) (γ : outParam Type) where
  hMod : α → β → γ
infix:70 " %ₚ " => PyModulo.hMod

def pyMod (a b : Int) : Int :=
  if b == 0 then
    a
  else
    let r := a % b
    if (r < 0 && b > 0) || (r > 0 && b < 0) then
      r + b
    else
      r

@[default_instance]
instance (priority := high) : PyModulo Int Int Int where
  hMod := pyMod

instance : PyModulo Nat Nat Nat where
  hMod := fun a b => a % b

@[default_instance]
instance {α β γ} [HPow α β γ] : PyHPow α β γ where
  hPow := HPow.hPow

@[default_instance]
instance(priority := high) {α β}  [Pow α β]: PyHPow α β α where
  hPow := Pow.pow

@[default_instance]
instance(priority := high) : PyHPow Rat Int Rat where
  hPow := fun a b => (a : Rat) ^ (b : Int)

@[default_instance]
instance(priority := high) : Neg Rat where
  neg := fun a => - (a : Rat)

class PyHDiv (α β : Type) (γ : outParam Type) where
  hDiv : α → β → γ

infix:70 " /ₚ " => PyHDiv.hDiv

@[default_instance]
instance {α β γ} [HDiv α β γ] : PyHDiv α β γ where
  hDiv := HDiv.hDiv


instance (priority := high) : PyHDiv Int Int Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)


instance (priority := high) : PyHDiv Nat Nat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

@[default_instance]
instance (priority := high) : PyHDiv Rat Rat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

def pyRange (stop : Int) (start : Int := 0) (step : Int := 1) : List Int := do
  if step > 0 then
    List.map (fun i => start + i) (List.range' 0 ((stop-start)/step + (stop-start)%step).toNat step.toNat)
  else if step < 0 then
    List.map (fun i => start - i) (List.range' 0 ((start-stop)/(-step) + (start-stop)%(-step)).toNat (-step).toNat)
  else
    []

-- #eval pyRange 10 (17:Int) (-2)
@[pygen "BinOp"]
def binOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    Term.synthesizeSyntheticMVarsNoPostponing
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
    | "div" => `($leftCode /ₚ $rightCode)
    | "pow" => `($leftCode ^ₚ $rightCode)
    | "mod" => `($leftCode %ₚ $rightCode)
    | _ => throwError s!"Unsupported binary operator: {op}"
  | _, _ => throwError s!"Unsupported syntax category for BinOp node"

@[pygen "UnaryOp"]
def unaryOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"UnaryOp node does not have an 'op' field or it is not a string: {json}"
    let .ok operandJson := json.getObjValAs? Json "operand" | throwError
      s!"UnaryOp node does not have an 'operand' field or it is not a JSON value: {json}"
    let operandCode ← getCode operandJson `term
    match op with
    | "not" => `(! $operandCode)
    | "neg" => `(- $operandCode)
    | "pos" => `($operandCode)
    | _ => throwError s!"Unsupported unary operator: {op}"
  | _, _ => throwError s!"Unsupported syntax category for UnaryOp node"

@[pygen "BoolOp"]
def boolOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"BoolOp node does not have an 'op' field or it is not a string: {json}"
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"BoolOp node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesCodes ← match valuesJson with
      | .arr arr => arr.mapM (fun valueJson => getCode valueJson `term)
      | _ => throwError s!"BoolOp node 'values' field is not an array: {valuesJson}"
    -- let valuesCodes := valuesCodes.toList
    let l := valuesCodes.toList.length
    if l = 0 then throwError s!"BoolOp node 'values' array is empty: {valuesJson}"
    match op with
    | "and" => return ← valuesCodes.foldlM (fun a b => `($a && $b)) (valuesCodes[0]!) (start := 1)
    | "or" => return ← valuesCodes.foldlM (fun a b => `($a || $b)) (valuesCodes[0]!) (start := 1)
    | _ => throwError s!"Unsupported boolean operator: {op}"
  | _, _ => throwError s!"Unsupported syntax category for BoolOp node"

#eval (-3)^2
@[pygen "Compare"]
def compareSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"Compare node does not have an 'op' field or it is not a string: {json}"
    let .ok leftJson := json.getObjValAs? Json "left" | throwError
      s!"Compare node does not have a 'left' field or it is not a JSON value: {json}"
    let .ok rightJson := json.getObjValAs? Json "right" | throwError
      s!"Compare node does not have a 'right' field or it is not a JSON value: {json}"
    let leftCode ← getCode leftJson `term
    let rightCode ← getCode rightJson `term
    match op with
    | "eq" => `($leftCode == $rightCode)
    | "ne" => `($leftCode != $rightCode)
    | "lt" => `($leftCode < $rightCode)
    | "le" => `($leftCode <= $rightCode)
    | "gt" => `($leftCode > $rightCode)
    | "ge" => `($leftCode >= $rightCode)
    | _ => throwError s!"Unsupported comparison operator: {op}"
  | _, _ => throwError s!"Unsupported syntax category for Compare node"

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
    let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          let mappedName ← leanName funcName.toName
          pure <| (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode funcJson `term
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
  | `doElem, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          let mappedName ← leanName funcName.toName
          pure <| (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode funcJson `term
    let mut t ← `($funcCode)
    let argsCodes ← match argsJson with
      | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    for argCode in argsCodes do
      t ← `($t $argCode)
    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
    for (kwName, kwValueJson) in keyWordsMap.toList do
      let kwValueCode ← getCode kwValueJson `term
      let kwId := mkIdent kwName.toName
      t ← `($t ($kwId:ident := $kwValueCode))
    let callCode := t
    `(doElem| let _ := $callCode)
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
      -- IO.eprintln s!"Successfully elaborated term: {codeStx}"  -- Debugging output
      return codeStx
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString} for {← PrettyPrinter.ppTerm codeStx}"

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
      if cmd.raw.isOfKind nullKind then
        return cmd
      else
        liftCommandElabM <| Command.elabCommand cmd
      -- IO.eprintln s!"Successfully elaborated command: {← PrettyPrinter.ppCommand cmd}"  -- Debugging output
      return cmd
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString} for {← PrettyPrinter.ppCommand cmd}"

#eval pygen

end PyAstLean
