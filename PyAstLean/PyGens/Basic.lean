import Mathlib
import Libraries.Registry
import PyAstLean.Codegen
import PyAstLean.PyAPI
import PyAstLean.PyGens.Attributes
import PyAstLean.PyAPI.BuiltinRegistry
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

/-- Preserve Python float literals as Lean `Float`s, even when the decimal part is `.0`. -/
def floatNumToStx (mantissa : Int) (exponent : Nat) : MetaM <| TSyntax `term := do
  let floatScientificIdent := mkIdent ``Float.ofScientific
  let magnitude := Int.natAbs mantissa
  let magnitudeStx := Syntax.mkNumLit (toString magnitude)
  let exponentStx := Syntax.mkNumLit (toString exponent)
  let base ← `($floatScientificIdent $magnitudeStx true $exponentStx)
  if mantissa < 0 then
    `(- $base:term)
  else
    pure base

@[pygen "Constant"]
def constantSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok value := json.getObjValAs? Json "value" | throwError
      s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
    let isPythonFloat :=
      json.getObjValAs? String "python_literal_kind" == .ok "float"
    match value with
    | .num (JsonNumber.mk mantissa exponent) =>
        if isPythonFloat then
          floatNumToStx mantissa exponent
        else
          numToStx mantissa exponent
    | .str s => return Syntax.mkStrLit s
    | .bool b => do
        let trueStx := mkIdent ``true
        let falseStx := mkIdent ``false
        if b then `($trueStx) else `($falseStx)
    | .null =>
        let noneIdent := mkIdent ``none
        `($noneIdent)
    | _ => throwError s!"Unsupported constant value: {value}"
  | _, _ => throwError s!"Unsupported syntax category for Constant node"

def jsonLibraryMappedName? (json : Json) : PygenM (Option Lean.Name) := do
  match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
  | .ok moduleName, .ok memberName =>
      match Libraries.pythonLibraryMap? moduleName memberName with
      | some leanName => pure (some leanName)
      | none => throwError s!"Unsupported imported library member '{moduleName}.{memberName}'."
  | _, _ => pure none

@[pygen "Name"]
def nameSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
        let .ok id := json.getObjValAs? String "id" | throwError
          s!"Name node does not have an 'id' field or it is not a string: {json}"
        return mkIdent id.toName
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
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

/-- `{a, b, c}` set literals lower to a deduplicated list via `pySetFromList`; sets are
modeled as lists so list-backed protocols (`in`, `len`, iteration) apply. -/
@[pygen "Set"]
def setSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"Set node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"Set node 'elts' field is not an array: {eltsJson}"
    let fromListIdent := mkIdent ``PyAstLean.pySetFromList
    `($fromListIdent [$eltCodes,*])
  | _, _ => throwError s!"Unsupported syntax category for Set node"

@[pygen "Tuple"]
def tupleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"Tuple node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"Tuple node 'elts' field is not an array: {eltsJson}"
    let rec buildTuple (elts : List (TSyntax `term)) : PygenM (TSyntax `term) := do
      match elts with
      | [] => `(())
      | [single] => pure single
      | first :: rest => do
          let restTuple ← buildTuple rest
          `(($first, $restTuple))
    buildTuple eltCodes.toList
  | _, _ => throwError s!"Unsupported syntax category for Tuple node"

/-- `Starred` (`*iterable`) in a call lowers, in term position, to the iterable itself.
The only place that interprets the spread is the `print(...)` lowering, which detects a
`Starred` argument by node type and maps over this value. -/
@[pygen "Starred"]
def starredSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Starred node does not have a 'value' field or it is not a JSON value: {json}"
    getCode valueJson `term
  | _, _ => throwError s!"Unsupported syntax category for Starred node"

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


def js₀ := json% {
  "node_type": "Constant",
  "value": 1
}

/- map to noop-/
@[pygen "Delete"]
def deleteSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let _ ← match targetsJson with
      | .arr arr => arr.mapM (fun targetJson => getCode targetJson `term)
      | _ => throwError s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- We currently do not support deletion semantics, so we simply return `()`.
    `(())
  | `doElem, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let _ ← match targetsJson with
      | .arr arr => arr.mapM (fun targetJson => getCode targetJson `term)
      | _ => throwError s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- We currently do not support deletion semantics, so we simply return `()`.
    `(doElem| let _ := ())
  | `command, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let _ ← match targetsJson with
      | .arr arr => arr.mapM (fun targetJson => getCode targetJson `term)
      | _ => throwError s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- We currently do not support deletion semantics, so we simply return `()`.
    `(command| def del := ())
  | _, _ => throwError s!"Unsupported syntax category for Delete node"
/-- Detect the JSON encoding of Python's `None`. -/
def isNoneConstantJson (json : Json) : Bool :=
  match json.getObjValAs? String "node_type", json.getObjValAs? Json "value" with
  | .ok "Constant", .ok .null => true
  | _, _ => false

/-- Apply a Python binary operator to already-lowered operand terms. Shared by `binOpSyntax`
and `inlineIOTerm` so IO-bearing operands can be hoisted without duplicating the op table. -/
def binOpApplyTerm (op : String) (leftCode rightCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match op with
  | "add" => `($leftCode +ₚ $rightCode)
  | "sub" => `($leftCode -ₚ $rightCode)
  | "mul" => `($leftCode *ₚ $rightCode)
  | "div" => `($leftCode /ₚ $rightCode)
  | "floordiv" =>
      let floorDivIdent := mkIdent ``PyAstLean.pyFloorDiv
      `($floorDivIdent $leftCode $rightCode)
  | "pow" => `($leftCode ^ₚ $rightCode)
  | "mod" => `($leftCode %ₚ $rightCode)
  | "bitand" => `($(mkIdent ``PyAstLean.pyBitAnd) $leftCode $rightCode)
  | "bitor" => `($(mkIdent ``PyAstLean.pyBitOr) $leftCode $rightCode)
  | "bitxor" => `($(mkIdent ``PyAstLean.pyBitXor) $leftCode $rightCode)
  | "lshift" => `($(mkIdent ``PyAstLean.pyShiftLeft) $leftCode $rightCode)
  | "rshift" => `($(mkIdent ``PyAstLean.pyShiftRight) $leftCode $rightCode)
  | _ => throwError s!"Unsupported binary operator: {op}"

/-- Apply a Python unary operator to an already-lowered operand term. -/
def unaryOpApplyTerm (op : String) (operandCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match op with
  | "not" => `(! $operandCode)
  | "neg" => `(- $operandCode)
  | "pos" => `($operandCode)
  | _ => throwError s!"Unsupported unary operator: {op}"

/-- Whether a condition's IR already lowers to a `Bool` (a comparison, boolean operator,
`not`, or a boolean literal). Such tests need no truthiness conversion; everything else (a
bare `int`/`list`/`str`/`Option` used as `if x:` / `while x:`) is wrapped in `pyTruthy`. -/
def conditionIsBoolean (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Compare" => true
  | .ok "BoolOp" => true
  | .ok "UnaryOp" => json.getObjValAs? String "op" == .ok "not"
  | .ok "Constant" =>
      match json.getObjValAs? Json "value" with
      | .ok (.bool _) => true
      | _ => false
  | _ => false

/-- Lower a condition expression, applying Python truthiness (`pyTruthy`) unless it already
produces a `Bool`. Used by `if`/`while`/`if`-expression lowering. -/
def truthyConditionTerm (json : Json) (code : TSyntax `term) : PygenM (TSyntax `term) := do
  if conditionIsBoolean json then pure code
  else `($(mkIdent ``PyAstLean.pyTruthy) $code)

/-- A JSON node that lowers to a Lean `String` value: a string literal or an f-string. Used to
route `x in s` to substring containment when the left operand is statically a string. -/
def isStringyJson (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "JoinedStr" => true
  | .ok "Constant" =>
      match json.getObjValAs? Json "value" with
      | .ok (.str _) => true
      | _ => false
  | _ => false

/-- Apply a Python comparison operator to already-lowered operand terms. `leftJson` is the
left operand's IR, used only to decide membership lowering: a string literal on the left of
`in`/`not in` means *substring* containment (`pyStrContainsSubstr`); otherwise membership
dispatches through `pyContains`, whose `outParam` element type pins the element from the
container. -/
def compareApplyTerm (op : String) (leftJson : Json) (leftCode rightCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match op with
  | "eq" => `($leftCode == $rightCode)
  | "ne" => `($leftCode != $rightCode)
  | "is" => `($leftCode == $rightCode)
  | "isnot" => `($leftCode != $rightCode)
  | "lt" => `($leftCode < $rightCode)
  | "le" => `($leftCode <= $rightCode)
  | "gt" => `($leftCode > $rightCode)
  | "ge" => `($leftCode >= $rightCode)
  | "in" =>
      if isStringyJson leftJson then
        `($(mkIdent ``PyAstLean.pyStrContainsSubstr) $rightCode $leftCode)
      else
        `($(mkIdent ``pyContains) $rightCode $leftCode)
  | "notin" =>
      if isStringyJson leftJson then
        `(! ($(mkIdent ``PyAstLean.pyStrContainsSubstr) $rightCode $leftCode))
      else
        `(! ($(mkIdent ``pyContains) $rightCode $leftCode))
  | _ => throwError s!"Unsupported comparison operator: {op}"

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
    binOpApplyTerm op leftCode rightCode
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
    unaryOpApplyTerm op operandCode
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
    compareApplyTerm op leftJson leftCode rightCode
  | _, _ => throwError s!"Unsupported syntax category for Compare node"

@[pygen "IfExp"]
def ifExpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok testJson := json.getObjValAs? Json "test" | throwError
      s!"IfExp node does not have a 'test' field or it is not a JSON value: {json}"
    let .ok bodyJson := json.getObjValAs? Json "body" | throwError
      s!"IfExp node does not have a 'body' field or it is not a JSON value: {json}"
    let .ok orelseJson := json.getObjValAs? Json "orelse" | throwError
      s!"IfExp node does not have an 'orelse' field or it is not a JSON value: {json}"
    let testCode ← truthyConditionTerm testJson (← getCode testJson `term)
    let bodyIsNone := isNoneConstantJson bodyJson
    let orelseIsNone := isNoneConstantJson orelseJson
    if bodyIsNone && orelseIsNone then
      `(none)
    else if bodyIsNone then
      let orelseCode ← getCode orelseJson `term
      `(if $testCode then none else some $orelseCode)
    else if orelseIsNone then
      let bodyCode ← getCode bodyJson `term
      `(if $testCode then some $bodyCode else none)
    else
      let bodyCode ← getCode bodyJson `term
      let orelseCode ← getCode orelseJson `term
      `(if $testCode then $bodyCode else $orelseCode)
  | _, _ => throwError s!"Unsupported syntax category for IfExp node"

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

-- @[pygen "Call"]
-- def callSyntax : (kind : SyntaxNodeKind) → Json →
--     PygenM (TSyntax kind)
--   | `term, json => do
--     let .ok funcJson := json.getObjValAs? Json "func" | throwError
--       s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
--     let .ok argsJson := json.getObjValAs? Json "args" | throwError
--       s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
--     let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
--       | .ok "Name", .ok funcName =>
--           let mappedName ← leanName funcName.toName
--           pure <| (mkIdent mappedName : TSyntax `term)
--       | _, _ =>
--           getCode funcJson `term
--     let mut t ← `($funcCode)
--     let argsCodes ← match argsJson with
--       | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
--       | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
--     for argCode in argsCodes do
--       t ←  `($t $argCode)
--     let .ok keyWordsJson := json.getObjVal?  "keywords" | throwError
--       s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
--     let .ok keyWordsMap := keyWordsJson.getObj? | throwError
--       s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
--     for (kwName, kwValueJson) in keyWordsMap.toList do
--       let kwValueCode ← getCode kwValueJson `term
--       let kwId := mkIdent kwName.toName
--       t ← `($t ($kwId:ident := $kwValueCode))
--     return t
--   | `doElem, json => do
--     let .ok funcJson := json.getObjValAs? Json "func" | throwError
--       s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
--     let .ok argsJson := json.getObjValAs? Json "args" | throwError
--       s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
--     let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
--       | .ok "Name", .ok funcName =>
--           let mappedName ← leanName funcName.toName
--           pure <| (mkIdent mappedName : TSyntax `term)
--       | _, _ =>
--           getCode funcJson `term
--     let mut t ← `($funcCode)
--     let argsCodes ← match argsJson with
--       | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
--       | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
--     for argCode in argsCodes do
--       t ← `($t $argCode)
--     let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
--       s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
--     let .ok keyWordsMap := keyWordsJson.getObj? | throwError
--       s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
--     for (kwName, kwValueJson) in keyWordsMap.toList do
--       let kwValueCode ← getCode kwValueJson `term
--       let kwId := mkIdent kwName.toName
--       t ← `($t ($kwId:ident := $kwValueCode))
--     let callCode := t
--     `(doElem| let _ := $callCode)
--   | _, _ => throwError s!"Unsupported syntax category for Call node"

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

-- #eval pygen

end PyAstLean
