import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyAPI
import PyAstLean.PyGens.Attributes
open Lean Meta Elab Term Qq Std

namespace PyAstLean

#map_names [print → pyPrint, len → pyLen]

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
    | .null =>
        let noneIdent := mkIdent ``none
        `($noneIdent)
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
    let rec buildTuple (elts : List (TSyntax `term)) : PygenM (TSyntax `term) := do
      match elts with
      | [] => `(())
      | [single] => pure single
      | first :: rest => do
          let restTuple ← buildTuple rest
          `(($first, $restTuple))
    buildTuple eltCodes.toList
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

/-- Local copy of the exception-effect probe so `Call.doElem` can avoid a cyclic import on `Utils`. -/
partial def basicJsonUsesExceptionEffect (json : Json) : Bool :=
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
    | .arr elems => elems.toList.any basicJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesExceptionEffect value)
    | _ => false

/-- Detect the JSON encoding of Python's `None`. -/
def isNoneConstantJson (json : Json) : Bool :=
  match json.getObjValAs? String "node_type", json.getObjValAs? Json "value" with
  | .ok "Constant", .ok .null => true
  | _, _ => false
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
    let usePyContains :=
      match rightJson.getObjValAs? String "node_type" with
      | .ok "BinOp" => true
      | .ok "Constant" =>
          match rightJson.getObjValAs? Json "value" with
          | .ok (.str _) => true
          | _ => false
      | _ => false
    match op with
    | "eq" => `($leftCode == $rightCode)
    | "ne" => `($leftCode != $rightCode)
    | "lt" => `($leftCode < $rightCode)
    | "le" => `($leftCode <= $rightCode)
    | "gt" => `($leftCode > $rightCode)
    | "ge" => `($leftCode >= $rightCode)
    | "in" =>
        if usePyContains = true then
          let containsIdent := mkIdent ``pyContains
          `($containsIdent $rightCode $leftCode)
        else
          `(decide ($leftCode ∈ $rightCode))
    | "notin" =>
        if usePyContains = true then
          let containsIdent := mkIdent ``pyContains
          `(! ($containsIdent $rightCode $leftCode))
        else
          `(decide ($leftCode ∉ $rightCode))
    | _ => throwError s!"Unsupported comparison operator: {op}"
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
    let testCode ← getCode testJson `term
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

-- The registry for mapping Python standard library methods to Lean functions.
-- Add any future list or string methods here.
@[pygen "Call"]
def callSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"

    let argsCodes ← match argsJson with
      | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"

    -- NEW: Array to hold ALL arguments for a flat application
    let mut allArgs : Array (TSyntax `term) := #[]
    let mut funcIdent : TSyntax `term ← `("")

    -- 1. INTERCEPT METHOD CALLS
    if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
      let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
        s!"Attribute node missing 'value' field: {funcJson}"
      let .ok attr := funcJson.getObjValAs? String "attr" | throwError
        s!"Attribute node missing 'attr' field: {funcJson}"

      let valCode ← getCode valueJson `term

      -- Push the base object as the very first argument
      allArgs := allArgs.push valCode

      match pythonMethodMap attr with
      | some funcName =>
          funcIdent := mkIdent funcName
      | none =>
          throwError s!"Unsupported Python method '{attr}' encountered in Call node."

    -- 2. STANDARD FUNCTION CALLS
    else
      funcIdent ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok funcName =>
            let mappedName ← leanName funcName.toName
            pure <| (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            getCode funcJson `term

    -- 3. APPLY POSITIONAL ARGUMENTS
    for argCode in argsCodes do
      allArgs := allArgs.push argCode

    -- 4. APPLY KEYWORD ARGUMENTS
    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    -- 5. FLATTEN POSITIONAL CALL FIRST (Fixes the bracketing issue)
    -- This generates `funcIdent arg1 arg2` cleanly
    let mut t ← `($funcIdent $allArgs*)

    -- 6. APPLY KEYWORD ARGUMENTS ITERATIVELY
    -- Lean correctly parses `($id := $val)` here because it is in the context of an application
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
    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let argsCodes ← match argsJson with
      | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut funcIdent : TSyntax `term ← `("")

    -- 1. INTERCEPT METHOD CALLS
    if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
      let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
        s!"Attribute node missing 'value' field: {funcJson}"
      let .ok attr := funcJson.getObjValAs? String "attr" | throwError
        s!"Attribute node missing 'attr' field: {funcJson}"

      if attr == "append" then
        unless keyWordsMap.isEmpty do
          throwError "append() calls do not support keyword arguments."
        let argsArray ← match argsJson with
          | .arr arr => pure arr
          | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
        let some argJson := argsArray[0]? | throwError "append() expects exactly one positional argument."
        unless argsArray.size == 1 do
          throwError "append() expects exactly one positional argument."
        let targetIdent ← getCode valueJson `ident
        let argCode ← getCode argJson `term
        let pyAppendIdent := mkIdent ``pyAppend
        return ← `(doElem| $targetIdent:ident := $pyAppendIdent $targetIdent $argCode)

      let valCode ← getCode valueJson `term

      allArgs := allArgs.push valCode

      match pythonMethodMap attr with
      | some funcName =>
          funcIdent := mkIdent funcName
      | none =>
          throwError s!"Unsupported Python method '{attr}' encountered in Call node."

    -- 2. STANDARD FUNCTION CALLS
    else
      funcIdent ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok funcName =>
            let mappedName ← leanName funcName.toName
            pure <| (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            getCode funcJson `term

    -- 3. APPLY POSITIONAL ARGUMENTS
    for argCode in argsCodes do
      allArgs := allArgs.push argCode

    -- 5. FLATTEN POSITIONAL CALL FIRST (Fixes the bracketing issue)
    -- This generates `funcIdent arg1 arg2` cleanly
    let mut t ← `($funcIdent $allArgs*)

    -- 6. APPLY KEYWORD ARGUMENTS ITERATIVELY
    -- Lean correctly parses `($id := $val)` here because it is in the context of an application
    for (kwName, kwValueJson) in keyWordsMap.toList do
      let kwValueCode ← getCode kwValueJson `term
      let kwId := mkIdent kwName.toName
      t ← `($t ($kwId:ident := $kwValueCode))


    -- 5. FLATTEN THE CALL
    `(doElem| let _ := $t)

  | _, _ => throwError s!"Unsupported syntax category for Call node"

@[pygen "Attribute"]
def attributeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok attr := json.getObjValAs? String "attr" | throwError
      s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
    let valueCode ← getCode valueJson `term
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

@[pygen "Subscript"]
def subscriptSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Subscript node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok sliceJson := json.getObjValAs? Json "slice" | throwError
      s!"Subscript node does not have a 'slice' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    match sliceJson.getObjValAs? String "node_type", sliceJson.getObjValAs? Json "value" with
    | .ok "Constant", .ok (.num (JsonNumber.mk 0 0)) =>
        let fstIdent := mkIdent ``Prod.fst
        `($fstIdent $valueCode)
    | .ok "Constant", .ok (.num (JsonNumber.mk 1 0)) =>
        let sndIdent := mkIdent ``Prod.snd
        `($sndIdent $valueCode)
    | _, _ =>
        throwError "Only tuple subscript projections `[0]` and `[1]` are supported right now."
  | _, _ => throwError s!"Unsupported syntax category for Subscript node"


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
