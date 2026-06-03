import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Attributes

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Wrap each `print(...)` argument as `PyPrintArg.mk (pyStringify arg)`.

We do this explicitly instead of relying on the `CoeOut` into a `List PyPrintArg` literal:
the coercion pushes the expected element type `PyPrintArg` into each argument, which breaks
polymorphic argument terms such as `pyListGetItem a i` (the element type unifies with
`PyPrintArg`, then demands `Inhabited PyPrintArg`). Applying `pyStringify` lets each argument
elaborate at its natural type first; the result is identical for fixed-type arguments. -/
def wrapPrintArgs (resolvedArgs : Array (TSyntax `term)) : PygenM (Array (TSyntax `term)) := do
  let printArgIdent := mkIdent ``PyAstLean.PyPrintArg.mk
  let stringifyIdent := mkIdent ``PyAstLean.pyStringify
  resolvedArgs.mapM fun a => `($printArgIdent ($stringifyIdent $a))

/-- Local copy of the exception-effect probe so call lowering can avoid cyclic imports. -/
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

/-- Local copy of the IO-effect probe so calls can lift nested `input(...)` / `print(...)`. -/
partial def basicJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any basicJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesIOEffect value)
    | _ => false

/-- Detect whether a JSON subtree contains any translated monadic effect. -/
def basicJsonUsesMonadicEffect (json : Json) : Bool :=
  basicJsonUsesExceptionEffect json || basicJsonUsesIOEffect json

/--
Inline simple translated `IO` expressions directly as terms that contain local `←` binds.

This is used in surrounding `do` notation so code like `b = int(input())` can become
`let mut b := PyAstLean.pyInt (← PyAstLean.pyInputIO "")` instead of an extra nested
`do ... : IO _` wrapper.
-/
partial def inlineIOTerm (json : Json) : PygenM (TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return ← getCode json `term
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return ← getCode json `term
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          unless argsArray.size ≤ 1 do
            throwError "input() expects zero or one positional argument."
          let pyInputIOIdent := mkIdent ``pyInputIO
          match argsArray.size with
          | 0 => `((← $pyInputIOIdent ""))
          | 1 =>
              let arg0 ← inlineIOTerm argsArray[0]!
              `((← $pyInputIOIdent $arg0))
          | _ => throwError "input() expects zero or one positional argument."
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 do
            throwError "int() expects exactly one positional argument."
          let pyIntIdent := mkIdent ``pyInt
          let arg0 ← inlineIOTerm argsArray[0]!
          `($pyIntIdent $arg0)
      | _, _ =>
          let mut inlineArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              inlineArgs := inlineArgs.push (← inlineIOTerm argJson)
            else
              match argJson.getObjValAs? String "node_type", argJson.getObjValAs? String "id" with
              | .ok "Name", .ok funcName =>
                  match pythonBuiltinMap? funcName with
                  | some mappedName =>
                      inlineArgs := inlineArgs.push ((mkIdent mappedName : TSyntax `term))
                  | none =>
                      let mappedName ← leanName funcName.toName
                      inlineArgs := inlineArgs.push ((mkIdent mappedName : TSyntax `term))
              | _, _ =>
                  inlineArgs := inlineArgs.push (← getCode argJson `term)
          let mut funcTerm : TSyntax `term ← `("")
          if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
            let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
              s!"Attribute node missing 'value' field: {funcJson}"
            let .ok attr := funcJson.getObjValAs? String "attr" | throwError
              s!"Attribute node missing 'attr' field: {funcJson}"
            let receiverTerm ←
              if basicJsonUsesIOEffect valueJson then
                inlineIOTerm valueJson
              else
                getCode valueJson `term
            match pythonMethodMap attr with
            | some funcName =>
                let mapped := mkIdent funcName
                funcTerm ← `($mapped $receiverTerm)
            | none =>
                let attrId := mkIdent attr.toName
                funcTerm ← `($receiverTerm.$attrId)
          else
            match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
            | .ok "Name", .ok funcName =>
                match pythonBuiltinMap? funcName with
                | some mappedName => funcTerm := (mkIdent mappedName : TSyntax `term)
                | none =>
                    let mappedName ← leanName funcName.toName
                    funcTerm := (mkIdent mappedName : TSyntax `term)
            | _, _ =>
                funcTerm ← getCode funcJson `term
          let mut t ← `($funcTerm $inlineArgs*)
          for (kwName, kwValueJson) in keyWordsMap.toList do
            let kwValueCode ←
              if basicJsonUsesIOEffect kwValueJson then
                inlineIOTerm kwValueJson
              else
                getCode kwValueJson `term
            let kwId := mkIdent kwName.toName
            t ← `($t ($kwId:ident := $kwValueCode))
          return t
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let valueCode ← inlineIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      `($toStringIdent $valueCode)
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let valueCode ← inlineIOTerm valueJson
        res ← `($appendIdent $res $valueCode)
      pure res
  | _ =>
      return ← getCode json `term

/--
Hoist translated `IO` subexpressions into surrounding `do` blocks and return a pure term
that refers to the bound result.
-/
partial def hoistIOTerm (json : Json) : PygenM (Array (TSyntax `doElem) × TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return (#[], ← getCode json `term)
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return (#[], ← getCode json `term)
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyInputIOIdent := mkIdent ``pyInputIO
          let action ← match resolvedArgs.size with
            | 0 => `($pyInputIOIdent "")
            | 1 =>
                let arg0 := resolvedArgs[0]!
                `($pyInputIOIdent $arg0)
            | _ => throwError "input() expects zero or one positional argument."
          let binder := mkIdent (s!"__py_input{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 do
            throwError "int() expects exactly one positional argument."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyIntIdent := mkIdent ``pyInt
          let arg0 := resolvedArgs[0]!
          return (bindings, ← `($pyIntIdent $arg0))
      | .ok "Name", .ok "print" => do
          let supportedKeywords := ["sep", "end"]
          for (kwName, _) in keyWordsMap.toList do
            unless supportedKeywords.contains kwName do
              throwError s!"print() keyword argument '{kwName}' is not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyPrintIOIdent := mkIdent ``pyPrintIO
          let printArgs ← wrapPrintArgs resolvedArgs
          let action ← match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
            | none, none =>
                `($pyPrintIOIdent [$printArgs,*])
            | _, _ =>
                let sepCode ← match keyWordsMap.get? "sep" with
                  | some sepJson => getCode sepJson `term
                  | none => `(" ")
                let endCode ← match keyWordsMap.get? "end" with
                  | some endJson => getCode endJson `term
                  | none => `("\n")
                `($pyPrintIOIdent [$printArgs,*] $sepCode $endCode)
          let binder := mkIdent (s!"__py_print{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | _, _ =>
          return (#[], ← getCode json `term)
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let (bindings, valueTerm) ← hoistIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      return (bindings, ← `($toStringIdent $valueTerm))
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut bindings : Array (TSyntax `doElem) := #[]
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let (pieceBindings, pieceTerm) ← hoistIOTerm valueJson
        bindings := bindings ++ pieceBindings
        res ← `($appendIdent $res $pieceTerm)
      return (bindings, res)
  | _ =>
      return (#[], ← getCode json `term)

/-- Lift a pure function application into `IO` when any argument is already monadic. -/
def buildIOPureApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkResult : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let resultTerm ← mkResult resolvedArgs
  if bindings.isEmpty then
    return resultTerm
  let ioIdent := mkIdent ``IO
  `(((do
        $[$bindings:doElem]*
        return $resultTerm:term) : $ioIdent _))

/-- Lift an `IO`-returning application when some arguments are already monadic. -/
def buildIOActionApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkAction : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let actionTerm ← mkAction resolvedArgs
  if bindings.isEmpty then
    return actionTerm
  let ioIdent := mkIdent ``IO
  `(((do
        $[$bindings:doElem]*
        let __py_result ← $actionTerm:term
        return __py_result) : $ioIdent _))

end PyAstLean
