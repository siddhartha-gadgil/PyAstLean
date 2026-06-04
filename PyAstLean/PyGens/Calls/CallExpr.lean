import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Attributes
import PyAstLean.PyGens.Calls.CallEffects
import PyAstLean.PyGens.Calls.CallShared
import PyAstLean.PyGens.Calls.SpecialCalls

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Local effect probe for early string-lowering code, before the general call helpers below. -/
partial def stringJsonUsesExceptionEffect (json : Json) : Bool :=
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
    | .arr elems => elems.toList.any stringJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesExceptionEffect value)
    | _ => false

/-- Local effect probe for `IO`-bearing string pieces such as `input()` inside f-strings. -/
partial def stringJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any stringJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesIOEffect value)
    | _ => false

/-- Detect whether an early string subtree contains any translated monadic effect. -/
def stringJsonUsesMonadicEffect (json : Json) : Bool :=
  stringJsonUsesExceptionEffect json || stringJsonUsesIOEffect json

@[pygen "FormattedValue"]
def formattedValueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    let toStringIdent := mkIdent ``toString
    if stringJsonUsesMonadicEffect valueJson then
      let binder := mkIdent `__py_fmt
      let stringIdent := mkIdent ``String
      let effectTy ←
        if stringJsonUsesExceptionEffect valueJson then
          let exceptIdent := mkIdent ``PyAstLean.PyExcept
          `($exceptIdent $stringIdent)
        else
          let ioIdent := mkIdent ``IO
          `($ioIdent $stringIdent)
      `(((do
            let $binder:ident ← $valueCode:term
            return ($toStringIdent $binder:term)) :
          $effectTy))
    else
      `($toStringIdent $valueCode)
  | _, _ => throwError s!"Unsupported syntax category for FormattedValue node"

@[pygen "JoinedStr"]
def joinedStrSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesArray ← match valuesJson with
      | .arr arr => pure arr
      | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
    let valuesCodes ← valuesArray.mapM (fun valueJson => getCode valueJson `term)
    let appendIdent := mkIdent ``String.append
    let mut res : TSyntax `term ← `("")
    let mut bindings : Array (TSyntax `doElem) := #[]
    for idx in [0:valuesCodes.size] do
      let valueJson := valuesArray[idx]!
      let valueCode := valuesCodes[idx]!
      if stringJsonUsesMonadicEffect valueJson then
        let binder := mkIdent (s!"__py_join{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $valueCode:term))
        res ← `($appendIdent $res $binder:term)
      else
        res ← `($appendIdent $res $valueCode)
    if bindings.isEmpty then
      return res
    let stringIdent := mkIdent ``String
    let effectTy ←
      if stringJsonUsesExceptionEffect json then
        let exceptIdent := mkIdent ``PyAstLean.PyExcept
        `($exceptIdent $stringIdent)
      else
        let ioIdent := mkIdent ``IO
        `($ioIdent $stringIdent)
    `(((do
          $[$bindings:doElem]*
          return $res:term) :
        $effectTy))
  | _, _ => throwError s!"Unsupported syntax category for JoinedStr node"

/-- Map a bare Python builtin function name to the Lean runtime symbol when it is used as a value. -/
def mappedCallableValueCode (json : Json) : PygenM (TSyntax `term) := do
  match ← jsonLibraryMappedName? json with
  | some leanName =>
      pure (mkIdent leanName : TSyntax `term)
  | none =>
      match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          match pythonBuiltinMap? funcName with
          | some mappedName => pure (mkIdent mappedName : TSyntax `term)
          | none =>
              let mappedName ← leanName funcName.toName
              pure (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode json `term

@[pygen "Call"]
def callSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let argsArray ← match argsJson with
      | .arr arr => pure arr
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    let argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← lowerSpecialCallTerm? funcJson argsArray argsCodes keyWordsMap with
    | some lowered => return lowered
    | none => pure ()

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          match argsArray.size with
          | 1 =>
              let keyCode ← getCode argsArray[0]! `term
              let pyGetOptIdent := mkIdent ``pyGetOpt?
              return ← `($pyGetOptIdent $valCode $keyCode)
          | 2 =>
              let keyCode ← getCode argsArray[0]! `term
              let defaultCode ← getCode argsArray[1]! `term
              let pyGetDIdent := mkIdent ``pyGetD
              return ← `($pyGetDIdent $valCode $keyCode $defaultCode)
          | _ =>
              throwError "get() expects one or two positional arguments."

        if attr == "sort" then
          throwError "sort() is only supported as a statement; use sorted(x) in expressions."

        -- `pop` both returns a value and mutates its receiver, which a pure term cannot express.
        -- Refuse it in expression position so the pure-function path falls back to the monadic
        -- lowering, where `x = container.pop(...)` is handled as a statement (value bind +
        -- container update). `pop` in any other expression position stays a clear error.
        if attr == "pop" then
          throwError "pop() returns a value *and* mutates its receiver; it is only supported as \
            a direct assignment `x = container.pop(...)`, not as a sub-expression."

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
        | none =>
            throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent ``pyPrintIO
              let printArgs ← buildPrintArgsList argsArray resolvedArgs
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($pyPrintIOIdent $printArgs)
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($pyPrintIOIdent $printArgs $sepCode $endCode)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            let pyInputIOIdent := mkIdent ``pyInputIO
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($pyInputIOIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($pyInputIOIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "int() expects exactly one positional argument."
            let pyIntIdent := mkIdent ``pyInt
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyIntIdent $arg0)
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            return ← match argsArray.size with
            | 0 => `("")
            | 1 =>
                let pyStrIdent := mkIdent ``pyStr
                buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  let arg0 := resolvedArgs[0]!
                  `($pyStrIdent $arg0)
            | _ =>
                throwError "str() expects zero or one positional argument."
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
        | .ok "Name", .ok "sorted" => do
            -- `sorted(iterable)` → `pySort`; `sorted(iterable, key=f, reverse=b)` → `pySortBy`.
            -- Only `key`/`reverse` keywords are meaningful for Python's `sorted`.
            for (kwName, _) in keyWordsMap.toList do
              unless kwName == "key" || kwName == "reverse" do
                throwError s!"sorted() keyword argument '{kwName}' is not supported yet."
            unless argsArray.size == 1 do
              throwError "sorted() expects exactly one positional argument (the iterable)."
            match keyWordsMap.get? "key", keyWordsMap.get? "reverse" with
            | none, none =>
                let pySortIdent := mkIdent ``pySort
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  `($pySortIdent $(resolvedArgs[0]!))
            | keyOpt, revOpt =>
                let keyCode ← match keyOpt with
                  | some kJson => mappedCallableValueCode kJson
                  | none => `(fun x => x)
                let revCode ← match revOpt with
                  | some rJson => getCode rJson `term
                  | none => `(false)
                let pySortByIdent := mkIdent ``pySortBy
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  `($pySortByIdent $keyCode $revCode $(resolvedArgs[0]!))
        | .ok "Name", .ok funcName =>
            match pythonBuiltinMap? funcName with
            | some mappedName => funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                let mappedName ← leanName funcName.toName
                funcIdent := (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      let mut t ← `($funcIdent $resolvedArgs*)
      for (kwName, kwValueJson) in keyWordsMap.toList do
        let kwValueCode ← getCode kwValueJson `term
        let kwId := mkIdent kwName.toName
        t ← `($t ($kwId:ident := $kwValueCode))
      return t

    if allArgJsons.toList.any basicJsonUsesIOEffect then
      return ← buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
    else
      return ← buildApplied allArgs
  | `doElem, json => do
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

    let argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← lowerSpecialCallDoElem? funcJson argsArray argsCodes keyWordsMap with
    | some lowered => return lowered
    | none => pure ()

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        if attr == "append" then
          unless keyWordsMap.isEmpty do
            throwError "append() calls do not support keyword arguments."
          let some argJson := argsArray[0]? | throwError "append() expects exactly one positional argument."
          unless argsArray.size == 1 do
            throwError "append() expects exactly one positional argument."
          let targetIdent ← getCode valueJson `ident
          let argCode ← getCode argJson `term
          let pyAppendIdent := mkIdent ``pyAppend
          return ← `(doElem| $targetIdent:ident := $pyAppendIdent $targetIdent $argCode)

        -- Set mutators rebuild the set and reassign the variable, like `append`.
        if attr == "add" || attr == "discard" || attr == "remove" then
          unless keyWordsMap.isEmpty do
            throwError s!"{attr}() calls do not support keyword arguments."
          let some argJson := argsArray[0]? | throwError s!"{attr}() expects exactly one positional argument."
          unless argsArray.size == 1 do
            throwError s!"{attr}() expects exactly one positional argument."
          let targetIdent ← getCode valueJson `ident
          let argCode ← getCode argJson `term
          let mutIdent := match attr with
            | "add" => mkIdent ``pySetAdd
            | "discard" => mkIdent ``pySetDiscard
            | _ => mkIdent ``pySetRemove
          return ← `(doElem| $targetIdent:ident := $mutIdent $targetIdent $argCode)

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          let t ← match argsArray.size with
            | 1 =>
                let keyCode ← getCode argsArray[0]! `term
                let pyGetOptIdent := mkIdent ``pyGetOpt?
                `($pyGetOptIdent $valCode $keyCode)
            | 2 =>
                let keyCode ← getCode argsArray[0]! `term
                let defaultCode ← getCode argsArray[1]! `term
                let pyGetDIdent := mkIdent ``pyGetD
                `($pyGetDIdent $valCode $keyCode $defaultCode)
            | _ =>
                throwError "get() expects one or two positional arguments."
          return ← `(doElem| let _ := $t)

        if attr == "sort" then
          -- In-place `list.sort()`: lower to a reassignment of the (immutable-value) list.
          -- Supports Python's `key=` / `reverse=` keywords; rejects positional args.
          for (kwName, _) in keyWordsMap.toList do
            unless kwName == "key" || kwName == "reverse" do
              throwError s!"sort() keyword argument '{kwName}' is not supported yet."
          unless argsArray.isEmpty do
            throwError "sort() expects no positional arguments."
          let targetIdent ← getCode valueJson `ident
          match keyWordsMap.get? "key", keyWordsMap.get? "reverse" with
          | none, none =>
              let pySortIdent := mkIdent ``pySort
              return ← `(doElem| $targetIdent:ident := $pySortIdent $targetIdent)
          | keyOpt, revOpt =>
              let keyCode ← match keyOpt with
                | some kJson => mappedCallableValueCode kJson
                | none => `(fun x => x)
              let revCode ← match revOpt with
                | some rJson => getCode rJson `term
                | none => `(false)
              let pySortByIdent := mkIdent ``pySortBy
              return ← `(doElem| $targetIdent:ident := $pySortByIdent $keyCode $revCode $targetIdent)

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
        | none =>
            throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent ``pyPrintIO
              let printArgs ← buildPrintArgsList argsArray resolvedArgs
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($pyPrintIOIdent $printArgs)
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($pyPrintIOIdent $printArgs $sepCode $endCode)
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            let pyInputIOIdent := mkIdent ``pyInputIO
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($pyInputIOIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($pyInputIOIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "int() expects exactly one positional argument."
            let pyIntIdent := mkIdent ``pyInt
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyIntIdent $arg0)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            let t ← match argsArray.size with
              | 0 => `("")
              | 1 =>
                  let pyStrIdent := mkIdent ``pyStr
                  buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                    let arg0 := resolvedArgs[0]!
                    `($pyStrIdent $arg0)
              | _ =>
                  throwError "str() expects zero or one positional argument."
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok funcName =>
            match pythonBuiltinMap? funcName with
            | some mappedName => funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                let mappedName ← leanName funcName.toName
                funcIdent := (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      let mut t ← `($funcIdent $resolvedArgs*)
      for (kwName, kwValueJson) in keyWordsMap.toList do
        let kwValueCode ← getCode kwValueJson `term
        let kwId := mkIdent kwName.toName
        t ← `($t ($kwId:ident := $kwValueCode))
      return t

    if allArgJsons.toList.any basicJsonUsesIOEffect then
      let t ← buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
      `(doElem| let _ ← $t:term)
    else
      let t ← buildApplied allArgs
      if basicJsonUsesMonadicEffect json then
        `(doElem| let _ ← $t:term)
      else
        `(doElem| let _ := $t)
  | _, _ => throwError s!"Unsupported syntax category for Call node"

@[pygen "Attribute"]
def attributeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let valueCode ← getCode valueJson `term
        let attrId := mkIdent attr.toName
        `($valueCode.$attrId)
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let id ← getCode valueJson `ident
        return mkIdent <| id.getId ++ attr.toName
  | _, _ => throwError s!"Unsupported syntax category for Attribute node"

end PyAstLean
