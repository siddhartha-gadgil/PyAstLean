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

/-- If `json` is a string-literal `Constant`, return its text (the literal pieces of an
f-string). Otherwise `none` — those pieces are interpolated values. -/
def jsonStringLiteral? (json : Json) : Option String :=
  match json.getObjValAs? String "node_type" with
  | .ok "Constant" =>
      match json.getObjVal? "value" with
      | .ok (.str s) => some s
      | _ => none
  | _ => none

/-- Escape a literal chunk so it is safe inside a Lean interpolated string `s!"…"`: backslash,
double quote and the interpolation braces are escaped, and control characters spelled out. -/
def escapeInterpChunk (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\"
      | '"' => "\\\""
      | '{' => "\\{"
      | '}' => "\\}"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => "\\r"
      | _ => c.toString)) ""

/-- The term placed inside `{…}` for an interpolated f-string slot. For a `FormattedValue` the
inner value is used directly (Lean's `s!` applies `toString`); anything else is lowered as-is. -/
def joinedInterpTerm (valueJson : Json) : PygenM (TSyntax `term) := do
  match valueJson.getObjValAs? String "node_type" with
  | .ok "FormattedValue" =>
      let innerCode ← match valueJson.getObjVal? "value" with
        | .ok inner => getCode inner `term
        | .error _ => getCode valueJson `term
      -- A `:.Nf`-style format spec wraps the value in `pyFormatSpec`, which returns the formatted
      -- String (and `s!`'s `toString` on a String is the identity).
      match valueJson.getObjValAs? String "format_spec" with
      | .ok spec =>
          let fmtIdent := mkIdent ``PyAstLean.pyFormatSpec
          let specLit := Syntax.mkStrLit spec
          `($fmtIdent $innerCode $specLit)
      | .error _ => pure innerCode
  | _ => getCode valueJson `term

/-- Build a Lean interpolated string `s!"lit{e}lit…"` from the literal/interpolation pieces of an
f-string. `chunks` has exactly one more element than `interps` and they alternate
`chunk₀ interp₀ chunk₁ … interpₙ₋₁ chunkₙ`. -/
def mkInterpolatedStr (chunks : Array String) (interps : Array (TSyntax `term)) :
    TSyntax `term := Id.run do
  let n := interps.size
  let mut children : Array Syntax := #[]
  for i in [0:n+1] do
    let text := escapeInterpChunk (chunks[i]!)
    let atomStr :=
      if i == 0 then "\"" ++ text ++ "{"
      else if i == n then "}" ++ text ++ "\""
      else "}" ++ text ++ "{"
    children := children.push
      (Syntax.node SourceInfo.none `interpolatedStrLitKind #[Syntax.atom SourceInfo.none atomStr])
    if i < n then
      children := children.push interps[i]!.raw
  let interpNode := Syntax.node SourceInfo.none `interpolatedStrKind children
  ⟨Syntax.node SourceInfo.none (Name.mkSimple "termS!_")
    #[Syntax.atom SourceInfo.none "s!", interpNode]⟩

@[pygen "JoinedStr"]
def joinedStrSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesArray ← match valuesJson with
      | .arr arr => pure arr
      | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
    -- The common, all-pure case lowers to a readable `s!"…{e}…"` interpolation. Effectful
    -- pieces (e.g. `← input()` inside an f-string) can't sit inside `s!`, so those fall back to
    -- the `do`-bound append chain below.
    if !valuesArray.any stringJsonUsesMonadicEffect then
      let mut chunks : Array String := #[]
      let mut interps : Array (TSyntax `term) := #[]
      let mut buf : String := ""
      for valueJson in valuesArray do
        match jsonStringLiteral? valueJson with
        | some s => buf := buf ++ s
        | none =>
            chunks := chunks.push buf
            buf := ""
            interps := interps.push (← joinedInterpTerm valueJson)
      chunks := chunks.push buf
      if interps.isEmpty then
        return Syntax.mkStrLit chunks[0]!
      return mkInterpolatedStr chunks interps
    let appendIdent := mkIdent ``String.append
    let valuesCodes ← valuesArray.mapM (fun valueJson => getCode valueJson `term)
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

/-- Fold a binary runtime function `fn` over `args` (length ≥ 2), associating per `dir`. A right
fold builds `fn a₁ (fn a₂ (… (fn aₙ₋₁ aₙ)))`; a left fold builds `fn (… (fn a₁ a₂) …) aₙ`. Drives
the variadic-builtin lowering (e.g. `zip`) from `variadicFoldBuiltin?`. -/
def foldBinaryOverArgs (fn : TSyntax `term) (dir : BuiltinFoldDir) (args : Array (TSyntax `term)) :
    PygenM (TSyntax `term) := do
  match dir with
  | .right =>
      let mut acc := args[args.size - 1]!
      for i in (List.range (args.size - 1)).reverse do
        acc ← `($fn $(args[i]!) $acc)
      pure acc
  | .left =>
      let mut acc := args[0]!
      for i in [1:args.size] do
        acc ← `($fn $acc $(args[i]!))
      pure acc

/-- Map a bare Python builtin function name to the Lean runtime symbol when it is used as a value. -/
def mappedCallableValueCode (json : Json) : PygenM (TSyntax `term) := do
  match ← jsonLibraryMappedName? json with
  | some leanName =>
      pure (mkIdent leanName : TSyntax `term)
  | none =>
      match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          match ← builtinMappedName? funcName with
          | some mappedName => pure (mkIdent mappedName : TSyntax `term)
          | none =>
              let mappedName ← leanName funcName.toName
              pure (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode json `term

/-- Lower `min(...)` / `max(...)` (`which` is `"min"` or `"max"`). Handles a single iterable
(`min(xs)`), several positionals gathered into a list (`min(a, b, c)`), and the optional
`key=f` keyword (→ `pyMinBy`/`pyMaxBy`). -/
def lowerMinMaxCall (which : String) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (TSyntax `term) := do
  for (kwName, _) in keyWordsMap.toList do
    unless kwName == "key" do
      throwError s!"{which}() keyword argument '{kwName}' is not supported yet."
  unless argsArray.size ≥ 1 do
    throwError s!"{which}() expects at least one argument."
  let keyOpt := keyWordsMap.get? "key"
  buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
    let iterable ← if resolvedArgs.size == 1 then pure resolvedArgs[0]!
      else `([$resolvedArgs,*])
    match keyOpt with
    | none =>
        let fn := mkIdent (if which == "min" then ``pyMin else ``pyMax)
        `($fn $iterable)
    | some kJson =>
        let keyCode ← mappedCallableValueCode kJson
        let fn := mkIdent (if which == "min" then ``pyMinBy else ``pyMaxBy)
        `($fn $keyCode $iterable)

/-- Resolve the class of a method-call receiver `recv.m(...)`: `self` inside a class body resolves
to the class being lowered; otherwise fall back to the unique registered class that declares a
method named `attr`. `none` when it can't be determined (an unknown/ambiguous method). -/
def resolveReceiverClass? (valueJson : Json) (attr : String) : PygenM (Option String) := do
  if jsonNodeType? valueJson == some "Name"
      && valueJson.getObjValAs? String "id" == .ok "self" then
    match (← get).currentClass with
    | some c => return some c
    | none => pure ()
  classOfMethod? attr

/-- The class to construct for a call `f(...)` whose callee is the `Name` `funcName`: a registered
class (`C(..)`), or `cls(..)` inside a class body (classmethod sugar). `none` for ordinary calls. -/
def constructorClassOfName? (funcName : String) : PygenM (Option String) := do
  if ← isRegisteredClass funcName then return some funcName
  if funcName == "cls" then return (← get).currentClass
  return none

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

        -- `ClassName.method(args)` (static/classmethod/unbound) -> `C.method args`, no receiver.
        if let some cls := (json.getObjValAs? String "_static_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if argsArray.toList.any basicJsonUsesIOEffect then
            return ← buildIOPureApplicationFromArgs argsArray argsCodes build
          else
            return ← build argsCodes

        -- A method call on a known class instance (`_receiver_class` stamped by py2lean) dispatches
        -- to `C.attr recv args` and takes precedence over the builtin-method special-cases below,
        -- so a user method may shadow a builtin name (`get`, `pop`, …).
        if let some cls := (json.getObjValAs? String "_receiver_class").toOption then
          if (json.getObjValAs? Bool "_is_mutator").toOption.getD false then
            throwError s!"Mutating method '{attr}' cannot be used as an expression under value \
              semantics; call it as a statement on its own line."
          let valCode ← getCode valueJson `term
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let allJsons := #[valueJson] ++ argsArray
          let allCodes := #[valCode] ++ argsCodes
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if allJsons.toList.any basicJsonUsesIOEffect then
            return ← buildIOPureApplicationFromArgs allJsons allCodes build
          else
            return ← build allCodes

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

        if attr == "format" then
          -- `"… {} …".format(a, b)`: stringify each argument and fill the `{}` placeholders.
          unless keyWordsMap.isEmpty do
            throwError "str.format() keyword arguments are not supported yet."
          let receiverCode ← getCode valueJson `term
          let stringifyIdent := mkIdent ``PyAstLean.pyStringify
          let formatIdent := mkIdent ``PyAstLean.pyStrFormat
          return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
            let stringified ← resolvedArgs.mapM (fun a => `($stringifyIdent $a))
            `($formatIdent $receiverCode [$stringified,*])

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
            -- A user-defined method `recv.m(args)` -> `C.m recv args` (receiver already pushed).
            -- Prefer the py2lean stamp (`_receiver_class`/`_is_mutator`); fall back to the registry.
            let cls? ← match (json.getObjValAs? String "_receiver_class").toOption with
              | some c => pure (some c)
              | none => resolveReceiverClass? valueJson attr
            match cls? with
            | some cls =>
                let isMut ← match (json.getObjValAs? Bool "_is_mutator").toOption with
                  | some b => pure b
                  | none => methodIsMutator cls attr
                if isMut then
                  throwError s!"Mutating method '{attr}' cannot be used as an expression under \
                    value semantics; call it as a statement on its own line."
                funcIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
            | none =>
                throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            -- `prove` (exact) semantics: `print` is a no-op (theorems, not output) — hoist IO args
            -- (e.g. `input()`) for their side effect, then `pyPrintNoop` with no rendering.
            if (← getNumericMode) == .exact then
              return ← buildIOActionApplicationFromArgs argsArray argsCodes fun _ =>
                `($(mkIdent `pyPrintNoop))
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent `pyPrintIO
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
        | .ok "Name", .ok "round" => do
            -- `round(x)` returns an `int` (banker's rounding); `round(x, n)` returns a `float`.
            unless keyWordsMap.isEmpty do
              throwError "round() keyword arguments are not supported yet."
            match argsArray.size with
            | 1 =>
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun r => do
                  `($(mkIdent ``pyRound) $(r[0]!))
            | 2 =>
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun r => do
                  `($(mkIdent ``pyRoundDigits) $(r[0]!) $(r[1]!))
            | _ => throwError "round() expects one or two arguments."
        | .ok "Name", .ok "min" => return ← lowerMinMaxCall "min" argsArray argsCodes keyWordsMap
        | .ok "Name", .ok "max" => return ← lowerMinMaxCall "max" argsArray argsCodes keyWordsMap
        | .ok "Name", .ok funcName =>
            -- Class instantiation `C(args)` (or `cls(args)` in a classmethod) -> `C.mk args`.
            -- Prefer the py2lean dispatch stamp (`_class_ctor`); fall back to the local registry.
            match ← (do match (json.getObjValAs? String "_class_ctor").toOption with
                        | some c => pure (some c) | none => constructorClassOfName? funcName) with
            | some cls => funcIdent := (mkIdent (Name.mkStr (← suffixIfUserName cls).toName "new") : TSyntax `term)
            | none =>
            -- Variadic builtins that fold a binary runtime function over their args (e.g. `zip`)
            -- are handled generically from the `variadicFoldBuiltin?` registry — one handler for
            -- all of them, so a new such builtin is a registry row, not a branch here.
            if let some (foldFn, dir) := variadicFoldBuiltin? funcName then
              unless keyWordsMap.isEmpty do
                throwError s!"{funcName}() keyword arguments are not supported yet."
              unless argsArray.size ≥ 2 do
                throwError s!"{funcName}() expects at least two arguments."
              let foldIdent := mkIdent foldFn
              return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                foldBinaryOverArgs foldIdent dir resolvedArgs
            else match ← builtinMappedName? funcName with
            | some mappedName => funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                let mappedName ← leanName (← suffixIfUserName funcName).toName
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

        -- `ClassName.method(args)` (static/classmethod/unbound) as a statement.
        if let some cls := (json.getObjValAs? String "_static_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if argsArray.toList.any basicJsonUsesIOEffect then
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes build
            return ← `(doElem| let _ ← $t:term)
          else
            let t ← build argsCodes
            if basicJsonUsesMonadicEffect json then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)

        -- A method call on a known class instance (`_receiver_class` stamped by py2lean) dispatches
        -- here, taking precedence over the builtin-method special-cases. A mutator on a bare
        -- variable reassigns it (`obj := C.m obj args`); a getter is run/bound like any call.
        if let some cls := (json.getObjValAs? String "_receiver_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          if (json.getObjValAs? Bool "_is_mutator").toOption.getD false then
            if jsonNodeType? valueJson == some "Name" then
              let targetIdent ← getCode valueJson `ident
              return ← `(doElem| $targetIdent:ident := $methodIdent $targetIdent $argsCodes*)
            else
              throwError s!"Mutating method '{attr}' on a non-variable receiver is not supported \
                under value semantics."
          let valCode ← getCode valueJson `term
          let allJsons := #[valueJson] ++ argsArray
          let allCodes := #[valCode] ++ argsCodes
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if allJsons.toList.any basicJsonUsesIOEffect then
            let t ← buildIOPureApplicationFromArgs allJsons allCodes build
            return ← `(doElem| let _ ← $t:term)
          else
            let t ← build allCodes
            if basicJsonUsesMonadicEffect json then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)

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
            -- User method in statement position. A mutator on a bare variable receiver reassigns
            -- it (`obj := C.m obj args`, value semantics); a getter falls through to `C.m recv …`.
            let cls? ← match (json.getObjValAs? String "_receiver_class").toOption with
              | some c => pure (some c)
              | none => resolveReceiverClass? valueJson attr
            match cls? with
            | some cls =>
                let isMut ← match (json.getObjValAs? Bool "_is_mutator").toOption with
                  | some b => pure b
                  | none => methodIsMutator cls attr
                if isMut then
                  if jsonNodeType? valueJson == some "Name" then
                    let targetIdent ← getCode valueJson `ident
                    let methodIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
                    return ← `(doElem| $targetIdent:ident := $methodIdent $targetIdent $argsCodes*)
                  else
                    throwError s!"Mutating method '{attr}' on a non-variable receiver is not \
                      supported under value semantics."
                else
                  funcIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
            | none =>
                throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            if (← getNumericMode) == .exact then
              -- `prove` no-op `print` (see the other print site): preserve `input()` side effects,
              -- drop the rendering.
              let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun _ =>
                `($(mkIdent `pyPrintNoop))
              return ← `(doElem| let _ ← $t:term)
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent `pyPrintIO
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
            match ← (do match (json.getObjValAs? String "_class_ctor").toOption with
                        | some c => pure (some c) | none => constructorClassOfName? funcName) with
            | some cls => funcIdent := (mkIdent (Name.mkStr (← suffixIfUserName cls).toName "new") : TSyntax `term)
            | none =>
            match ← builtinMappedName? funcName with
            | some mappedName => funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                let mappedName ← leanName (← suffixIfUserName funcName).toName
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
