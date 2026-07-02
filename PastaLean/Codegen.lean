import Lean
import Qq
import PastaLean.Basic

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-!
## Numeric lowering mode

Controls how a Python `float` is lowered: `exact` → Lean `ℚ` (an exact, *computable* and
*provable* ordered field — the default, so generated functions can be reasoned about with
`ring`/`nlinarith`); `approx` → `Float` (IEEE; fast and computable but not a ring, so unprovable).
The mode is set per backend request (see `py2lean.lean`) into a global ref the codegen reads.
-/

inductive NumericMode where
  | exact
  | approx
  deriving Repr, BEq, Inhabited

initialize numericModeRef : IO.Ref NumericMode ← IO.mkRef .exact

/-- Read the current numeric lowering mode (set per backend request). -/
def getNumericMode : IO NumericMode := numericModeRef.get

/-- True when `float` should lower to `ℚ` (the default exact mode). -/
def numericModeIsExact : IO Bool := return (← getNumericMode) == .exact

/-- Whether the function currently being lowered is "real-valued" — it (transitively) produces an
`ℝ` transcendental (the Python pass stamps such defs `_real_fn`). While set, exact-mode `float`
literals/params lower to `ℝ` instead of `ℚ`, so the whole function is uniformly `ℝ` (noncomputable)
rather than a `ℚ`/`ℝ` mix that won't type-check. Only consulted in exact mode. -/
initialize realContextRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether we're lowering inside a real-valued (`ℝ`) function body. -/
def getRealContext : IO Bool := realContextRef.get

/-- True while lowering a *condition position* — the direct test of an `if`/`while` — where a
comparison may be a `Prop` (`a < b`, and `a = b`/`a ≠ b` in exact mode) so it is provable, paired
with the `if h : …` hypothesis. False everywhere else (the default): a comparison used as a *value*
— a comprehension element, an `and`/`or` operand, an `any`/`all` generator — must stay `Bool`
(`decide (a < b)`, `==`), since a `Prop` has no value there. `Float` equality stays `==` regardless
(no `DecidableEq`). See `compareApplyTerm`. -/
initialize propConditionRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether comparisons may currently lower to a provable `Prop` (condition position). -/
def getPropCondition : IO Bool := propConditionRef.get

/-- When emitting the runnable "twin" of a declaration in `--mode both`, this is the suffix (`'rn`)
appended to every top-level definition name AND to references to other user-defined functions/classes
(listed in `userNamesRef`). Empty for the single-version `prove`/`run` modes. Lets one file carry the
provable `foo` and the runnable `foo'rn` side by side. -/
initialize runSuffixRef : IO.Ref String ← IO.mkRef ""

/-- The names of the user's top-level functions/classes — references to these get `runSuffix` appended
in a run-twin so `foo'rn` calls `bar'rn` / builds `CNN'rn`, not the `prove` `bar`/`CNN`. -/
initialize userNamesRef : IO.Ref (List String) ← IO.mkRef []

/-- The suffix to append to a top-level def name being emitted (empty unless in a run-twin). -/
def getRunSuffix : IO String := runSuffixRef.get

/-- Append the run-twin suffix to a name unconditionally (for the def being emitted). -/
def withRunSuffix (name : String) : IO String := return name ++ (← getRunSuffix)

/-- Append the run-twin suffix to a *reference* only when it names a user function/class (so locals
and library names are untouched). -/
def suffixIfUserName (name : String) : IO String := do
  if (← userNamesRef.get).contains name then return name ++ (← getRunSuffix) else return name

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `pygenerator` a Json object and a syntax category, and returns the corresponding syntax (in the monad `PygenM`) or throws an error.
-/

namespace PyGen

structure State where
  varNames : HashSet Name := HashSet.emptyWithCapacity 100
  checkExr : Bool := true
  useArrow : Bool := false
  /-- When the innermost enclosing loop has a Python `else` clause, this holds the name of the
  `let mut` flag that records whether a `break` fired (so the `else` runs only on natural
  completion). `none` means the innermost loop has no `else`, so `break` lowers plainly. -/
  breakFlag : Option Name := none
  /-- While lowering the methods of a `class C`, the class name `C` (so `self.method(..)` calls
  inside the body dispatch to `C.method`). `none` outside any class body. -/
  currentClass : Option String := none
  /-- The mutator-method names of the class currently being lowered (a `self.m(..)` call to one of
  these reassigns `self`). Empty outside a class body. -/
  currentClassMutators : List String := []
  deriving Inhabited, Repr

end PyGen

abbrev PygenM := StateT PyGen.State TermElabM

def withPygenState {α : Type} (modifyState : PyGen.State → PyGen.State) (x : PygenM α) :
    PygenM α := do
  let saved ← get
  set (modifyState saved)
  try
    let result ← x
    set saved
    return result
  catch e =>
    set saved
    throw e

def withPygenStateField {α β : Type} (getField : PyGen.State → β)
    (setField : PyGen.State → β → PyGen.State) (value : β) (x : PygenM α) :
    PygenM α := do
  let saved := getField (← get)
  modify fun st => setField st value
  try
    let result ← x
    modify fun st => setField st saved
    return result
  catch e =>
    modify fun st => setField st saved
    throw e

def withoutCheck {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField (·.checkExr) (fun st checkExr => { st with checkExr := checkExr }) false x

def withUseArrow {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField (·.useArrow) (fun st useArrow => { st with useArrow := useArrow }) true x

/-- Run `x` with the real-context flag set to `b` (restoring it afterwards). Used to lower a
real-marked assignment's RHS so its float literals (and list literals) become `ℝ`. -/
def withRealContext {α : Type} (b : Bool) (x : PygenM α) : PygenM α := do
  let saved ← realContextRef.get
  realContextRef.set b
  try
    let r ← x
    realContextRef.set saved
    return r
  catch e =>
    realContextRef.set saved
    throw e

/-- Run `x` with the prop-condition flag set to `b` (restoring it afterwards). `if`/`while` set it
`true` around lowering their test; `and`/`or`/`not` operands set it back `false` (they need `Bool`). -/
def withPropCondition {α : Type} (b : Bool) (x : PygenM α) : PygenM α := do
  let saved ← propConditionRef.get
  propConditionRef.set b
  try
    let r ← x
    propConditionRef.set saved
    return r
  catch e =>
    propConditionRef.set saved
    throw e

/-- Lower `x` in real-context when `json` carries the per-variable `_real` stamp (exact mode) — set
by the Python pass on every assignment whose root variable holds an `ℝ` value, so the RHS literals
are born `ℝ` (scalars would coerce, but `List ℚ ↛ List ℝ`, so list literals must be `ℝ` directly). -/
def withRealIfMarked {α : Type} (json : Lean.Json) (x : PygenM α) : PygenM α := do
  if (← getNumericMode) == .exact && json.getObjValAs? Bool "_real" == .ok true then
    withRealContext true x
  else
    x

def withFixedVariables {α : Type} (x : PygenM α) : PygenM α := do
  withPygenStateField (·.varNames) (fun st varNames => { st with varNames := varNames }) (← get).varNames x

/-- Run `x` with the current loop's break-flag set to `flag?`. A loop body always overrides the
flag (to its own `else` flag, or `none`) so a `break` binds to the innermost loop only. -/
def withBreakFlag {α : Type} (flag? : Option Name) (x : PygenM α) : PygenM α :=
  withPygenStateField (·.breakFlag) (fun st breakFlag => { st with breakFlag := breakFlag }) flag? x

def getBreakFlag : PygenM (Option Name) := do
  return (← get).breakFlag

def isCheckEnabled : PygenM Bool := do
  return (← get).checkExr

def isUseArrowEnabled : PygenM Bool := do
  return (← get).useArrow

def hasVar (usedName : Name) : PygenM Bool := do
  return (← get).varNames.contains usedName

def addVar (usedName : Name) : PygenM Unit := do
  modify fun st => { st with varNames := st.varNames.insert usedName }

/-- Run `x` while lowering the body of `class name` (with mutator set `mutators`), so `self.m(..)`
calls inside dispatch to `name.m` and reassign `self` when `m` mutates. Restored on exit. -/
def withCurrentClass {α : Type} (name : String) (mutators : List String) (x : PygenM α) : PygenM α :=
  withPygenStateField (·.currentClass) (fun st v => { st with currentClass := v }) (some name) <|
    withPygenStateField (·.currentClassMutators)
      (fun st v => { st with currentClassMutators := v }) mutators x

/-- Metadata about a generated Python class, recorded when its `ClassDef` is lowered so later
top-level statements can dispatch instantiation (`C(..)` → `C.mk`) and method calls
(`obj.m(..)` → `C.m obj ..`, with mutators reassigning the receiver). -/
structure ClassInfo where
  methods : List String := []
  mutators : List String := []
  staticmethods : List String := []
  classmethods : List String := []
  deriving Inhabited, Repr

/-- Process-global registry of generated classes. The Lean backend is a persistent server that
streams one statement at a time with a fresh `PygenM` state per statement, so cross-statement
class metadata cannot live in `PyGen.State`; it lives here and persists for the process. A class's
`ClassDef` is always lowered before any statement that instantiates it (module order), so the
registry is populated in time. -/
initialize classRegistry : IO.Ref (Std.HashMap String ClassInfo) ←
  IO.mkRef (Std.HashMap.emptyWithCapacity 16)

def registerClass (name : String) (info : ClassInfo) : PygenM Unit := do
  classRegistry.modify (·.insert name info)

def isRegisteredClass (name : String) : PygenM Bool := do
  return (← classRegistry.get).contains name

def classInfo? (name : String) : PygenM (Option ClassInfo) := do
  return (← classRegistry.get).get? name

def methodIsMutator (className method : String) : PygenM Bool := do
  match (← classRegistry.get).get? className with
  | some info => return info.mutators.contains method
  | none => return false

/-- The unique class declaring method `m`, if exactly one does (else `none`: ambiguous or unknown).
Fallback for resolving a method-call receiver's class when the receiver isn't `self`. -/
def classOfMethod? (m : String) : PygenM (Option String) := do
  let reg ← classRegistry.get
  let owners := reg.toList.filterMap fun (c, info) =>
    if info.methods.contains m then some c else none
  match owners with
  | [c] => return some c
  | _ => return none

instance : MonadEvalT PygenM TermElabM where
    monadEval := fun x => x.run' {}


initialize
  registerTraceClass `PastaLean.pygen.info
  registerTraceClass `PastaLean.pygen.debug


instance : Repr SyntaxNodeKind where
  reprPrec kind n :=
    let name : Name := kind
    Repr.reprPrec name n

instance : ToString SyntaxNodeKind where
  toString kind :=
    let name : Name := kind
    ToString.toString name

/-- Environment extension storing code generation lemmas -/
initialize pygenExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) =>
        m.insert key <| (m.getD key #[] ).push n
    initial := {}
  }

/-- Environment extension storing syntax transformation functions. -/
initialize pygenTransformExt :
    SimpleScopedEnvExtension (SyntaxNodeKind × Name) (Std.HashMap SyntaxNodeKind (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (kind, f) =>
        m.insert kind <| (m.getD kind #[]).push f
    initial := {}
  }

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `PygenM <| TSyntax kind` from a JSON object, with the matching key as part of the attribute.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := pygen) "pygen" (str,*) : attr

/--
Attribute for Lean syntax transformers that can rewrite syntax in a given category.
-/
syntax (name := pygenTransform) "pygen_transform" ident : attr

/--
Extract the keys from the `pygen` attribute syntax. Returns an array of strings.
-/
def pygenKeyM (stx : Syntax) : CoreM <| Array String := do
  match stx with
  | `(attr|pygen $x) => do
    return #[x.getString]
  | `(attr|pygen $xs,*) => do
    let keys := xs.getElems
    return keys.map (·.getString)
  | _ => throwUnsupportedSyntax

/--
Extract the syntax kind from the `pygen_transform` attribute syntax.
-/
def pygenTransformKindM (stx : Syntax) : CoreM SyntaxNodeKind := do
  match stx with
  | `(attr|pygen_transform $kind:ident) =>
    return kind.getId
  | _ => throwUnsupportedSyntax

/--
An environment extension for code generation functions. It stores the functions that can be used to generate code from JSON data. The key is a string that identifies the function, and the value is an array of names of the functions that can be used to generate code for that key.
-/
initialize registerBuiltinAttribute {
  name := `pygen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    -- Obtained from Qq.
    let expectedType : Q(Type) := q((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind))
    unless ← isDefEq declTy expectedType do
      throwError -- replace with error
        s!"pygen: {decl} has type {declTy}, but expected {expectedType}"
    let keys ← pygenKeyM stx
    trace[PastaLean.pygen.debug] m!"pygen: {decl}; keys: {keys}"
    for key in keys do
      pygenExt.add (decl, key) kind
}

/--
An environment extension for syntax transformation functions. It stores functions that can
transform generated syntax after the initial JSON-to-syntax pass.
-/
initialize registerBuiltinAttribute {
  name := `pygenTransform
  descr := "Lean syntax transformer for generated code"
  add := fun decl stx attrKind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let kind ← pygenTransformKindM stx
    let kindExpr : Q(SyntaxNodeKind) := toExpr kind
    let expectedType : Q(Type) := q((stx : TSyntax $kindExpr) → PygenM (TSyntax $kindExpr))
    unless ← isDefEq declTy expectedType do
      throwError
        s!"pygen_transform: {decl} has type {declTy}, but expected {expectedType}"
    trace[PastaLean.pygen.debug] m!"pygen_transform: {decl}; kind: {kind}"
    pygenTransformExt.add (kind, decl) attrKind
}

/-- Environment extension storing code generation lemmas -/
initialize funcMapExt :
    SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (py, lean) =>
        m.insert py lean
    initial := {}
  }

syntax nameMapEntry := ident " → " ident

elab "#map_names" "[" nms:nameMapEntry,* "]" : command => do
  for nm in nms.getElems do
    match nm with
    | `(nameMapEntry| $py → $lean) =>
      let pyName := py.getId
      let leanName := lean.getId
      funcMapExt.add (pyName, leanName)
    | _ => throwUnsupportedSyntax

def leanName (pyName: Name) : CoreM Name := do
  let leanName := (funcMapExt.getState (← getEnv)).getD pyName pyName
  return leanName

/--
Get the code generation functions for a given key. The key is a string that identifies the function. If no function is found for the key, an error is thrown.
-/
def pygenMatches (key: String) : CoreM <| Array Name := do
  let allKeys := (pygenExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fs :=
    (pygenExt.getState (← getEnv)).get? key | throwError
      s!"pygen: no function found for key '{key}' available keys are {allKeys.toList}"
  trace[PastaLean.pygen.info] m!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    trace[PastaLean.pygen.debug] m!"no function found for key {key} in {allKeys.toList}"
  return fs

/--
Get the syntax transformation functions registered for a syntax category.
-/
def pygenTransformers (kind : SyntaxNodeKind) : CoreM <| Array Name := do
  return (pygenTransformExt.getState (← getEnv)).getD kind #[]

def codeFromFunc (f: Name) (json: Json) (kind: SyntaxNodeKind)  : PygenM <| TSyntax kind := do
  let fInfo ← getConstInfo f
  let expectedType : Q(Type) := q((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind))
  unless ← isDefEq fInfo.type expectedType do
    throwError -- replace with error
      s!"pygen: {f} has type {fInfo.type}, but expected {expectedType}"
  let fn ← unsafe evalConst ((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind)) f
  fn kind json
/--
  Get the code generation function for a given key and syntax category. The key is a string that identifies the function, and the syntax category is used to disambiguate between functions that can generate different syntax categories. If no function is found for the key and syntax category, an error is thrown.
-/
def getCode (json: Json) (kind: SyntaxNodeKind) : PygenM <| TSyntax kind := do
  let .ok key := json.getObjValAs? String "node_type" | throwError
    s!"pygen: JSON object does not have a 'node_type' field or it is not a string: {json}"
  let fs ← pygenMatches key
  -- IO.eprintln s!"getting code for json: \n{json.pretty}"
  -- IO.eprintln s!"getCode: found functions '{fs}' for key '{key}' and syntax category '{kind}'" -- Debugging output
  let code? ← fs.findSomeM? (fun f => do try
    let mut code ← codeFromFunc f json kind
    let transformers ← pygenTransformers kind
    for t in transformers do
      let transformFn ← unsafe evalConst (TSyntax kind → PygenM (TSyntax kind)) t
      code ← transformFn code
    pure (some code)
  catch e =>
    throwError s!"Error in code generation function {f} for key '{key}' and syntax category '{kind}': {← e.toMessageData.toString}")
  match code? with
  | some code => return code
  | none => throwError s!"pygen: no function found for key '{key}' and syntax category '{kind}'"

def getCodeCore (json: Json) (kind: SyntaxNodeKind) (checkCode : Bool := true) : CoreM <| Except String Format := do
  try
    let code := if checkCode then getCode json kind else withoutCheck <| getCode json kind
    let codeElab := code.run' {}
    let codeMeta := codeElab.run' {} {}
    let codeCore ← codeMeta.run' {} {}
    -- A pygen may return several commands wrapped in a null node (e.g. tuple-assign
    -- re-exports or top-level state-threading folds). Pretty-print each child and
    -- join them, since `ppCategory` cannot render a raw null node.
    if kind == `command && codeCore.raw.isOfKind nullKind then
      let mut fmts : Array Format := #[]
      for arg in codeCore.raw.getArgs do
        let child : TSyntax `command := ⟨arg⟩
        let childFmt ← PrettyPrinter.ppCategory `command child
        fmts := fmts.push childFmt
      return .ok (Format.joinSep fmts.toList "\n\n")
    let fmt ← PrettyPrinter.ppCategory kind codeCore
    return .ok fmt
  catch e =>
    return .error s!"Error generating code: {← e.toMessageData.toString}"

def getCodeIO (json: Json) (kind: SyntaxNodeKind) (ctx : Core.Context) (env: Environment)
    (checkCode : Bool := true) :
  IO <| Except String Format := do
  let code := getCodeCore json kind checkCode
  let eio := code.run' ctx {env := env}
  match ← eio.toIO' with
  | .ok code =>
    return code
  | .error err =>
    return .error s!"Error generating code: {← err.toMessageData.toString}"

open Tactic
syntax (name:= pyTerm) "py_term%" term : term
@[term_elab pyTerm] def elabPyTerm : TermElab := fun stx expectedType => do
  match stx with
  | `(py_term% $json) => do
    let jsonExpr ← elabTerm json (mkConst ``Json)
    Term.synthesizeSyntheticMVarsNoPostponing
    let js ← unsafe evalExpr Json (mkConst ``Json) jsonExpr
    let termCodeM := getCode js `term
    let termCode ← termCodeM.run' {}
    TryThis.addSuggestion stx termCode
    elabTerm termCode expectedType
  | _ => throwUnsupportedSyntax

macro "py_term%" js:json : term =>
  `(py_term% json% $js)

-- #eval pygen

end PastaLean
