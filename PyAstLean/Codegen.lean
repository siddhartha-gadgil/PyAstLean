import Lean
import Qq
import PyAstLean.Basic

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `pygenerator` a Json object and a syntax category, and returns the corresponding syntax (in the monad `PygenM`) or throws an error.
-/

namespace PyGen

structure State where
  varNames : HashSet Name := HashSet.emptyWithCapacity 100
  checkExr : Bool := true
  useArrow : Bool := false
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

def isCheckEnabled : PygenM Bool := do
  return (← get).checkExr

def isUseArrowEnabled : PygenM Bool := do
  return (← get).useArrow

def hasVar (usedName : Name) : PygenM Bool := do
  return (← get).varNames.contains usedName

def addVar (usedName : Name) : PygenM Unit := do
  modify fun st => { st with varNames := st.varNames.insert usedName }

instance : MonadEvalT PygenM TermElabM where
    monadEval := fun x => x.run' {}


initialize
  registerTraceClass `pyastlean.pygen.info
  registerTraceClass `pyastlean.pygen.debug


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
    trace[pyastlean.pygen.debug] m!"pygen: {decl}; keys: {keys}"
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
    trace[pyastlean.pygen.debug] m!"pygen_transform: {decl}; kind: {kind}"
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
  trace[pyastlean.pygen.info] m!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    trace[pyastlean.pygen.debug] m!"no function found for key {key} in {allKeys.toList}"
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
  IO.eprintln s!"getting code for json: \n{json.pretty}"
  IO.eprintln s!"getCode: found functions '{fs}' for key '{key}' and syntax category '{kind}'" -- Debugging output
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

def getCodeCore (json: Json) (kind: SyntaxNodeKind) : CoreM <| Except String Format := do
  try
    let code := getCode json kind
    let codeElab := code.run' {}
    let codeMeta := codeElab.run' {} {}
    let codeCore ← codeMeta.run' {} {}
    let fmt ← PrettyPrinter.ppCategory kind codeCore
    return .ok fmt
  catch e =>
    return .error s!"Error generating code: {← e.toMessageData.toString}"

def getCodeIO (json: Json) (kind: SyntaxNodeKind) (ctx : Core.Context) (env: Environment) :
  IO <| Except String Format := do
  let code := getCodeCore json kind
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

end PyAstLean
