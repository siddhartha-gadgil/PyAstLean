import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.UseCases.FuncDef

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term
open Lean.Parser.Command

/-!
  Translates Python `class` definitions to a Lean `structure` plus namespaced method `def`s.

  * Fields (`self.x = …`, class-level `x = …`) become structure fields, types from
    `annotate_python`/parameter annotations (defaulting to `Int`).
  * `__init__` becomes the smart constructor `C.mk`, built by the same `self`-threading machinery
    as a mutator (start from `default`, apply each `self.x = …`, return `self`), so partial and
    locally-computed `__init__`s both work.
  * A non-mutating method is a pure `def C.method (self : C) … `; a mutator returns the rebuilt
    `self` (value semantics — see the module plan for the aliasing caveat).
  * Methods are emitted with fully-qualified names (`def C.method`), so `obj.method` dot-notation
    resolves without a `namespace` wrapper.
-/

/-- One structure field `name : Type [:= default]` from a `{name, annotation?, default?}` entry. -/
def classStructFieldSyntax (fieldJson : Json) :
    PygenM (TSyntax ``Lean.Parser.Command.structSimpleBinder) := do
  let .ok fname := fieldJson.getObjValAs? String "name" | throwError
    s!"Class field is missing a 'name': {fieldJson}"
  let fid := mkIdent fname.toName
  let intTy : TSyntax `term := mkIdent ``Int
  -- A field the per-variable pass marked `_real` (holds an `ℝ` value, e.g. a trained weight) types
  -- its annotation under real-context so `float`/`list[float]` → `ℝ`/`List ℝ`.
  let isRealField := (← getNumericMode) == .exact && fieldJson.getObjValAs? Bool "_real" == .ok true
  let ty : TSyntax `term ←
    match (fieldJson.getObjVal? "annotation").toOption with
    | some (.null) | none => pure intTy
    | some annJson => pure ((← withRealContext isRealField (functionArgTypeSyntax? annJson)).getD intTy)
  match (fieldJson.getObjVal? "default").toOption with
  | some (.null) | none => `(structSimpleBinder| $fid:ident : $ty)
  | some defJson =>
      let defCode ← getCode defJson `term
      `(structSimpleBinder| $fid:ident : $ty := $defCode)

/-- Build the `Id.run do` body of a `self`-threading routine (`__init__` or a mutator method):
declare a mutable `self` (the parameter for a mutator, or `default` for a constructor), lower the
body (where `self.x = …` becomes `self := { self with x := … }` — see `Core/Assign.lean`), then
`return self`. Wrapped in a lambda over `argInfos`. -/
def classSelfThreadingValue (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (classTyTerm : TSyntax `term) (bodyElems : Array Json) (selfIsParam : Bool) :
    PygenM (TSyntax `term) := withFreshVariables do
  let selfId := mkIdent `self
  addVar `self
  let selfDecl ← if selfIsParam then `(doElem| let mut $selfId:ident := $selfId:ident)
                 else `(doElem| let mut $selfId:ident : $classTyTerm := default)
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let idRun := mkIdent ``Id.run
  let core ← `($idRun do
      $selfDecl:doElem
      $[$bodyStxArray:doElem]*
      return $selfId:term)
  let mut result := core
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- If `__init__`'s body is purely straight-line `self.X = expr` (no control flow, no locals, and
no value reading `self`), return the `(field, valueJson)` pairs in order — the case that lowers to
a plain record literal (which honors structure field defaults for unassigned fields). `none`
otherwise (then the constructor threads a mutable `self` from `default`). -/
def initFieldAssignments? (bodyElems : Array Json) : Option (Array (String × Json × Bool)) := Id.run do
  let mut out := #[]
  for s in bodyElems do
    if jsonNodeType? s != some "Assign" then return none
    let some target := (s.getObjVal? "target").toOption | return none
    let some attr := selfAttrTarget? target | return none
    let some value := (s.getObjVal? "value").toOption | return none
    if jsonReferencesName value "self" then return none
    -- carry the per-field `_real` stamp so a real field's initial value is lowered in real-context
    out := out.push (attr, value, s.getObjValAs? Bool "_real" == .ok true)
  return some out

/-- The smart constructor `C.new` from `__init__`. A straight-line `__init__` becomes a record
literal `{ field := … }` (so unassigned fields take their structure defaults); anything else threads
a mutable `self` from `default`. Named `new` (not `mk`) to avoid clashing with the structure's
auto-generated `C.mk` field constructor. -/
def classInitConstructor (className : String) (initJson : Json) (hasRealField : Bool) :
    PygenM (TSyntax `command) := do
  let mkIdentC := mkIdent (Name.mkStr className.toName "new")
  let classTy : TSyntax `term := mkIdent className.toName
  let argInfos := (← functionArgInfos initJson).drop 1   -- drop the leading `self`
  let bodyElems ← functionBodyElems initJson
  let valueStx ← withFreshVariables do
    match initFieldAssignments? bodyElems with
    | some pairs =>
        let fields ← pairs.mapM fun (attr, valJson, isReal) => do
          -- a real field's initial value is lowered in real-context so it matches the `ℝ` field type
          let v ← if isReal then withRealContext true (getCode valJson `term) else getCode valJson `term
          `(Lean.Parser.Term.structInstField| $(mkIdent attr.toName):ident := $v)
        let mut result : TSyntax `term ← `(({ $fields:structInstField,* } : $classTy))
        for (argIdent, ty?) in argInfos.toList.reverse do
          result ← match ty? with
            | some ty => `(fun ($argIdent : $ty) ↦ $result)
            | none => `(fun $argIdent ↦ $result)
        pure result
    | none =>
        withCurrentClass className [] do
          classSelfThreadingValue argInfos classTy bodyElems (selfIsParam := false)
  -- A constructor building a struct with `ℝ` fields is `noncomputable`.
  let mkDef : TSyntax `term → PygenM (TSyntax `command) := fun ty =>
    if hasRealField then `(command| noncomputable def $mkIdentC : $ty := $valueStx)
    else `(command| def $mkIdentC : $ty := $valueStx)
  match ← functionArrowTypeSyntax? argInfos classTy with
  | some fullTy => mkDef fullTy
  | none => if hasRealField then `(command| noncomputable def $mkIdentC := $valueStx)
            else `(command| def $mkIdentC := $valueStx)

/-- One method `def C.method …`. A getter is a pure `functionValueSyntax`; a mutator returns the
rebuilt `self`. Static/class methods drop the leading `self`/`cls`. -/
def classMethodDef (className : String) (info : ClassInfo) (m : Json) : PygenM (Array (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | throwError
    s!"Class method is missing a 'name': {m}"
  let defIdent := mkIdent (Name.mkStr className.toName mName)
  let classTy : TSyntax `term := mkIdent className.toName
  let allArgInfos ← functionArgInfos m
  let bodyElems ← functionBodyElems m
  let isStatic := info.staticmethods.contains mName
  let isClassM := info.classmethods.contains mName
  let isMutator := info.mutators.contains mName && !isStatic && !isClassM
  let argInfos : Array (TSyntax `ident × Option (TSyntax `term)) :=
    if isStatic then allArgInfos
    else if isClassM then allArgInfos.drop 1
    else #[(mkIdent `self, some classTy)] ++ allArgInfos.drop 1
  let valueStx ← withCurrentClass className info.mutators do
    if isMutator then
      classSelfThreadingValue argInfos classTy bodyElems (selfIsParam := true)
    else
      functionValueSyntax argInfos bodyElems
  -- A method the per-variable pass stamped `_real_fn` (produces/handles an `ℝ` transcendental)
  -- must be `noncomputable` in exact mode, exactly like a free function.
  let nc := (← getNumericMode) == .exact && m.getObjValAs? Bool "_real_fn" == .ok true
  let cmd ← if nc then `(command| noncomputable def $defIdent := $valueStx)
            else `(command| def $defIdent := $valueStx)
  let finalCmd ← applyPrivacy mName cmd
  -- Prove-version (exact) methods get `@[simp]` (and `taste_ingr` when a pure, computable, non-
  -- `assert` value method), so `taste?` can unfold them — mirroring free functions in `FuncDef`.
  -- Never the `'rn` twin (approx mode is skipped). Methods are emitted as plain `def`s, not
  -- `partial`, so there's no recursive-`@[simp]` hazard.
  if (← getNumericMode) == .exact then
    let isEffectful := bodyNeedsExceptionMonad bodyElems || bodyNeedsIOMonad bodyElems
    let hasAssert := bodyElems.any (jsonNodeType? · == some "Assert")
    let attrCmd ← if !isEffectful && !hasAssert && !nc
      then `(command| attribute [simp, taste_ingr] $defIdent)
      else `(command| attribute [simp] $defIdent)
    return #[finalCmd, attrCmd]
  else
    return #[finalCmd]

/-- A `__repr__`/`__str__` method becomes a `PyPrintable` instance, so `print(obj)` / `str(obj)`
use it (overriding the `deriving Repr` fallback). -/
def classPrintableInstance (className : String) (m : Json) : PygenM (TSyntax `command) := do
  let classTy : TSyntax `term := mkIdent className.toName
  let bodyElems ← functionBodyElems m
  let lam ← withCurrentClass className [] do
    functionValueSyntax #[(mkIdent `self, some classTy)] bodyElems
  let printableC ← `($(mkIdent ``PastaLean.PyPrintable) $classTy)
  `(command| instance : $printableC where pyStringify := $lam)

/-- Operator dunders become the runtime operator typeclass instances the generated code dispatches
through: `__add__`→`PyHAdd` (used by `+ₚ`), `__sub__`→`PyHSub`, `__mul__`→`PyHMul`, `__eq__`→`BEq`
(used by `==`). Returns `none` for a non-operator method name. -/
def classDunderInstance? (className : String) (m : Json) : PygenM (Option (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | return none
  let classTy : TSyntax `term := mkIdent className.toName
  let bodyElems ← functionBodyElems m
  let argInfos := #[(mkIdent `self, some classTy)] ++ (← functionArgInfos m).drop 1
  let lam ← withCurrentClass className [] do functionValueSyntax argInfos bodyElems
  match mName with
  | "__add__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHAdd) $classTy $classTy $classTy where hAdd := $lam)
  | "__sub__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHSub) $classTy $classTy $classTy where hSub := $lam)
  | "__mul__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHMul) $classTy $classTy $classTy where hMul := $lam)
  | "__eq__"  => some <$> `(command| instance : BEq $classTy where beq := $lam)
  | _ => return none

@[pygen "ClassDef"]
def classDefSyntax : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `command, json => do
      let .ok rawName := json.getObjValAs? String "name" | throwError
        s!"ClassDef node is missing a 'name': {json}"
      -- Run-twin: the class is emitted as `CNN'rn`; its methods/constructor follow (`CNN'rn.new`,
      -- `CNN'rn.forward`) since they are built from this name, and references to `CNN` are suffixed
      -- by the Name pygen + the constructor/method call sites.
      let name ← withRunSuffix rawName
      let nameId := mkIdent name.toName
      let .ok fields := json.getObjValAs? (Array Json) "fields" | throwError
        s!"ClassDef node is missing a 'fields' array: {json}"
      let .ok methods := json.getObjValAs? (Array Json) "methods" | throwError
        s!"ClassDef node is missing a 'methods' array: {json}"
      let mutators := (json.getObjValAs? (Array String) "mutators").toOption.getD #[]
      let staticmethods := (json.getObjValAs? (Array String) "staticmethods").toOption.getD #[]
      let classmethods := (json.getObjValAs? (Array String) "classmethods").toOption.getD #[]
      let bases := (json.getObjValAs? (Array Json) "bases").toOption.getD #[]

      -- Record class metadata so later top-level statements can dispatch instantiation/methods.
      let methodNames := methods.filterMap (·.getObjValAs? String "name" |>.toOption)
      let info : ClassInfo := {
        methods := methodNames.toList
        mutators := mutators.toList
        staticmethods := staticmethods.toList
        classmethods := classmethods.toList }
      registerClass name info

      let hasEq := methodNames.contains "__eq__"
      -- A class with an `ℝ` field (exact mode) can't derive a COMPUTABLE `BEq` (`Real.decidableEq`
      -- is noncomputable), and its constructor builds an `ℝ` struct → `noncomputable`.
      let hasRealField := (← getNumericMode) == .exact
        && fields.any (fun f => f.getObjValAs? Bool "_real" == .ok true)
      -- The structure, carrying the class docstring as its `/-- … -/` doc comment (when present)
      -- and `extends Base` for a single base. `BEq` is derived separately below unless the class
      -- supplies `__eq__` (which becomes a custom `BEq` instance).
      let fieldBinders ← fields.mapM classStructFieldSyntax
      let baseId? : Option (TSyntax `ident) ←
        match bases[0]? with
        | some baseJson =>
            match baseJson.getObjValAs? String "id" with
            | .ok bid => pure (some (mkIdent bid.toName))
            | _ => throwError s!"Class base is not a simple Name: {baseJson}"
        | none => pure none
      -- A leading class docstring → `/-- … -/`. `-/` inside the text is defanged so it can't close
      -- the comment early.
      let docStx? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
        match (json.getObjValAs? String "docstring").toOption with
        | some text =>
            let body := (text.trimAscii).toString.replace "-/" "- /"
            some ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (body ++ " -/")]⟩
        | none => none
      let structCmd ← match docStx?, baseId? with
        | some doc, some baseId =>
            `(command| $doc:docComment structure $nameId:ident extends $baseId:ident where
                $[$fieldBinders]* deriving Inhabited)
        | some doc, none =>
            `(command| $doc:docComment structure $nameId:ident where
                $[$fieldBinders]* deriving Inhabited)
        | none, some baseId =>
            `(command| structure $nameId:ident extends $baseId:ident where
                $[$fieldBinders]* deriving Inhabited)
        | none, none =>
            `(command| structure $nameId:ident where
                $[$fieldBinders]* deriving Inhabited)

      let mut members : Array (TSyntax `command) := #[structCmd]
      -- A class with an `ℝ` field can't derive a computable `BEq`/`Repr` (`Real.decidableEq` is
      -- noncomputable; `Real`'s only `Repr` is `unsafe`), and the `prove` version is never compared
      -- or printed — so skip both for real-field classes. Otherwise derive them as usual.
      unless hasEq || hasRealField do
        members := members.push (← `(command| deriving instance BEq for $nameId:ident))
      unless hasRealField do
        members := members.push (← `(command| deriving instance Repr for $nameId:ident))

      -- Constructor (from `__init__`), operator/printable dunders, and the remaining methods.
      let mut hasInit := false
      for m in methods do
        let .ok mName := m.getObjValAs? String "name" | throwError
          s!"Class method is missing a 'name': {m}"
        if mName == "__init__" then
          hasInit := true
          members := members.push (← classInitConstructor name m hasRealField)
        else if mName == "__str__" || (mName == "__repr__" && !methodNames.contains "__str__") then
          -- Prefer `__str__` for `pyStringify` when both are defined (Python `str()`/`print`).
          members := members.push (← classPrintableInstance name m)
        else if mName == "__repr__" then
          pure ()  -- shadowed by `__str__`

        else if let some inst ← classDunderInstance? name m then
          members := members.push inst
        else
          members := members ++ (← classMethodDef name info m)
      -- No `__init__`: `C()` builds an all-defaults instance (fields use their declared defaults).
      unless hasInit do
        members := members.push (← `(command| def $(mkIdent (Name.mkStr name.toName "new")) : $nameId := default))
      return ⟨mkNullNode (members.map (·.raw))⟩
  | kind, _ => throwError
      s!"ClassDef is only supported at command (top-level) position, not '{kind}'."

end PastaLean
