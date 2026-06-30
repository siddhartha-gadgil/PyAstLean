import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Core.Assign
import PastaLean.PyGens.UseCases.ControlFlow
import PastaLean.PyGens.UseCases.ListComp
import PastaLean.PyGens.UseCases.Match
import PastaLean.PyGens.UseCases.Exceptions
import PastaLean.PyVerify.AssertTactic
import PastaLean.PyVerify.Contracts

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term
open Std.Do  -- the `⦃⌜…⌝⦄ … ⦃⇓ … => …⦄` Hoare-triple notation used by the `while` (`pyWhile`) spec

/-!
  Translates Python function definitions and the remaining module-level glue.
  Feature-specific statement lowering lives in the smaller files under `PyGens/`.
-/

/-- Map a simple Python annotation JSON node to a Lean type term when we know a direct runtime type. -/
partial def functionArgTypeSyntax? (annotationJson : Json) : PygenM (Option (TSyntax `term)) := do
  let .ok nodeType := annotationJson.getObjValAs? String "node_type" | throwError
    s!"Function argument annotation is missing a 'node_type' field: {annotationJson}"
  match nodeType with
  | "Name" =>
      let .ok id := annotationJson.getObjValAs? String "id" | throwError
        s!"Function argument annotation is missing an 'id' field: {annotationJson}"
      match id with
      | "int" | "Int" => return some (mkIdent ``Int)
      | "bool" | "Bool" => return some (mkIdent ``Bool)
      | "str" | "String" => return some (mkIdent ``String)
      -- `float` → exact `ℚ` (default), `ℝ` under real-context (a real-marked param, set in
      -- `functionArgInfos`), or `Float` (`--mode run`). Real-context preserves container shape:
      -- `list[list[float]]` → `List (List ℝ)`, a scalar `float` → `ℝ`.
      | "float" | "Float" =>
          match ← getNumericMode with
          | .exact => return some (mkIdent (if (← getRealContext) then ``Real else ``Rat))
          | .approx => return some (mkIdent ``Float)
      | "Any" => return none -- let Lean handle the type inference for now
      | _ => return none
  | "Subscript" =>
      let .ok valueJson := annotationJson.getObjValAs? Json "value" | throwError
        s!"Function argument subscript annotation is missing a 'value' field: {annotationJson}"
      let .ok sliceJson := annotationJson.getObjValAs? Json "slice" | throwError
        s!"Function argument subscript annotation is missing a 'slice' field: {annotationJson}"
      match valueJson.getObjValAs? String "node_type", valueJson.getObjValAs? String "id" with
      | .ok "Name", .ok "list" | .ok "Name", .ok "List" =>
          match ← functionArgTypeSyntax? sliceJson with
          | some elemTy => return some (← `(List $elemTy))
          | none => return none
      | .ok "Name", .ok "dict" | .ok "Name", .ok "Dict" =>
          match sliceJson.getObjValAs? String "node_type" with
          | .ok "Tuple" =>
              let .ok elts := sliceJson.getObjValAs? (Array Json) "elts" | throwError
                s!"Dictionary annotation tuple is missing an 'elts' field: {sliceJson}"
              match elts[0]?, elts[1]? with
              | some keyJson, some valJson =>
                  match ← functionArgTypeSyntax? keyJson, ← functionArgTypeSyntax? valJson with
                  | some keyTy, some valTy => return some (← `(Std.HashMap $keyTy $valTy))
                  | _, _ => return none
              | _, _ => return none
          | _ => return none
      | _, _ => return none
  | _ => return none

/-- Read Python function parameters as Lean idents plus any simple type annotations we can preserve. -/
def functionArgInfos (json : Json) : PygenM (Array (TSyntax `ident × Option (TSyntax `term))) := do
  let .ok args := json.getObjVal? "args" | throwError
    s!"FuncDef node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
    s!"FuncDef args does not have an 'args' field or it is not a JSON value: {args}"
  let mut argInfos := #[]
  for arg in argsArray do
    let .ok argName := arg.getObjValAs? String "arg" | throwError
      s!"FuncDef argument does not have an 'arg' field or it is not a string: {arg}"
    -- A parameter the per-variable real-flow pass stamped `_real` receives an `ℝ` value at some
    -- call site → ascribe `ℝ` (exact mode), overriding the annotation. Everything else stays `ℚ`.
    let isRealParam := (← getNumericMode) == .exact && arg.getObjValAs? Bool "_real" == .ok true
    let ty? ← match jsonFieldOption arg "annotation" with
      -- Real-marked params lower their annotation under real-context so `float` → `ℝ` while the
      -- container shape is preserved (`list[list[float]]` → `List (List ℝ)`, scalar → `ℝ`).
      | some annotationJson => withRealContext isRealParam (functionArgTypeSyntax? annotationJson)
      -- No annotation but real: ascribe a bare scalar `ℝ` (best effort).
      | none => if isRealParam then pure (some (← `(Real))) else pure none
    argInfos := argInfos.push (mkIdent argName.toName, ty?)
  return argInfos

def functionBodyElems (json : Json) : PygenM (Array Json) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"FuncDef node does not have a 'body' field or it is not a JSON value: {json}"
  return bodyElems

/-- Whether the JSON references a library member that lowers to a `noncomputable` `ℝ`
transcendental (`math.exp`, `math.sqrt`, …). Used to mark a generated `def` as `noncomputable`
in exact mode — Lean rejects an unmarked `def` whose body transitively uses `Real.*`. -/
partial def jsonUsesRealTranscendental (json : Json) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
    | .ok m, .ok mem => (Libraries.pythonLibraryMapReal? m mem).isSome
    | _, _ => false
  if directMatch then true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesRealTranscendental
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesRealTranscendental value)
    | _ => false

/-- Whether any body statement uses an `ℝ` transcendental, but only in exact numeric mode
(in `--mode run` the transcendentals stay computable `Float`, so no `noncomputable` is needed). -/
def bodyNeedsNoncomputable (bodyElems : Array Json) : PygenM Bool := do
  if (← getNumericMode) == .exact then
    return bodyElems.any jsonUsesRealTranscendental
  else
    return false

/-- Whether a type annotation mentions `float` anywhere (`float`, `list[float]`, `dict[_,float]`). -/
partial def annotationMentionsFloat (json : Json) : Bool :=
  if json.getObjValAs? String "node_type" == .ok "Name" then
    json.getObjValAs? String "id" == .ok "float" || json.getObjValAs? String "id" == .ok "Float"
  else
    (match (json.getObjVal? "slice").toOption with | some s => annotationMentionsFloat s | none => false)
    || (match (json.getObjValAs? (Array Json) "elts").toOption with
        | some es => es.any annotationMentionsFloat | none => false)

/-- Read a Python function return annotation when it maps cleanly to a Lean runtime type. -/
def functionReturnTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match jsonFieldOption json "returns" with
  | some returnJson =>
      -- In exact mode a `float`-involving return is left UNASCRIBED so Lean infers `ℚ` (a rational
      -- function) or `ℝ` (a transcendental one); a fixed `ℚ` would clash with an `ℝ` body.
      if (← getNumericMode) == .exact && annotationMentionsFloat returnJson then
        pure none
      else
        functionArgTypeSyntax? returnJson
  | none => pure none

/-- Check whether a JSON subtree references a given variable name. -/
partial def jsonReferencesName (json : Json) (target : String) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
    | .ok "Name", .ok id => id == target
    | _, _ => false
  if directMatch then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonReferencesName elem target)
    | .obj fields => fields.toList.any (fun (_, value) => jsonReferencesName value target)
    | _ => false

/-- Does assigning to this target node mutate the variable `name`? Covers a bare `Name`, tuple/
list unpacking, `Starred`, and a `Subscript`/`Attribute` whose base (recursively) is `name`
(`a[i] = …` reassigns the immutable-value container `a`, so it mutates `a`). -/
partial def assignTargetMutatesName (target : Json) (name : String) : Bool :=
  match target.getObjValAs? String "node_type" with
  | .ok "Name" => target.getObjValAs? String "id" == .ok name
  | .ok "Tuple" | .ok "List" =>
      match target.getObjValAs? (Array Json) "elts" with
      | .ok elts => elts.any (fun e => assignTargetMutatesName e name)
      | _ => false
  | .ok "Starred" | .ok "Subscript" | .ok "Attribute" =>
      (target.getObjVal? "value").toOption.any (fun v => assignTargetMutatesName v name)
  | _ => false

/-- Python list/set/dict methods that mutate their receiver in place. Codegen lowers each as a
reassignment of the (immutable-value) receiver, so a parameter used as the receiver of one of
these must be shadowed by `let mut`. Over-inclusion is harmless (an unused shadow). -/
def inPlaceMutatingMethods : List String :=
  [ "append", "extend", "insert", "remove", "pop", "clear", "sort", "reverse",
    "add", "discard", "update", "setdefault", "popitem",
    "intersection_update", "difference_update", "symmetric_difference_update",
    "appendleft", "popleft", "appendright" ]

/-- Is `name` mutated (an `=`, augmented `op=`, annotated assignment, or `for` target — including
unpacking and subscript-assignment) anywhere in this subtree, without descending into a nested
function/lambda/class scope (which rebinds the name in a separate scope)? Used to decide which
function parameters must be shadowed by `let mut` so the monadic body can reassign them. -/
partial def jsonMutatesName (json : Json) (name : String) : Bool :=
  match json with
  | .arr elems => elems.toList.any (fun e => jsonMutatesName e name)
  | .obj fields =>
      match json.getObjValAs? String "node_type" with
      | .ok "FunctionDef" | .ok "AsyncFunctionDef" | .ok "Lambda" | .ok "ClassDef" => false
      | nodeType =>
          let mutatedHere :=
            match nodeType with
            | .ok "Assign" | .ok "AugAssign" | .ok "AnnAssign" | .ok "For" =>
                (json.getObjVal? "target").toOption.any (fun t => assignTargetMutatesName t name)
            | .ok "Delete" =>
                -- `del name[i]` rebuilds and reassigns the container, so it mutates `name`.
                match (json.getObjVal? "targets").toOption.bind (·.getArr?.toOption) with
                | some targets => targets.any (fun t => assignTargetMutatesName t name)
                | none => false
            | .ok "Call" =>
                -- An in-place mutating method (`name.append(x)`, `name.add(x)`, …) is lowered as a
                -- reassignment of the receiver, so it mutates `name`.
                match (json.getObjVal? "func").toOption with
                | some funcJson =>
                    funcJson.getObjValAs? String "node_type" == .ok "Attribute"
                      && (match funcJson.getObjValAs? String "attr" with
                          | .ok m => inPlaceMutatingMethods.contains m
                          | _ => false)
                      && (funcJson.getObjVal? "value").toOption.any
                          (fun recv => assignTargetMutatesName recv name)
                | none => false
            | _ => false
          mutatedHere || fields.toList.any (fun (_, v) => jsonMutatesName v name)
  | _ => false

/-- Build the Lean value for a Python function body, using a pure term when possible and
falling back to `do` notation for effectful bodies. This helper is reused for top-level
definitions, nested local functions, and `Head_FunctionDef` threading.

The body is lowered against a fresh variable set (`withFreshVariables`) so locals declared
inside a nested function do not leak into the enclosing scope's `let`/`let mut` tracking — a
leak would otherwise cause a later same-named outer assignment to be emitted as a reassignment
of a variable that was never declared `let mut`. -/
def functionValueSyntax (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (bodyElems : Array Json) :
    PygenM (TSyntax `term) := withFreshVariables do
  let usesExceptions := bodyNeedsExceptionMonad bodyElems
  let usesIO := !usesExceptions && bodyNeedsIOMonad bodyElems
  let mkLambda (body : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut result := body
    for (argIdent, ty?) in argInfos.toList.reverse do
      result ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $result)
        | none => `(fun $argIdent ↦ $result)
    pure result
  -- A Lean function parameter is an immutable binder, but Python lets a body reassign or
  -- augment its parameters (`i -= 1`, `a[k] = v`). For each mutated parameter, register it and
  -- emit a `let mut p := p` shadow at the top of the (monadic) body, then reassignments resolve
  -- against the mutable shadow. Pure bodies never mutate, so this prelude is empty for them.
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  if usesExceptions then
    let bodyStxArray ← monadicFunctionBodySyntax bodyElems
    let exceptIdent := mkIdent ``PastaLean.PyExcept
    let exceptBody ← `(((do
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*) : $exceptIdent _))
    if argInfos.isEmpty then
      pure exceptBody
    else
      mkLambda exceptBody
  else if usesIO then
    let bodyStxArray ← monadicFunctionBodySyntax bodyElems
    let ioIdent := mkIdent ``IO
    let ioBody ← `(((do
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*) : $ioIdent _))
    if argInfos.isEmpty then
      pure ioBody
    else
      mkLambda ioBody
  else
    try
      let bodyStx ← pureFunctionBodySyntax bodyElems
      if argInfos.isEmpty then
        pure bodyStx
      else
        mkLambda bodyStx
    catch e =>
      IO.eprintln s!"Could not generate pure function term: {← e.toMessageData.toString}"
      let bodyStxArray ← monadicFunctionBodySyntax bodyElems
      let idRunIdent := mkIdent ``Id.run
      if argInfos.isEmpty then
        `($idRunIdent do
            $[$paramPrelude:doElem]*
            $[$bodyStxArray:doElem]*)
      else
        mkLambda (← `($idRunIdent do
            $[$paramPrelude:doElem]*
            $[$bodyStxArray:doElem]*))

/-- Build a lambda-wrapped monadic body term without adding an inner effect cast. -/
def functionMonadicValueNoCast (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let mut result ← `(do
    $[$bodyStxArray:doElem]*)
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- Build a function type like `A → B → IO _` when every argument type is known. -/
def functionArrowTypeSyntax? (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (codomain : TSyntax `term) : PygenM (Option (TSyntax `term)) := do
  let mut result := codomain
  for (_, ty?) in argInfos.toList.reverse do
    match ty? with
    | some ty =>
        result ← `($ty → $result)
    | none =>
        return none
  return some result

/--
For top-level effectful defs, prefer putting the effect in the signature instead of on
the body cast when the argument types are known.
-/
def functionCommandWithEffectSignature? (nameIdent : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (json : Json)
    (noncomp : Bool := false) :
    PygenM (Option (TSyntax `command)) := do
  let bodyElems ← functionBodyElems json
  let returnTy? ← functionReturnTypeSyntax? json
  let mkDef : TSyntax `term → TSyntax `term → PygenM (TSyntax `command) := fun fullTy valueStx =>
    if noncomp then `(command| noncomputable def $nameIdent : $fullTy := $valueStx)
    else `(command| def $nameIdent : $fullTy := $valueStx)
  -- Exceptions take precedence over `IO`: `PyExcept` already layers `ExceptT` over `IO`, so a body
  -- that both prints and raises must be typed `PyExcept` (not `IO`), or the `try`/`catch` runs in
  -- raw `IO` and the caught value is `IO.Error` instead of `PyException`. Mirrors the body-lowering
  -- precedence in `functionDefSyntax`.
  if bodyNeedsExceptionMonad bodyElems then
    match returnTy? with
    | none => return none
    | some retTy =>
        let exceptIdent := mkIdent ``PastaLean.PyExcept
        let codomain ← `($exceptIdent $retTy)
        match ← functionArrowTypeSyntax? argInfos codomain with
        | some fullTy =>
            let valueStx ← functionMonadicValueNoCast argInfos bodyElems
            return some (← mkDef fullTy valueStx)
        | none =>
            return none
  else if bodyNeedsIOMonad bodyElems then
    match returnTy? with
    | none => return none
    | some retTy =>
        let ioIdent := mkIdent ``IO
        let codomain ← `($ioIdent $retTy)
        match ← functionArrowTypeSyntax? argInfos codomain with
        | some fullTy =>
            let valueStx ← functionMonadicValueNoCast argInfos bodyElems
            return some (← mkDef fullTy valueStx)
        | none =>
            return none
  else
    return none

/-- A single theorem-shaped obligation → `(hypotheses, conclusion-test)`. A bare `assert C` gives
`(#[], C)`; `if H: assert C` (no `else`, body a lone assert) gives the guard's conjuncts and `C` (a
conjunction `H1 and H2` splits into separate hypotheses, so the prover gets named hyps). `none`
otherwise. This is the per-statement half of `theoremShape?`; add new obligation forms here. -/
def obligationShape? (stmt : Json) : Option (Array Json × Json) :=
  match jsonNodeType? stmt with
  | some "Assert" => (stmt.getObjValAs? Json "test").toOption.map (fun t => (#[], t))
  | some "If" =>
      let isSubst := fun (s : Json) =>
        jsonNodeType? s != some "Comment" && jsonNodeType? s != some "DocString"
      let body := ((stmt.getObjValAs? (Array Json) "body").toOption.getD #[]).filter isSubst
      let orelse := (stmt.getObjValAs? (Array Json) "orelse").toOption.getD #[]
      if orelse.isEmpty && body.size == 1 && jsonNodeType? body[0]! == some "Assert" then
        match stmt.getObjValAs? Json "test", body[0]!.getObjValAs? Json "test" with
        | .ok hyp, .ok concl =>
            let hyps :=
              if jsonNodeType? hyp == some "BoolOp" && hyp.getObjValAs? String "op" == .ok "and" then
                (hyp.getObjValAs? (Array Json) "values").toOption.getD #[hyp]
              else #[hyp]
            some (hyps, concl)
        | _, _ => none
      else none
  | _ => none

/-- The promotable theorem shape of a *pure* function body: zero or more pure `let`-bindings (fresh
distinct simple names — no reassignment or parameter mutation) followed by exactly ONE obligation
(`obligationShape?`). Returns `(lets, hypotheses, conclusion)`, or `none` when the body is monadic
(IO / `raise` / `try`), has a loop / mutation / early return, or isn't `let`s-then-one-obligation.
Single source of truth for assert→theorem promotion: monadic bodies can never match, since they
carry an IO/except effect or a non-`Assign` statement before the obligation. -/
def theoremShape? (paramNames : Array String) (body : Array Json) (substantive : Array Json) :
    Option (Array Json × Array Json × Json) := Id.run do
  if substantive.isEmpty then return none
  if bodyNeedsIOMonad body || bodyNeedsExceptionMonad body then return none
  let lets := substantive.pop
  let last := substantive[substantive.size - 1]!
  let mut seen : Array String := #[]
  for s in lets do
    if jsonNodeType? s != some "Assign" then return none
    let .ok target := s.getObjVal? "target" | return none
    if jsonNodeType? target != some "Name" then return none
    let .ok tname := target.getObjValAs? String "id" | return none
    if paramNames.contains tname || seen.contains tname then return none
    seen := seen.push tname
  match obligationShape? last with
  | some (hyps, concl) => return some (lets, hyps, concl)
  | none => return none

/-! ### `while`-loop verification via `pyWhile` -/

/-- Projection of the `idx`-th component (0-based) of an `n`-tuple `base`: `base.1`, `base.2.1`, …, with
the last component being the full `.2`-chain (Lean tuples are right-nested). `n ≤ 1` → `base` itself. -/
partial def whileTupleProj (base : TSyntax `term) (idx n : Nat) : PygenM (TSyntax `term) := do
  if n ≤ 1 then return base
  let mut t := base
  for _ in [0:idx] do t ← `(($t).2)
  if idx == n - 1 then return t else `(($t).1)

/-- Right-nested tuple `(e₀, e₁, …, e_{k-1})` from `elems` (matching `whileTupleProj`). -/
def whileNestedTuple (elems : Array (TSyntax `term)) : PygenM (TSyntax `term) := do
  if elems.isEmpty then return (← `(()))
  let mut acc := elems[elems.size - 1]!
  for i in [0:elems.size - 1] do
    let e := elems[elems.size - 2 - i]!
    acc ← `(($e, $acc))
  return acc

/-- `fun s => let v₁ := s.<p₁>; … ; <inner>` — a lambda over the loop state tuple that binds each state
variable name to its projection, so `inner` (built by `getCode` over the original JSON) refers to the
state variables by name. `inner` is run with those names registered. -/
def whileStateLambda (stateVars : Array String) (inner : PygenM (TSyntax `term)) :
    PygenM (TSyntax `term) := withFreshVariables do
  for v in stateVars do addVar v.toName
  let innerStx ← inner
  let s := mkIdent `s
  let n := stateVars.size
  let mut body := innerStx
  for i in [0:n] do
    let idx := n - 1 - i
    let proj ← whileTupleProj s idx n
    body ← `(let $(mkIdent stateVars[idx]!.toName):ident := $proj; $body)
  `(fun $s => $body)

/-- Emit a `while`-shaped contracted function as a `pyWhile` verification def plus its `@[spec]`
Hoare-triple theorem, discharged by `pyWhile_correct` (init/step/exit left to `taste?`). Returns the
two commands. Exact mode only; the runnable `'rn` twin takes the ordinary `while` path. -/
def buildWhileFunction (name : String) (json : Json) (sh : WhileShape) :
    PygenM (Array (TSyntax `command)) := do
  let nameIdent := mkIdent name.toName
  let argInfos ← functionArgInfos json
  let stateVars := sh.stateVars
  let n := stateVars.size
  -- The three combinator lambdas (each captures the function parameters freely).
  let cLam ← whileStateLambda stateVars
    (do truthyConditionTerm sh.test (← withPropCondition true (getCode sh.test `term)))
  let muLam ← whileStateLambda stateVars
    (do let d ← getCode sh.decreases `term; `(($d : Int).toNat))
  let bodyLam ← whileStateLambda stateVars (do
    let elems : Array (TSyntax `term) := stateVars.map (fun v => ⟨(mkIdent v.toName).raw⟩)
    let mut b ← whileNestedTuple elems
    for assign in sh.bodyAssigns.reverse do
      let .ok target := assign.getObjVal? "target" | throwError "pyWhile: body assign without target"
      let .ok tname := target.getObjValAs? String "id" | throwError "pyWhile: body assign target not a Name"
      let .ok valJson := assign.getObjVal? "value" | throwError "pyWhile: body assign without value"
      let valStx ← getCode valJson `term
      b ← `(let $(mkIdent tname.toName):ident := $valStx; $b)
    pure b)
  -- Initial state tuple s₀.
  let s0Elems ← sh.inits.mapM (fun e => getCode e `term)
  let s0 ← whileNestedTuple s0Elems
  let pyWhileCall ← `(PastaLean.pyWhile $muLam $cLam $bodyLam $s0)
  -- The def: `fun params ↦ let sf := pyWhile …; let vᵢ := sf.<pᵢ>; <retExpr>`.
  let defValue ← withFreshVariables do
    for v in stateVars do addVar v.toName
    let retStx ← getCode sh.retExpr `term
    let sf := mkIdent `__py_sf
    let mut b := retStx
    for i in [0:n] do
      let idx := n - 1 - i
      let proj ← whileTupleProj sf idx n
      b ← `(let $(mkIdent stateVars[idx]!.toName):ident := $proj; $b)
    b ← `(let $sf := $pyWhileCall; $b)
    -- The spec is a Hoare triple `⦃P⦄ fn args ⦃⇓ r => Q⦄`, so `fn args` must be a *monadic* value.
    -- Wrap the pure result in `Id` (mirrors the `for`-loop path's `(do … : Id _)`); the `'rn` twin
    -- keeps the ordinary runnable form.
    b ← `((pure $b : Id _))
    let mut v := b
    for (argIdent, ty?) in argInfos.reverse do
      v ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $v)
        | none => `(fun $argIdent ↦ $v)
    pure v
  let finalDef ← applyPrivacy name (← `(command| def $nameIdent := $defValue))
  -- The spec theorem.
  let preProps ← sh.requires.mapM (fun r => withPropCondition true (getCode r `term))
  let pre ← conjoin preProps
  let rId := mkIdent `__py_r
  let postProps ← sh.ensures.mapM
    (fun e => withPropCondition true (getCode (substResultWith (nameJson "__py_r") e) `term))
  let post ← conjoin postProps
  -- `I` and `Q` lambdas over the state tuple (`Q` uses `Result() := retExpr`).
  let iLam ← whileStateLambda stateVars
    (do conjoin (← sh.invariants.mapM (fun inv => withPropCondition true (getCode inv `term))))
  let qLam ← whileStateLambda stateVars
    (do conjoin (← sh.ensures.mapM
      (fun e => withPropCondition true (getCode (substResultWith sh.retExpr e) `term))))
  let paramIdents := argInfos.map (·.1)
  let nameLemma ← `(Lean.Parser.Tactic.simpLemma| $nameIdent:term)
  -- Each `pyWhile_correct` side goal (init `I s₀`, step `I(body) ∧ μ' < μ`, exit `Q`) is a conjunction
  -- mixing nonlinear (`nlinarith`) and `.toNat`-measure (`omega`) facts, which no single closer handles.
  -- So: introduce, simp with the lambda β/ζ-reductions, split the conjunction (`and_intros`), then run a
  -- closer portfolio per leaf. (`intros` covers `I s₀`, which has no binders.)
  let oblTac ← `(tactic|
    intros <;> simp_all (config := { zetaDelta := true }) <;> and_intros <;>
      first | omega | nlinarith | positivity | grind | simp_all)
  let thmCmd ← `(command| @[spec] theorem $(mkIdent (name ++ "_spec").toName) :
      ⦃⌜$pre⌝⦄ $nameIdent $paramIdents* ⦃⇓ $rId => ⌜$post⌝⦄ := by
        mvcgen [$nameLemma]
        · exact PastaLean.pyWhile_correct (I := $iLam) (Q := $qLam) $muLam $cLam $bodyLam $s0
            (by $oblTac:tactic) (by $oblTac:tactic) (by $oblTac:tactic))
  return #[finalDef, thmCmd]

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok rawName := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        -- Lean reserves the top-level name `main` for the program entry point and requires it to
        -- have type `IO (UInt32 | Unit | PUnit)`. A Python function literally named `main` that is
        -- NOT the `__main__` entry point would emit `def main := …` and be rejected. The Python
        -- pre-pass already renames `main` → `main'` whenever a `__main__` guard exists (so the guard
        -- owns the entry point); therefore any `FunctionDef` that still reaches here named `main`
        -- is a plain helper with no guard, and must yield the reserved name to stay compilable.
        let baseName := if rawName == "main" then "main'" else rawName
        -- In a run-twin (`--mode both`) the emitted name gets the `'rn` suffix (`foo` → `foo'rn`);
        -- `baseName` (unsuffixed) is still used to scan the JSON body for self-reference (recursion).
        let name ← withRunSuffix baseName
        let nameIdent := mkIdent name.toName
        -- A *pure* body that is some `let`-bindings followed by ONE obligation (`assert C`, or
        -- `if H: assert C`) becomes a named, reusable `@[taste_ingr] theorem`. `theoremShape?` is the
        -- single source of truth — it returns `(lets, hyps, conclusion)` and matches only pure bodies,
        -- so monadic/loop/mutation bodies never reach here. The statement is built outside-in:
        -- `∀ params, let x := …; H1 → … → C`, lowered as a `Prop` (so `==`→`=`, `<`/`≤`→real order).
        -- The run twin (`approx`) drops the obligation. Anything else (≥2 asserts, non-`let` statements)
        -- stays a `def` with anonymous `have`s (see `Head_Assert`).
        let bodyArr := (json.getObjValAs? (Array Json) "body").toOption.getD #[]
        let substantive := bodyArr.filter fun (s : Json) =>
          jsonNodeType? s != some "Comment" && jsonNodeType? s != some "DocString"
        let paramNames := (← functionArgInfos json).map (fun (id, _) => id.getId.toString)
        if let some (letJsons, hypJsons, conclJson) := theoremShape? paramNames bodyArr substantive then
          if (← getNumericMode) == .approx then return ⟨mkNullNode #[]⟩
          let thmCmd ← buildSpecTheorem nameIdent (← functionArgInfos json) letJsons hypJsons conclJson
          return ⟨mkNullNode #[thmCmd.raw]⟩
        -- Track P: a pure, straight-line contracted function (`Requires`/`Ensures` + `let`s +
        -- `return`) emits its ordinary runnable `def` (contracts stripped) plus a `<fn>_spec` theorem.
        if let some (cleanBody, letJsons, hypJsons, conclJson) := contractShape? paramNames bodyArr substantive then
          let argInfos ← functionArgInfos json
          let valueStx ← functionValueSyntax argInfos cleanBody
          let finalDef ← applyPrivacy name (← `(command| def $nameIdent := $valueStx))
          if (← getNumericMode) == .approx then
            return ⟨mkNullNode #[finalDef.raw]⟩
          let thmName := mkIdent (name ++ "_spec").toName
          let thmCmd ← buildSpecTheorem thmName argInfos letJsons hypJsons conclJson
          let attrCmd ← `(command| attribute [simp] $nameIdent)
          return ⟨mkNullNode #[finalDef.raw, attrCmd.raw, thmCmd.raw]⟩
        -- Track W: a `while`-loop contracted function (single straight-line `while` with `Invariant`
        -- + `Decreases`). Lowered through `pyWhile` + `pyWhile_correct` (the `while` rule), since core
        -- `while` is the opaque `whileM` mvcgen can't reason about. Exact mode only; the `'rn` twin
        -- keeps a real `while`.
        if (← getNumericMode) == .exact then
          if let some sh := whileContractShape? paramNames substantive then
            let cmds ← buildWhileFunction name json sh
            return ⟨mkNullNode (cmds.map (·.raw))⟩
        -- Track M: a monadic contracted function (a `for` loop with `Invariant(...)`). Emit the
        -- function `Id`-typed (so `mvcgen` sees the `do`) with `Requires`/`Assume` stripped to the
        -- precondition, plus a `<fn>_spec` Hoare-triple theorem driven by `mvcgen … with taste?`.
        -- Exact mode only; the runnable `'rn` twin (approx) falls through to normal emission.
        if (← getNumericMode) == .exact then
          if let some info := monadicContractInfo? substantive then
            let argInfos ← functionArgInfos json
            -- Pick the monad mvcgen sees. A `try`/`raise` body needs a *pure* exception monad with
            -- mvcgen `throw`/`try` specs: `ExceptT PyException Id`. `Id` has no `MonadExcept`, so
            -- `throw`/`caught.OfKind` won't elaborate; bare `Except PyException` leaves universe
            -- metavariables in `Spec.throw_Except` for an *uncaught* `throw`; `PyExcept` drags in `IO`
            -- (no mvcgen specs). `ExceptT … Id` avoids all three. A pure body stays `Id _`.
            let usesExc := bodyNeedsExceptionMonad info.cleanBody
            let valueStx ← withFreshVariables do
              let bodyStxArray ← monadicFunctionBodySyntax info.cleanBody
              let doStx ← `(do $[$bodyStxArray:doElem]*)
              let monadTy ← if usesExc then `(ExceptT PastaLean.PyException Id _) else `(Id _)
              let mut v ← `(($doStx : $monadTy))
              for (argIdent, ty?) in argInfos.reverse do
                v ← match ty? with
                  | some ty => `(fun ($argIdent : $ty) ↦ $v)
                  | none => `(fun $argIdent ↦ $v)
              pure v
            -- A body that touches `ℝ` is noncomputable in exact mode; the verification def only needs
            -- to *elaborate* for `mvcgen`, so mark it as such. `bodyNeedsNoncomputable` catches a direct
            -- transcendental (`math.sqrt`); the `_real_fn` stamp (set by the Python per-variable pass)
            -- additionally catches *transitive* ℝ — e.g. a function whose value comes from calling
            -- another ℝ-returning function (`euclidean_distance`), which the body scan can't see.
            let nc ← (pure (json.getObjValAs? Bool "_real_fn" == .ok true)) <||>
              bodyNeedsNoncomputable info.cleanBody
            let defCmd ← if nc then `(command| noncomputable def $nameIdent := $valueStx)
              else `(command| def $nameIdent := $valueStx)
            let finalDef ← applyPrivacy name defCmd
            let thmCmd ← buildMonadicSpec (mkIdent (name ++ "_spec").toName) nameIdent
              (argInfos.map (·.1)) info
            return ⟨mkNullNode #[finalDef.raw, thmCmd.raw]⟩
        -- `_real_fn` (set by the Python per-variable pass) means the function produces or handles an
        -- `ℝ` value → it must be `noncomputable` in exact mode. This is now DECOUPLED from which
        -- floats are `ℝ`: real params carry a per-`arg` `_real` stamp (read in `functionArgInfos`)
        -- and real local literals are lowered under a per-assignment `withRealContext`; the function
        -- is NOT blanket-lifted, so its `ℚ` locals stay `ℚ`.
        let isReal := (← getNumericMode) == .exact && json.getObjValAs? Bool "_real_fn" == .ok true
        let argInfos ← functionArgInfos json
        let effectCmd? ← functionCommandWithEffectSignature? nameIdent argInfos json isReal
        -- Drop any `Ensures(Result() …)`/`Assert(Result() …)` markers: they are verification-only
        -- (lifted to the spec postcondition) and `Result()` has no runtime lowering, so they must not
        -- leak into a runnable body — notably the `'rn` twin, which reaches this generic path.
        let bodyElems := stripResultMarkers (← functionBodyElems json)
        let isRecursive := bodyElems.any (jsonReferencesName · baseName)
        -- A real-valued body (transcendental, directly or via a callee) forces `noncomputable`.
        let nc := isReal || (← bodyNeedsNoncomputable bodyElems)
        let cmd ← match effectCmd? with
          | some cmd => pure cmd
          | none =>
              let valueStx ← functionValueSyntax argInfos bodyElems
              -- take care of recursion function Type
              if isRecursive then
                let fullTy? ← match ← functionReturnTypeSyntax? json with
                  | some retTy => functionArrowTypeSyntax? argInfos retTy
                  | none => pure none
                match fullTy?, nc with
                | some fullTy, true => `(noncomputable partial def $nameIdent : $fullTy := $valueStx)
                | some fullTy, false => `(partial def $nameIdent : $fullTy := $valueStx)
                | none, true => `(noncomputable partial def $nameIdent := $valueStx)
                | none, false => `(partial def $nameIdent := $valueStx)
              else if nc then
                `(noncomputable def $nameIdent := $valueStx)
              else
                `(def $nameIdent := $valueStx)
        -- Python's leading-underscore convention (`def _foo`) maps to a Lean `private def`.
        let finalCmd ← applyPrivacy name cmd
        -- Tag prove-version (exact) functions for proof search. Skip RECURSIVE/`partial` defs: Lean
        -- rejects `@[simp]` on them (no unfolding equation). `taste_ingr` is narrower still — only a
        -- *simple arithmetic* function (pure: no IO/raise, no `assert` in its body, computable) — so
        -- `taste?`'s `simp only [taste_ingr]` stays a small fast set (never `main'`, a proof
        -- obligation, or a noncomputable `norm` whose `whnf` would stall simp).
        if (← getNumericMode) == .exact && !isRecursive then
          let isEffectful := bodyNeedsExceptionMonad bodyElems || bodyNeedsIOMonad bodyElems
          let hasAssert := bodyArr.any (jsonNodeType? · == some "Assert")
          let attrCmd ← if !isEffectful && !hasAssert && !nc
            then `(command| attribute [simp, taste_ingr] $nameIdent)
            else `(command| attribute [simp] $nameIdent)
          return ⟨mkNullNode #[finalCmd.raw, attrCmd.raw]⟩
        else
          return finalCmd
    | `term, json => do
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        functionValueSyntax argInfos bodyElems
    | `doElem, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        let valueStx ← functionValueSyntax argInfos bodyElems
        `(doElem| let $nameIdent := $valueStx)
    | kind, _ => throwError s!"Unsupported syntax category `{kind}` for FuncDef node"

@[pygen "Head_Assign"]
def assignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assign node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        match ← tupleAssignTargetNames? target with
        | some idents => do
            let n := idents.size
            let valueStx ← getCode value `term
            let unpackTmpIdent := mkIdent (← freshName `__unpack_pair)
            -- A `Tuple` literal or a tuple-returning function call both produce a `Prod` (use
            -- `Prod.fst`/`Prod.snd`); list-returning RHSs are pre-split into subscripts and never
            -- reach native unpacking (see Core/Assign.lean for the same reasoning).
            let isTuple := jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            let mut result := tailCode
            for i in (List.range n).reverse do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              result ← `(let $(idents[i]!) := $acc
                $result)
            `(let $unpackTmpIdent := $valueStx
              $result)
        | none => do
            let nameIdent ← getCode target `ident
            let valueStx ← getCode value `term
            `(let $nameIdent := $valueStx
              $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_Assign node"

@[pygen "Head_AnnAssign"]
def annAssignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
              s!"AnnAssign node does not have a 'rest' field or it is not a JSON value: {json}"
            let splitRest ← splitList rest
            withoutCheck do
              getCode splitRest `term
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Head_Assign")]
            let json := targetJson.mergeObj json
            assignHeadSyntax `term json
    | _, _ => throwError s!"Unsupported syntax category for Head_AnnAssign node"

@[pygen "Head_Pass"]
def passHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Pass node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        withoutCheck do
          getCode splitRest `term
    | _, _ => throwError s!"Unsupported syntax category for Head_Pass node"

@[pygen "Head_FunctionDef"]
def functionDefHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json
        let bodyElems ← functionBodyElems json
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"FuncDef node does not have a 'rest' field or it is not a JSON value: {json}"
        let valueStx ← functionValueSyntax argInfos bodyElems
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        `(let $nameIdent := $valueStx
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_FunctionDef node"

@[pygen "Head_If"]
def ifHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"If node does not have a 'rest' field or it is not a JSON value: {json}"
        if !rest.isEmpty &&
            (!statementListDefinitelyReturns bodyElems.toList ||
              !statementListDefinitelyReturns orelseElems.toList) then
          throwError
            "If branches that fall through into later statements require monadic lowering."
        let testStx ← getCode testJson `term
        let thenBranch ← withoutCheck do
          let splitThen ← splitList (bodyElems.toList ++ rest)
          getCode splitThen `term
        let elseTail := if orelseElems.isEmpty then rest else orelseElems.toList ++ rest
        let elseBranch ← withoutCheck do
          let splitElse ← splitList elseTail
          getCode splitElse `term
        `(if $testStx then $thenBranch else $elseBranch)
    | _, _ => throwError s!"Unsupported syntax category for Head_If node"

@[pygen "Head_Match"]
def matchHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok subjectJson := json.getObjValAs? Json "subject" | throwError
          s!"Match node does not have a 'subject' field or it is not a JSON value: {json}"
        let .ok casesJson := json.getObjValAs? (Array Json) "cases" | throwError
          s!"Match node does not have a 'cases' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Match node does not have a 'rest' field or it is not a JSON value: {json}"
        let subjectTerm ← getCode subjectJson `term
        matchCaseTermSyntax subjectTerm casesJson.toList rest
    | _, _ => throwError s!"Unsupported syntax category for Head_Match node"

@[pygen "Head_Return"]
def returnHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← withoutCheck do
          getCode value `term
        return valueStx
    | _, _ => throwError s!"Unsupported syntax category for Head_Return node"

/-- All top-level `FunctionDef` nodes in a module body, paired with their names, in module order. -/
def topLevelFuncDefs (bodyElems : Array Json) : Array (String × Json) :=
  bodyElems.filterMap fun e =>
    match e.getObjValAs? String "node_type", e.getObjValAs? String "name" with
    | .ok "FunctionDef", .ok name => some (name, e)
    | _, _ => none

/-- For each top-level function, the set of top-level functions reachable from its body
(transitive closure of "references"). Used to find mutually-recursive groups. -/
def transitiveFuncRefs (funcs : Array (String × Json)) : Array (String × Array String) := Id.run do
  let names := funcs.map (·.1)
  let mut reach : Array (String × Array String) := funcs.map fun (nm, body) =>
    (nm, names.filter fun m => jsonReferencesName body m)
  -- Relax to a fixed point (longest reference chain is at most `names.size` long).
  for _ in [0:names.size] do
    reach := reach.map fun (nm, rs) => Id.run do
      let mut acc := rs
      for r in rs do
        match reach.find? (·.1 == r) with
        | some (_, rs2) =>
            for x in rs2 do
              unless acc.contains x do acc := acc.push x
        | none => pure ()
      return (nm, acc)
  return reach

/-- The mutual-recursion group (strongly-connected component) containing `nm`: every function `m`
such that `nm` reaches `m` and `m` reaches `nm`. A non-mutual function yields a singleton. -/
def mutualGroupOf (reach : Array (String × Array String)) (nm : String) : Array String :=
  let reachOf := fun x => ((reach.find? (·.1 == x)).map (·.2)).getD #[]
  (#[nm] ++ (reachOf nm).filter fun m => m != nm && (reachOf m).contains nm)

/-- Build `partial def name : <arg tys → ret> := value` for a member of a mutual group. The
explicit signature is required for `mutual` and also keeps operators from defaulting (see the
self-recursive case in `funcDefSyntax`). -/
def mutualMemberDef (json : Json) : PygenM (TSyntax `command) := do
  let .ok name := json.getObjValAs? String "name" | throwError
    s!"FuncDef node does not have a 'name' field: {json}"
  let nameIdent := mkIdent name.toName
  let argInfos ← functionArgInfos json
  let bodyElems ← functionBodyElems json
  let valueStx ← functionValueSyntax argInfos bodyElems
  match ← functionReturnTypeSyntax? json with
  | some retTy =>
      match ← functionArrowTypeSyntax? argInfos retTy with
      | some fullTy => `(command| partial def $nameIdent : $fullTy := $valueStx)
      | none => `(command| partial def $nameIdent := $valueStx)
  | none => `(command| partial def $nameIdent := $valueStx)

@[pygen "Module"]
def moduleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let some first := bodyElems[0]? | throwError "Cannot translate an empty module to a term."
        unless bodyElems.size == 1 do
          throwError "Module-to-term translation requires exactly one top-level statement."
        withFreshVariables do
          getCode first `term
    | `command, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let funcs := topLevelFuncDefs bodyElems
        let reach := transitiveFuncRefs funcs
        let mut cmds : Array (TSyntax `command) := #[]
        let mut emitted : Array String := #[]
        for elem in bodyElems do
          match elem.getObjValAs? String "node_type", elem.getObjValAs? String "name" with
          | .ok "FunctionDef", .ok name =>
              unless emitted.contains name do
                let group := mutualGroupOf reach name
                if group.size ≥ 2 then
                  -- A mutually-recursive group can't be a sequence of plain `def`s (each would
                  -- forward-reference an undeclared name), so emit it as one `mutual … end` block
                  -- of `partial def`s, in module order.
                  let members := funcs.filterMap fun (m, j) =>
                    if group.contains m then some j else none
                  let defs ← members.mapM fun j => withFreshVariables do mutualMemberDef j
                  cmds := appendCommandSyntax cmds (← `(command| mutual $defs:command* end))
                  emitted := emitted ++ group
                else
                  cmds := appendCommandSyntax cmds (← withFreshVariables do getCode elem `command)
          | _, _ =>
              cmds := appendCommandSyntax cmds (← withFreshVariables do getCode elem `command)
        return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
    | _, _ => throwError s!"Unsupported syntax category for Module node"

end PastaLean
