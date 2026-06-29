import PastaLean.PyGens.Core.Utils
import PastaLean.PyVerify.AssertTactic
import Std.Tactic.Do

/-!
# PASSTA contract codege

Detection and theorem-building for the `Libraries.passta` contract markers (`Requires`/`Ensures`/ `Assert`/`Assume`/`Invariant`/`Decreases`).
-/

open Lean Meta Elab Term Qq Std
open Lean.Parser.Term
open Std.Do

namespace PastaLean

/-- `contractArg?` extracts contract metadata from a Python AST node. Verifies the function is from the "passta" library. Extracts the contract type (library member:
"Requires" /"Ensures" /"Assert" /"Assume" /"Invariant"/"Decreases") and Returns the contract type paired with its argument, or none if it's not a contract statement -/
def contractArg? (stmt : Json) : Option (String × Json) :=
  match jsonNodeType? stmt with
  | some "Expr" =>
    match (stmt.getObjVal? "value").toOption with
    | some value =>
      match jsonNodeType? value, (value.getObjVal? "func").toOption with
      | some "Call", some func =>
        match func.getObjValAs? String "library_module", func.getObjValAs? String "library_member",
              (value.getObjValAs? (Array Json) "args").toOption with
        | .ok "passta", .ok member, some args =>
          match args[0]? with
          | some arg => some (member, arg)
          | none => none
        | _, _, _ => none
      | _, _ => none
    | none => none
  | _ => none

/-- A *pure, straight-line* contracted function (`Requires`/`Ensures`, `let`s, `return` —
no loops, IO, or `raise`). Splits the body into the runnable statements (contracts stripped) and the
proof data. Returns `(cleanBody, lets, hyps, concl)`. `none` if monadic, if any statement isn't a
fresh `let`/`return`/contract, if an `Invariant`/`Decreases` appears (those imply a loop)
or if there's no `Ensures`/`Assert` to prove. Multiple `Ensures` conjoin into one conclusion. -/
def contractShape? (paramNames : Array String) (body substantive : Array Json) :
    Option (Array Json × Array Json × Array Json × Json) := Id.run do
  if bodyNeedsIOMonad body || bodyNeedsExceptionMonad body then return none
  let mut lets : Array Json := #[]
  let mut hyps : Array Json := #[]
  let mut concls : Array Json := #[]
  let mut clean : Array Json := #[]
  let mut seen : Array String := #[]
  let mut sawContract := false
  let mut sawReturn := false
  for s in substantive do
    match contractArg? s with
    | some (member, arg) =>
      sawContract := true
      match member with
      | "Requires" | "Assume" => hyps := hyps.push arg
      | "Ensures" | "Assert" => concls := concls.push arg
      | _ => return none
    | none =>
      match jsonNodeType? s with
      | some "Return" => sawReturn := true; clean := clean.push s
      | some "Assign" =>
        let .ok target := s.getObjVal? "target" | return none
        if jsonNodeType? target != some "Name" then return none
        let .ok tname := target.getObjValAs? String "id" | return none
        if paramNames.contains tname || seen.contains tname then return none
        seen := seen.push tname
        lets := lets.push s
        clean := clean.push s
      | _ => return none
  if !sawContract || concls.isEmpty || !sawReturn then return none
  let concl := if concls.size == 1 then concls[0]!
    else Json.mkObj [("node_type", Json.str "BoolOp"), ("op", Json.str "and"), ("values", Json.arr concls)]
  return some (clean, lets, hyps, concl)

/-- Build `@[taste_ingr] theorem <thmName> : ∀ params, <hyps> → (let-binders; <concl>) := by taste?`
from extracted proof data. Shared by the lone-assert promotion (`theoremShape?`) and the contract
(`_spec`) path.  -/
def buildSpecTheorem (thmName : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (letJsons hypJsons : Array Json) (conclJson : Json) : PygenM (TSyntax `command) :=
  withFreshVariables do
    for letJson in letJsons do
      if let .ok tname := (letJson.getObjVal? "target").bind (·.getObjValAs? String "id") then
        addVar tname.toName
    let mut propTy ← withPropCondition true (getCode conclJson `term)
    for hypJson in hypJsons.reverse do
      propTy ← `($(← withPropCondition true (getCode hypJson `term)) → $propTy)
    for letJson in letJsons.reverse do
      let .ok target := letJson.getObjVal? "target" | throwError "buildSpecTheorem: Assign without target"
      let .ok value := letJson.getObjVal? "value" | throwError "buildSpecTheorem: Assign without value"
      propTy ← `(let $(← getCode target `ident) := $(← getCode value `term)
                 $propTy)
    for (argIdent, ty?) in argInfos.reverse do
      propTy ← match ty? with
        | some ty => `(∀ ($argIdent : $ty), $propTy)
        | none => `(∀ $argIdent, $propTy)
    `(command| @[taste_ingr] theorem $thmName : $propTy := by taste?)

/-- Does any `Assign`/`AugAssign` inside `stmt` (recursing into nested bodies) target `name`? Used
to find which mutable variables a loop threads (its mvcgen state). -/
partial def jsonAssignsName (stmt : Json) (name : String) : Bool :=
  match jsonNodeType? stmt with
  | some "Assign" | some "AugAssign" =>
    ((stmt.getObjVal? "target").bind (·.getObjValAs? String "id")) == .ok name
  | _ => Id.run do
    for key in ["body", "orelse", "finalbody"] do
      if let .ok (arr : Array Json) := stmt.getObjValAs? (Array Json) key then
        for s in arr do
          if jsonAssignsName s name then return true
    return false

/-- Mutable-variable declaration order: top-level `Assign` targets, first occurrence first. This is
the order mvcgen threads them as the loop state tuple. -/
def declaredMutOrder (body : Array Json) : Array String := Id.run do
  let mut acc : Array String := #[]
  for s in body do
    if jsonNodeType? s == some "Assign" then
      if let .ok name := (s.getObjVal? "target").bind (·.getObjValAs? String "id") then
        if !acc.contains name then acc := acc.push name
  return acc

/-- If accumulator `acc` is updated at the loop-body top level by `acc += e` or `acc = acc + e`,
return the contribution `e` — used to auto-derive `acc = (cur.prefix.map (fun v => e)).sum` when the
user gave no `Invariant`. `none` for conditional/other mutations. -/
def accContribution? (loopBody : Array Json) (acc : String) : Option Json := Id.run do
  for s in loopBody do
    match jsonNodeType? s with
    | some "AugAssign" =>
      if (s.getObjVal? "target").bind (·.getObjValAs? String "id") == .ok acc
          && s.getObjValAs? String "op" == .ok "add" then
        return (s.getObjVal? "value").toOption
    | some "Assign" =>
      if (s.getObjVal? "target").bind (·.getObjValAs? String "id") == .ok acc then
        if let some value := (s.getObjVal? "value").toOption then
          if jsonNodeType? value == some "BinOp" && value.getObjValAs? String "op" == .ok "add" then
            match (value.getObjVal? "left").toOption, (value.getObjVal? "right").toOption with
            | some lj, some rj =>
              if lj.getObjValAs? String "id" == .ok acc then return some rj
              if rj.getObjValAs? String "id" == .ok acc then return some lj
            | _, _ => pure ()
    | _ => pure ()
  return none

/-- Does `stmt` early-exit *this* loop (a `return`/`break`, recursing through `if`s but not into a
nested `for`/`while`, which owns its own exits)? Such a loop threads an extra early-return state, so
its invariant must use `Invariant.withEarlyReturn` rather than a plain `⇓` bullet. -/
partial def jsonHasEarlyExit (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" | some "Break" => true
  | some "For" | some "While" => false
  | _ => Id.run do
    for key in ["body", "orelse", "finalbody"] do
      if let .ok (arr : Array Json) := stmt.getObjValAs? (Array Json) key then
        for s in arr do if jsonHasEarlyExit s then return true
    return false

/-- Per-loop invariant data: the loop variable, whether the iterable is a `range(...)`, the threaded
accumulators (in declaration order), the conjuncts of its `Invariant(...)` markers, the contribution
expressions of `+= e` accumulators (for auto-derivation), and whether the loop early-exits. -/
structure LoopInv where
  loopVar : String
  isRange : Bool
  accumulators : Array String
  invariants : Array Json
  accMutations : Array (String × Json)
  hasEarlyExit : Bool

/-- All proof data for a monadic contracted function. -/
structure MonadicContract where
  cleanBody : Array Json   -- def body with `Requires`/`Assume` stripped (other markers kept)
  requires : Array Json    -- `Requires`/`Assume` predicate args → precondition
  loops : Array LoopInv

/-- Builds a LoopInv from one For node. Returns none only if the For lacks a target/iter. -/
def loopInvOf (declaredOrder : Array String) (forNode : Json) : Option LoopInv :=
  match (forNode.getObjVal? "target").bind (·.getObjValAs? String "id"),
        (forNode.getObjVal? "iter").toOption with
  | .ok loopVar, some iter =>
    let isRange := jsonNodeType? iter == some "Range"
    let loopBody := (forNode.getObjValAs? (Array Json) "body").toOption.getD #[]
    let invariants := loopBody.filterMap fun s =>
      match contractArg? s with
      | some ("Invariant", arg) => some arg
      | _ => none
    let accumulators := declaredOrder.filter fun v => loopBody.any (jsonAssignsName · v)
    let accMutations := accumulators.filterMap fun a =>
      (accContribution? loopBody a).map (fun e => (a, e))
    let hasEarlyExit := loopBody.any jsonHasEarlyExit
    some { loopVar, isRange, accumulators, invariants, accMutations, hasEarlyExit }
  | _, _ => none

/-- A *monadic* contracted function (has a `for` loop with `Invariant(...)`, or effects).
Strips `Requires`/`Assume` (→ precondition), keeps everything else (so `Ensures` stay as in-body
checkpoints and `Invariant` markers stay as provable checkpoints), and records per-loop invariant
data. `none` when there is no contract marker. -/
def monadicContractInfo? (body : Array Json) : Option MonadicContract := Id.run do
  let declared := declaredMutOrder body
  let mut requires : Array Json := #[]
  let mut clean : Array Json := #[]
  let mut loops : Array LoopInv := #[]
  let mut sawContract := false
  for s in body do
    match contractArg? s with
    | some (member, _arg) =>
      sawContract := true
      match member with
      | "Requires" | "Assume" => requires := requires.push _arg
      | _ => clean := clean.push s
    | none =>
      if jsonNodeType? s == some "For" then
        if let some li := loopInvOf declared s then
          sawContract := sawContract || !li.invariants.isEmpty
          loops := loops.push li
      clean := clean.push s
  if !sawContract then return none
  return some { cleanBody := clean, requires, loops }

/-- Conjoin a list of `Prop` terms (empty → `True`). -/
private def conjoin (ps : Array (TSyntax `term)) : PygenM (TSyntax `term) :=
  match ps.toList with
  | [] => `(True)
  | p :: rest => rest.foldlM (fun acc q => `($acc ∧ $q)) p

/-- One invariant bullet for a loop. The predicate relates the accumulators to `cur.prefix`:
* user `Invariant(...)` markers, conjoined — for a `range` loop the loop variable is bound to
  `cur.prefix.length` (the index), so index-style invariants work;
* otherwise, **auto-derived** from each `acc += e` update: `acc = (cur.prefix.map (fun v => e)).sum`
  (only for non-`range` loops, where `cur.prefix` is the element list);
* else `True`.
The binder is `⇓ cur =>` with no accumulators, `⇓⟨cur, a, …⟩` with some. -/
def buildBullet (li : LoopInv) : PygenM (TSyntax `term) := do
  for a in li.accumulators do addVar a.toName
  addVar li.loopVar.toName
  -- A loop that `return`s/`break`s threads an early-return state; its invariant is supplied via
  -- `Invariant.withEarlyReturn`. For the `True` postcondition a trivial pair discharges it.
  if li.hasEarlyExit then
    return ← `(Invariant.withEarlyReturn (onReturn := fun _ _ => ⌜True⌝) (onContinue := fun _ _ => ⌜True⌝))
  let cur := mkIdent `cur
  let loopVarId := mkIdent li.loopVar.toName
  let body ←
    if !li.invariants.isEmpty then
      let props ← li.invariants.mapM (fun inv => withPropCondition true (getCode inv `term))
      let conj ← conjoin props
      if li.isRange then `(let $loopVarId := ($(cur).prefix.length : Int); $conj) else pure conj
    else if !li.isRange && !li.accMutations.isEmpty then
      let mut autos : Array (TSyntax `term) := #[]
      for (acc, contrib) in li.accMutations do
        let cStx ← getCode contrib `term
        autos := autos.push
          (← `($(mkIdent acc.toName) = ($(cur).prefix.map (fun $loopVarId => $cStx)).sum))
      conjoin autos
    else
      `(True)
  if li.accumulators.isEmpty then
    `(⇓ $cur => ⌜$body⌝)
  else
    -- mvcgen threads the loop state as a right-nested `MProd` whose `.fst` is the *last*-declared
    -- mutable variable, i.e. the tuple is in **reverse** declaration order.
    let accIdents := li.accumulators.reverse.map (fun s => mkIdent s.toName)
    `(⇓⟨$cur, $accIdents,*⟩ => ⌜$body⌝)

/-- Build the monadic spec theorem `⦃⌜Requires⌝⦄ fn params ⦃⇓ _ => ⌜True⌝⦄` proven by
`mvcgen [fn] invariants …` + a trailing `taste?`. Only the precondition is lifted from `Requires`/
`Assume`; the postcondition stays `True` (`Ensures`/`Assert` are proved as in-body checkpoints). -/
def buildMonadicSpec (thmName fnName : TSyntax `ident) (paramIdents : Array (TSyntax `ident))
    (info : MonadicContract) : PygenM (TSyntax `command) := withFreshVariables do
  for p in paramIdents do addVar p.getId
  let preProps ← info.requires.mapM (fun r => withPropCondition true (getCode r `term))
  let pre ← conjoin preProps
  let bullets ← info.loops.mapM buildBullet
  -- mvcgen lemma set is added here
  let lemmas ← #[(⟨fnName.raw⟩ : TSyntax `term), mkIdent ``PastaLean.pyRange_forIn,
      mkIdent ``PastaLean.pyRange_forIn_start].mapM
    (fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
  -- `taste?` is a TRAILING tactic (not `mvcgen … with taste?`). `with` runs one closer per VC, so
  -- heterogeneous VCs force an ugly `first | …` portfolio in the recorded proof. As a trailing tactic
  -- `taste?` instead sees all the leftover VCs as goals at once and its close-loop records a flat
  -- `c₁; c₂; …` sequence (one closer per goal, in order) — the prove-and-replace splice drops that in
  -- verbatim. If `mvcgen` already discharged every VC, `taste?` runs on no goals and records nothing,
  -- and the splice prunes the dangling `taste?` line, leaving a clean `mvcgen [...]`.
  let mv ← if bullets.isEmpty then
      `(tactic| mvcgen [$lemmas,*])
    else
      `(tactic| mvcgen [$lemmas,*] invariants $[· $bullets:term]*)

  -- POSTCONDITION (currently the postcondition is `True`, `Ensures` is proved as an
  -- in-body checkpoint instead). To lift `Ensures` into the spec *statement* (Nagini-style, modular
  -- `@[spec]` reuse): collect the `Ensures` args into `info.ensures` and the returned variable name
  -- into `info.retName` (see git history), then build the postcondition by binding that variable so an
  -- `Ensures(result …)` reads as a fact about the result, and tag the theorem `@[spec]`:
  --
  --   let retBinder := (info.retName.map (mkIdent ·.toName)).getD (mkIdent `x)
  --   if let some r := info.retName then addVar r.toName
  --   let postProps ← info.ensures.mapM (fun e => withPropCondition true (getCode e `term))
  --   let post ← conjoin postProps        -- empty ⇒ `True`
  --   `(command| @[spec] theorem $thmName :
  --       ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ $retBinder => ⌜$post⌝⦄ := by $mv:tactic
  -- taste?)
  --
  `(command| theorem $thmName :
      ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ _ => ⌜True⌝⦄ := by
        $mv:tactic
        taste?)

end PastaLean
