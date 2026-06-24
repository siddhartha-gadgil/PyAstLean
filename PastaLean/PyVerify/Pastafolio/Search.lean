import PastaLean.PyVerify.Pastafolio.Basic

/-!
# Pastafolio proof search — the engine

The domain-agnostic search loop over a `Profile`. Given the profile's tiered candidate tactics,
it races them in priority order, commits the first that makes progress (resolving `simp?`/`grind?`
to concrete tactics), re-derives the tiers against the new goal, and repeats — then records the
discovered proof and `sorry`s any residual so the surrounding term still elaborates.
-/

open Lean Elab Tactic Meta Meta.Tactic.TryThis

namespace PastaLean.Pastafolio

/-- Run `tac` for real progress: a target changed OR the goal count changed (so `intros`, splits,
etc. count). Rejects `sorry`-closures. Does not restore state — the caller owns rollback. `none`
means "did nothing useful / failed / cheated with sorry / ran out of its `budget`". -/
def runForProgress (budget : Nat) (tac : TSyntax `tactic) (before : List Expr)
    (beforeGoals : List MVarId) : TacticM (Option (List Expr)) := do
  try
    withBudget budget (withoutRecover (evalTactic tac))
    let after ← goalTargets
    let afterGoals ← getGoals
    let madeProgress := before != after || beforeGoals.length != afterGoals.length
    if !madeProgress then
      return none
    for g in beforeGoals do
      unless afterGoals.contains g do
        if (← instantiateMVars (mkMVar g)).hasSorry then
          return none
    return some after
  catch _ =>
    return none

/-- Try a *simplifier*: commit on any progress to a goal-state not seen before (loop detection
rejects churn that revisits a state). Returns the rendered tactic and the new state, or `none`. -/
def trySimplifier (visited : List (List Expr)) (budget : Nat) (tac : TSyntax `tactic) :
    TacticM (Option (String × List Expr)) := do
  let before ← goalTargets
  let beforeGoals ← getGoals
  let saved ← saveState
  match ← runForProgress budget tac before beforeGoals with
  | none => saved.restore; return none
  | some after =>
    if visited.contains after then
      saved.restore         -- revisiting a seen state ⇒ a cycle; reject so the search can stop
      return none
    return some (← tacToString tac, after)

/-- Try a *closer*: commit only if it discharges **all** open goals (and not via `sorry`). A tactic
that merely normalizes the goal without closing it is rejected, so it never lands in the proof. -/
def tryCloser (budget : Nat) (tac : TSyntax `tactic) : TacticM (Option String) := do
  let beforeGoals ← getGoals
  let saved ← saveState
  try
    withBudget budget (withoutRecover (evalTactic tac))
    unless (← getGoals).isEmpty do
      saved.restore
      return none
    for g in beforeGoals do
      if (← instantiateMVars (mkMVar g)).hasSorry then
        saved.restore
        return none
    return some (← tacToString tac)
  catch _ =>
    saved.restore
    return none

/-- Race simplifiers; first that reaches a new goal-state wins. -/
def raceSimplifiers (visited : List (List Expr)) (budget : Nat) (cands : Array (TSyntax `tactic)) :
    TacticM (Option (String × List Expr)) := do
  for tac in cands do
    match ← trySimplifier visited budget tac with
    | some r => return some r
    | none   => pure ()
  return none

/-- Race closers; first that fully closes the goal wins. -/
def raceClosers (budget : Nat) (cands : Array (TSyntax `tactic)) : TacticM (Option String) := do
  for tac in cands do
    match ← tryCloser budget tac with
    | some r => return some r
    | none   => pure ()
  return none

/-- The two-phase search. Each round: re-derive the profile's tactics against the current goal,
greedily commit one simplifier step if any makes progress (recursing so simplification runs to a
fixpoint, with cycle detection), and only once simplification stalls try the closers — the first
that fully discharges the goal wins. Stops when simplification stalls and no closer closes; the
caller then records the committed prefix and `sorry`s the residual. `fuel` bounds simplifier steps. -/
partial def search (budget : Nat) (fuel : Nat) (p : Profile) (visited : List (List Expr))
    (acc : Array String) : TacticM (Array String) := do
  if fuel == 0 then return acc
  if (← getGoals).isEmpty then return acc
  let visited := (← goalTargets) :: visited
  match ← raceSimplifiers visited budget (← p.simplifiers) with
  | some (r, after) =>
    return (← search budget (fuel - 1) p (after :: visited) (acc.push r))
  | none =>
    match ← raceClosers budget (← p.closers) with
    | some r => return (acc.push r)
    | none   => return acc

/-- Drive a portfolio `p` on the current goal(s): search, build the proof string from the committed
candidates (or a `…; sorry` prefix when only partial progress was made), record it in
`p.winnersRef?`, offer it as a "Try this" at `stx`, and discharge any residual with `sorry` so the
surrounding term still elaborates. -/
def runPastafolio (p : Profile) (stx : Syntax) : TacticM Unit := do
  -- Per-candidate cap from the ambient `maxHeartbeats` (the file's `set_option`). The orchestration
  -- itself runs unbounded so its own bookkeeping never times out mid-search, and a candidate
  -- exhausting its budget only kills that candidate. Read before zeroing the ambient.
  let raw := match Lean.Core.getMaxHeartbeats (← getOptions) with
    | 0 => 200000000
    | n => n
  let budget := p.budget raw
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    let used ← search budget p.fuel p [] #[]
    let closed := (← getGoals).isEmpty
    -- `;`-sequence the committed tactics. No surrounding parens: a `by t1; t2; t3` block parses
    -- fine both as a top-level `theorem … := by …` and as an in-body `have … := by …`.
    let proof :=
      if closed then
        String.intercalate "; " used.toList
      else
        String.intercalate "; " (used.toList ++ ["sorry"])
    if let some ref := p.winnersRef? then
      ref.modify (·.push proof)
    match Lean.Parser.runParserCategory (← getEnv) `tactic proof with
    | .ok s => addSuggestion stx (⟨s⟩ : TSyntax `tactic) (origSpan? := stx)
    | .error _ => pure ()
    unless closed do
      evalTactic (← `(tactic| all_goals sorry))

end PastaLean.Pastafolio
