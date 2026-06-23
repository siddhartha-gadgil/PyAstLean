import Mathlib
import PastaLean.PyAPI.Operators

open Lean Elab Tactic Meta Meta.Tactic.TryThis

-- The `taste_ingr` simp set is registered in `PastaLean.PyAPI.Operators` (imported above) so the
-- operator rewrite lemmas can join it; the code generator also tags every pure prove-version
-- function with it. `taste?` unfolds the whole set with `simp [taste_ingr]`.

namespace PastaLean

/-!
# `taste` — search for a proof of a transpiled `assert`, or fall back to `sorry`

Generated `assert` statements emit `… := by taste`. When elaborated, this tactic tries a
fixed list of candidate tactics in order; the first one that *closes the goal* is kept, else it fails.
-/


/-- The candidate tactics tried for an assert goal, in order. Edit this list to taste. -/
def assertCandidates : TacticM (Array (TSyntax `tactic)) := do
  return #[
    -- `taste_ingr` already holds the transpiled functions AND the `*ₚ` operator lemmas, so these
    -- The `zetaDelta` is for `have` that binds intermediate `let`s (`new_depot := …`).
    ← `(tactic| (intros <;> simp_all (config := { zetaDelta := true }) [taste_ingr] <;> push_cast <;> grind +suggestions +locals)),
    ← `(tactic| (simp_all [taste_ingr] <;> grind +locals +suggestions)),
    ← `(tactic| grind +locals +suggestions),
    ← `(tactic| try?),
    ← `(tactic| sorry),
  ]

syntax (name := assertProveStx) "taste?" : tactic

@[tactic assertProveStx]
def evalAssertProve : Tactic := fun stx => do
  let candidates ← assertCandidates
  for tac in candidates do
    let saved ← saveState
    -- Try the candidate; success = it ran without error AND left no open goals.
    let closed ←
      try
        evalTactic tac
        pure (← getUnsolvedGoals).isEmpty
      catch _ =>
        pure false
    if closed then
      -- Keep this proof: suggest replacing `taste?` with the winning tactic.
      addSuggestion stx tac (origSpan? := stx)
      return
    else
      saved.restore
  -- Nothing worked — leave a `sorry` (and suggest it, so the search call is still replaced).
  let sry ← `(tactic| sorry)
  addSuggestion stx sry (origSpan? := stx)
  evalTactic sry

end PastaLean
