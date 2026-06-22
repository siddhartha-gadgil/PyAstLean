import Mathlib

open Lean Elab Tactic Meta Meta.Tactic.TryThis

namespace PastaLean

/-!
# `taste` — search for a proof of a transpiled `assert`, or fall back to `sorry`

Generated `assert` statements emit `… := by taste`. When elaborated, this tactic tries a
fixed list of candidate tactics in order; the first one that *closes the goal* is kept, and a
"Try this: <tactic>" suggestion is emitted so the `taste` call can be replaced by the concrete
proof in the source. If none close the goal, it suggests (and runs) `sorry`, so the file still
elaborates. Running the file therefore turns every `taste` into either a real proof or a
`sorry` — never a leftover search call.
-/

/-- The candidate tactics tried for an assert goal, in order. Edit this list to taste. -/
def assertCandidates : TacticM (Array (TSyntax `tactic)) := do
  return #[
    ← `(tactic| rfl),
    ← `(tactic| simp_all),
    ← `(tactic| grind +locals +suggestions),
    ← `(tactic| (simp_all <;> grind +locals +suggestions)),
    ← `(tactic| plausible),
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
