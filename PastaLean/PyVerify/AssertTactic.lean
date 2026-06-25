import Mathlib
import PastaLean.PyAPI.Operators
import PastaLean.PyVerify.Pastafolio

open Lean Elab Tactic
open PastaLean.Pastafolio

namespace PastaLean

/-! `taste?` — PastaLean's recipe for the Pastafolio proof-search engine. Just preferences; retune freely. -/

-- Extra lemmas for every `simp_all [taste_ingr]`. Add more with `attribute [taste_ingr] my_lemma`.
attribute [taste_ingr] mul_nonneg add_nonneg

/-- Discovered proofs, for the `py2lean` prove-and-replace pipeline. -/
initialize tasteWinnersRef : IO.Ref (Array String) ← IO.mkRef #[]

/-- Simplifiers reshape the goal (lower `+ₚ`/`*ₚ`, unfold leaves, clear casts); closers must fully
discharge it — first to close wins, so order is just preference. -/
def tasteProfile : Profile where
  simplifiers := do return #[
    ← `(tactic| intros),
    ← `(tactic| simp_all (config := { zetaDelta := true }) [taste_ingr]),
    ← `(tactic| push_cast at *)
  ]
  closers := do return #[
    ← `(tactic| ring),
    ← `(tactic| positivity),
    ← `(tactic| omega),
    ← `(tactic| linarith),
    ← `(tactic| nlinarith),
    ← `(tactic| grind +locals +suggestions),
    ← `(tactic| aesop)
  ]
  winnersRef? := some tasteWinnersRef

syntax (name := tasteStx) "taste?" : tactic

@[tactic tasteStx]
def evalTaste : Tactic := fun stx => runPastafolio tasteProfile stx

end PastaLean
