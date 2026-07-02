import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

def factorial := fun (n : Int) ↦
  (do
    let mut result := (1 : Int)
    for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
      let _ := Libraries.passta.pyPassInvariant (decide (i ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassInvariant (decide (n -ₚ i +ₚ (1 : Int) ≥ (0 : Int)))
      let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassDecreases (n -ₚ i +ₚ (1 : Int))
      result := result *ₚ i
    return result : Id _)

@[spec]
theorem factorial_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ factorial n ⦃⇓result => ⌜result ≥ (1 : Int)⌝⦄ :=
  by
  mvcgen [factorial, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, result⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      (i ≥ (1 : Int) ∧ n -ₚ i +ₚ (1 : Int) ≥ (0 : Int)) ∧ result ≥ (1 : Int)⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry; sorry; omega

def factorial'rn := fun (n : Int) ↦
  Id.run
    (do
      let _ := Libraries.passta.pyPassRequires (decide (n ≥ (0 : Int)))
      let mut result := (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        let _ := Libraries.passta.pyPassInvariant (decide (i ≥ (1 : Int)))
        let _ := Libraries.passta.pyPassInvariant (decide (n -ₚ i +ₚ (1 : Int) ≥ (0 : Int)))
        let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
        let _ := Libraries.passta.pyPassDecreases (n -ₚ i +ₚ (1 : Int))
        result := result *ₚ i
      return result)
