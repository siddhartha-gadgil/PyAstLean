import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- While-loop product accumulator with an explicit termination measure (Decreases).
-- Maintainable invariant: the running product stays >= 1 (so it is never zero / negative).
def factorial := fun (n : Int) ↦
  (do
    let mut result := (1 : Int)
    for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
      let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassDecreases (n -ₚ i)
      result := result *ₚ i
    let _ := Libraries.passta.pyPassEnsures (decide (result ≥ (1 : Int)))
    return result : Id _)

theorem factorial_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ factorial n ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [factorial, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, result⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      result ≥ (1 : Int)⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; nlinarith

def factorial'rn := fun (n : Int) ↦
  Id.run
    (do
      let _ := Libraries.passta.pyPassRequires (decide (n ≥ (0 : Int)))
      let mut result := (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
        let _ := Libraries.passta.pyPassDecreases (n -ₚ i)
        result := result *ₚ i
      let _ := Libraries.passta.pyPassEnsures (decide (result ≥ (1 : Int)))
      return result)
