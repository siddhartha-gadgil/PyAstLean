import Std.Tactic.Do
open Std.Do

def sum_to_n : Int → Id Int := fun n ↦
  (do
      let mut total := (0 : Int)
      let mut i := (1 : Int)
      while i <= n do
        total := total + i
        i := i + (1 : Int)
      return total)

-- Proof using while loop variant and invariant
def sum_to_n_correct : ⦃⌜ n ≥ 0 ⌝⦄ sum_to_n n ⦃⇓ r => ⌜ r = n * (n + 1) / 2 ⌝⦄ := by
  mvcgen [sum_to_n] invariants
    · fun ⟨i, total⟩ => .up (Int.toNat (n - i + 1))
    · ⇓ state => match state with
      | Sum.inl ⟨i, total⟩ => ⌜total = (i - 1) * i / 2 ∧ 1 ≤ i ∧ i ≤ n + 1⌝
      | Sum.inr ⟨i, total⟩ => ⌜total = n * (n + 1) / 2⌝
  with grind
