import Mathlib
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.Operators
import PastaLean.PyAPI.TasteIngr

/-!
# Helper lemmas for contract verification

`pyRange n` (Python `range(n)`) is `[0, 1, …, n-1]` as `Int`. mvcgen verifies loops over native
`List.range` out of the box (it recovers "element = index", membership, length, …), but `pyRange`
hides that behind an `Int`-cast. The fix is **one reduction spec** — `pyRange_forIn` — that rewrites
a `pyRange` loop into the equivalent native `List.range` loop (with the cast pushed into the body).
Pass it to mvcgen (`mvcgen [fn, pyRange_forIn] …`) and *every* `pyRange` loop inherits `List.range`'s
full native support, for any invariant style. This is the extensible approach: one spec per Python
container reducing it to its Mathlib primitive, rather than ad-hoc per-invariant lemmas.
-/

namespace PastaLean

/-- The `List Nat → List Int` coercion is elementwise `Int.ofNat`. -/
theorem coe_list_eq (l : List Nat) : (↑l : List Int) = l.map Int.ofNat := by
  induction l with
  | nil => rfl
  | cons h t ih => simp_all [Int.ofNat_eq_natCast]

/-- `pyRange n` (default start 0, step 1) is `List.range n.toNat` cast to `Int`. -/
theorem pyRange_eq_ofNat (n : Int) : pyRange n = (List.range n.toNat).map Int.ofNat := by
  unfold pyRange
  simp only [gt_iff_lt, List.range_eq_range', show (Int.toNat 1) = 1 from rfl, Int.ediv_one,
    Int.emod_one, Int.add_zero, Int.sub_zero, if_pos (show (0 : Int) < 1 by norm_num)]
  rw [← coe_list_eq]; simp

/-- **The reduction spec.** A `pyRange n` loop equals the native `List.range n.toNat` loop with the
`Int` cast pushed into the body. Pass to mvcgen so index-style invariants close as they do for
`List.range`. -/
@[taste_ingr] theorem pyRange_forIn {β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (n : Int) (init : β) (f : Int → β → m (ForInStep β)) :
    forIn (pyRange n) init f = forIn (List.range n.toNat) init (fun (k : Nat) => f (Int.ofNat k)) := by
  rw [pyRange_eq_ofNat, List.forIn_map]

/-- `pyRange stop start` (Python `range(start, stop)`, step 1) is `[start, …, stop-1]` as `Int`. -/
theorem pyRange_eq_start (stop start : Int) :
    pyRange stop start = (List.range (stop - start).toNat).map (fun k => start + Int.ofNat k) := by
  unfold pyRange
  simp only [gt_iff_lt, List.range_eq_range', show (Int.toNat 1) = 1 from rfl, Int.ediv_one,
    Int.emod_one, Int.add_zero, if_pos (show (0 : Int) < 1 by norm_num)]
  rw [coe_list_eq, List.map_map]; rfl

/-- Start-aware reduction: a `for i in range(start, stop)` loop becomes the native `List.range` loop
with the element `start + index` in the body, so mvcgen knows `i ≥ start`. -/
@[taste_ingr] theorem pyRange_forIn_start {β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (stop start : Int) (init : β) (f : Int → β → m (ForInStep β)) :
    forIn (pyRange stop start) init f
      = forIn (List.range (stop - start).toNat) init (fun (k : Nat) => f (start + Int.ofNat k)) := by
  rw [pyRange_eq_start, List.forIn_map]

/-- Python `x ** 2` lowers to `x ^ₚ (2 : Int)` (the `PyHPow Int Int Int` instance). `taste?`'s
closers (`positivity`/`nlinarith`) don't see through the `^ₚ` notation, so normalise it to the plain
`x ^ 2` monoid power — then `positivity` recognises the even power as nonnegative. Squares dominate
the contract goals (sum-of-squares, variance); higher powers can get their own reductions as needed. -/
@[taste_ingr] theorem pyHPow_two (a : Int) : a ^ₚ (2 : Int) = a ^ 2 := rfl

/-!
## `while` loops — `pyWhile` + the while rule

A Python `while` lowers, via core `while … do`, to `Loop.forIn` → the **`partial` `whileM`** fixpoint:
opaque, with no usable equation lemma, so nothing can be proved about it directly. The fix mirrors
`pyRange`/`pyRange_forIn`: a *total*, reasoned-about combinator (`pyWhile`) plus one Hoare rule
(`pyWhile_correct`). The verification def emits `pyWhile`; the runnable `'rn` twin keeps real `while`.
-/

/-- **The while rule.** If the invariant `I` holds initially, is preserved by `body` whenever the guard
holds *and* the measure `μ` strictly decreases there, and implies `Q` once the guard fails, then `Q`
holds of the loop result. The measure decrease is what makes `pyWhile` reach its exit within fuel.
Maps the contract markers directly: `Invariant → I`, `Decreases → μ`, loop test → `c`, post → `Q`. -/
theorem pyWhile_correct {σ : Type} {I Q : σ → Prop} (μ : σ → Nat) (c : σ → Bool) (body : σ → σ)
    (s₀ : σ) (hpre : I s₀)
    (hstep : ∀ s, I s → c s = true → I (body s) ∧ μ (body s) < μ s)
    (hexit : ∀ s, I s → c s = false → Q s) :
    Q (pyWhile μ c body s₀) := by
  -- Generalise over any fuel ≥ μ s and induct on it.
  suffices h : ∀ fuel s, I s → μ s ≤ fuel → Q (pyWhileFuel c body fuel s) from
    h (μ s₀) s₀ hpre (le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro s hI hμ
    cases hcs : c s with
    | false => exact hexit s hI hcs
    | true => obtain ⟨_, hdec⟩ := hstep s hI hcs; exfalso; omega
  | succ n ih =>
    intro s hI hμ
    cases hcs : c s with
    | false => simpa [pyWhileFuel, hcs] using hexit s hI hcs
    | true =>
      obtain ⟨hIb, hdec⟩ := hstep s hI hcs
      simp only [pyWhileFuel, hcs, if_true]
      exact ih (body s) hIb (by omega)

end PastaLean
