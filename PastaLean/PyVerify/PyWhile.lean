import Mathlib

/-!
# `pyWhile` — the total `while` combinator, its Hoare rule, and the `while → for` bridge

A Python `while` lowers, via core `while … do`, to `Loop.forIn` → the **`partial` `whileM`** fixpoint:
opaque, with no usable equation lemma, so nothing can be proved about it directly. The fix mirrors
`pyRange`/`pyRange_forIn`: a *total*, reasoned-about combinator (`pyWhile`) plus lemmas. The
verification def emits `pyWhile`; the runnable `'rn` twin keeps a real `while`.

This file holds everything about `pyWhile`:
* `pyWhileFuel` / `pyWhile` — the total combinator (fuel-bounded, structural recursion);
* `pyWhile_correct` — the Hoare while rule (`Invariant → I`, `Decreases → μ`, test → `c`, post → `Q`);
* `pyWhile_count` — the **bridge**: a counting `while` over `(acc, i)` equals the range fold that
  `for i in range(start, stop)` computes. This machine-checks the `while → for` normalization
  (`src/normalize_loops.py`): the two loop encodings denote the same value.
-/

namespace PastaLean

/-- Fuel-bounded loop: structurally recursive on `fuel`, hence total. Internal to `pyWhile`. -/
def pyWhileFuel {σ : Type} (c : σ → Bool) (body : σ → σ) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => if c s then pyWhileFuel c body n (body s) else s

/-- Python `while c: body` as a TOTAL function: iterate `body` while the guard `c` holds, with `μ` the
termination measure bounding the iteration count. (`for`'s collection is its own variant; an unbounded
`while` needs `μ` supplied — that is what the `Decreases(...)` contract provides.) The verification
def emits this; the runnable `'rn` twin keeps a real `while`. -/
def pyWhile {σ : Type} (μ : σ → Nat) (c : σ → Bool) (body : σ → σ) (s : σ) : σ :=
  pyWhileFuel c body (μ s) s

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

/-! ## The `while → for` bridge -/

/-- Peel the first index off a `range (n+1)` left fold. -/
theorem foldl_range_succ_shift {α : Type} (g : Nat → α → α) (n : Nat) (a0 : α) :
    (List.range (n + 1)).foldl (fun a k => g k a) a0
      = (List.range n).foldl (fun a k => g (k + 1) a) (g 0 a0) := by
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-- Run form: a counting `while` over `(acc, i)` — guard `i < stop`, body `(f i acc, i+1)` — given
`start + N = stop` (exactly `N` iterations remain), folds `f` over the counter values
`start, start+1, …, start+N-1`. Induct on `N` (the iteration count) so the range is `List.range N`. -/
theorem pyWhileFuel_run {α : Type} (f : Int → α → α) (stop : Int) :
    ∀ (N : Nat) (start : Int) (a0 : α), start + (N : Int) = stop →
      (pyWhileFuel (fun s => decide (s.2 < stop)) (fun s => (f s.2 s.1, s.2 + 1)) N (a0, start)).1
        = (List.range N).foldl (fun (a : α) (k : Nat) => f (start + (k : Int)) a) a0 := by
  intro N
  induction N with
  | zero => intro start a0 _; simp [pyWhileFuel]
  | succ n ih =>
    intro start a0 hEq
    have hlt : start < stop := by
      have : (0 : Int) < (n : Int) + 1 := by positivity
      omega
    have hc : decide ((a0, start).2 < stop) = true := by simp [hlt]
    have hstep :
        (pyWhileFuel (fun s => decide (s.2 < stop)) (fun s => (f s.2 s.1, s.2 + 1)) (n + 1) (a0, start)).1
          = (pyWhileFuel (fun s => decide (s.2 < stop)) (fun s => (f s.2 s.1, s.2 + 1)) n
              (f start a0, start + 1)).1 := by
      simp [pyWhileFuel, hc]
    have hEq' : (start + 1) + (n : Int) = stop := by push_cast at hEq ⊢; omega
    rw [hstep, ih (start + 1) (f start a0) hEq']
    simp only [foldl_range_succ_shift, Nat.cast_zero, add_zero]
    have hf : ∀ (k : Nat), start + 1 + (k : Int) = start + ((k + 1 : Nat) : Int) := by
      intro k; push_cast; ring
    simp only [hf]

/-- **The bridge.** The accumulator result of the counting `pyWhile` equals the range fold — exactly
what a `for i in range(start, stop)` loop computes. Certifies the `while → for` normalization: the two
loop encodings denote the same value. -/
theorem pyWhile_count {α : Type} (stop : Int) (f : Int → α → α) (start : Int) (a0 : α) :
    (pyWhile (fun s => (stop - s.2).toNat) (fun s => decide (s.2 < stop))
             (fun s => (f s.2 s.1, s.2 + 1)) (a0, start)).1
      = (List.range (stop - start).toNat).foldl (fun (a : α) (k : Nat) => f (start + (k : Int)) a) a0 := by
  show (pyWhileFuel _ _ ((stop - start).toNat) (a0, start)).1 = _
  by_cases h : start ≤ stop
  · exact pyWhileFuel_run f stop (stop - start).toNat start a0 (by omega)
  · have h0 : (stop - start).toNat = 0 := by omega
    rw [h0]
    simp [pyWhileFuel]

end PastaLean
