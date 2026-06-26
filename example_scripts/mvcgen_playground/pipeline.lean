import Std.Tactic.Do

open Std.Do


def massert {m : Type → Type} [Monad m] (_p : Prop) : m Unit := pure ()

@[spec]
theorem assertM_spec_Id (p : Prop) :
  ⦃⌜p⌝⦄ (massert (m := Id) p) ⦃⇓ _ => ⌜p⌝⦄ := by
  mvcgen [massert] with grind

@[spec]
theorem assertM_spec_StateM {σ : Type} (p : Prop) :
  ⦃⌜p⌝⦄ (massert (m := StateM σ) p) ⦃⇓ _ => ⌜p⌝⦄ := by
  mvcgen [massert] with grind

def pipeline (xs : List Int) : Id Int := do
  let mut acc := 0
  for x in xs do
      acc := acc + x
  massert (acc = xs.sum)
  acc := acc * 2
  let mut cnt := 0
  for _ in xs do
      cnt := cnt + 1
  massert (cnt = xs.length)
  let result := acc + cnt
  massert (result = 2 * xs.sum + xs.length)
  return result

theorem pipeline_correct : (Id.run (pipeline l)) = 2 * l.sum + l.length:= by
  generalize h : (pipeline l).run = x
  apply Id.of_wp_run_eq h
  mvcgen [pipeline] invariants
    · ⇓⟨x, y⟩ => ⌜y = x.prefix.sum⌝
    · ⇓⟨x, y⟩ => ⌜y = x.prefix.length⌝
  with grind
