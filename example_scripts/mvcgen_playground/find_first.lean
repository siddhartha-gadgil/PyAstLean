import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- Early-return linear search (mirrors early_return_break.lean): return the first index whose value
-- equals k, or -1. The loop invariant is "k absent from the prefix scanned so far".
def find_first := fun (xs : List Int) ↦ fun (k : Int) ↦
  (do
    for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
      let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
      if h_1 : xs⦋i⦌ = k then 
        return i
      else
        let _ := ()
    let __py_ret_1 := -(1 : Int)
    return __py_ret_1 : Id _)

theorem find_first_spec : ⦃⌜True⌝⦄ find_first xs k ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [find_first, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · Invariant.withEarlyReturn (onReturn := fun _ _ => ⌜True⌝) (onContinue := fun _ _ => ⌜True⌝)
  simp_all (config := { zetaDelta := true }) [taste_ingr]; simp_all (config := { zetaDelta := true }) [taste_ingr]; simp_all (config := { zetaDelta := true }) [taste_ingr]

def find_first'rn := fun (xs : List Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
        if h_1 : xs⦋i⦌ == k then 
          return i
        else
          let _ := ()
      let __py_ret_1 := -(1 : Int)
      return __py_ret_1)
