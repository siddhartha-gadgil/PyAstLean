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
  Id.run
    (do
      let mut result := (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        result := result *ₚ i
      return result)

attribute [simp, taste_ingr] factorial

def factorial'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut result := (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        result := result *ₚ i
      return result)
