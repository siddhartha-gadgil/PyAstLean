import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def sum_to_n := fun n ↦
  Id.run
    (do
      let mut total := (0 : Int)
      let mut i := (1 : Int)
      while (decide (i ≤ n)) do
        total := total +ₚ i
        i := i +ₚ (1 : Int)
      return total)

def sum_to_n'rn := fun n ↦
  Id.run
    (do
      let mut total := (0 : Int)
      let mut i := (1 : Int)
      while (decide (i ≤ n)) do
        total := total +ₚ i
        i := i +ₚ (1 : Int)
      return total)
