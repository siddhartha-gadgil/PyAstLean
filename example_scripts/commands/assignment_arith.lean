import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def f := fun n ↦
  let x := n +ₚ (1 : Int)
  let y := x *ₚ (2 : Int)
  let x := y -ₚ (1 : Int)
  x +ₚ y

def f'rn := fun n ↦
  let x := n +ₚ (1 : Int)
  let y := x *ₚ (2 : Int)
  let x := y -ₚ (1 : Int)
  x +ₚ y
