import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def f := fun x ↦ fun y ↦ (3 : Int) *ₚ x +ₚ (2 : Int) *ₚ y
