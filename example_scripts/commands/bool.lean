import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def func := fun a ↦ fun b ↦ fun c ↦ a && b && c || a && b

def func'rn := fun a ↦ fun b ↦ fun c ↦ a && b && c || a && b
