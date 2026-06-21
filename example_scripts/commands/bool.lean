import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def func := fun a ↦ fun b ↦ fun c ↦ a && b && c || a && b

def func'rn := fun a ↦ fun b ↦ fun c ↦ a && b && c || a && b
