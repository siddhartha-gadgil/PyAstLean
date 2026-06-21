import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def modulo := fun a ↦ a %ₚ (5 : Int)

def modulo'rn := fun a ↦ a %ₚ (5 : Int)
