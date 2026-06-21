import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def f := fun n ↦ n -ₚ -n

def f'rn := fun n ↦ n -ₚ -n
