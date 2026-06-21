import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def l :=
  if decide ((2 : Int) > (3 : Int)) then (2 : Int) else (3 : Int)
