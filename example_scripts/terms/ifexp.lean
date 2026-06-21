import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def l :=
  if decide ((2 : Int) > (3 : Int)) then (2 : Int) else (3 : Int)
