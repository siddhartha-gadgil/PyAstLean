import PastaLean
import Libraries

open PastaLean
open Libraries

set_option linter.all false

-- !/usr/bin/env python3
/-
Test that exceptions with real IO use PyExcept.
-/
-- CHECK: def get_validated : PyExcept Int
def get_validated : PastaLean.PyExcept Int := do
  let mut x := PastaLean.pyInt (← PastaLean.pyInputIO "")
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  else
    let _ := ()
  return x
