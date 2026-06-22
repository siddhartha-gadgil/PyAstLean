import PastaLean
import Libraries

open PastaLean
open Libraries

set_option linter.all false

partial def fibonacci : Int → Int := fun (n : Int) ↦
  if decide (n ≤ (0 : Int)) then (0 : Int)
  else if n == (1 : Int) then (1 : Int) else fibonacci (n -ₚ (1 : Int)) +ₚ fibonacci (n -ₚ (2 : Int))

partial def fibonacci'rn : Int → Int := fun (n : Int) ↦
  if decide (n ≤ (0 : Int)) then (0 : Int)
  else if n == (1 : Int) then (1 : Int) else fibonacci'rn (n -ₚ (1 : Int)) +ₚ fibonacci'rn (n -ₚ (2 : Int))

def funnyfoo := fun (x : Int) ↦ (x *ₚ x +ₚ x) ^ₚ x

def funnyfoo'rn := fun (x : Int) ↦ (x *ₚ x +ₚ x) ^ₚ x
