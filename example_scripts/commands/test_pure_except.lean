import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

-- !/usr/bin/env python3
/-
Test that pure exceptions (no IO) use PyExceptId in prove mode.
-/
-- CHECK: def validate : Int → PyExceptId Int
def validate : Int → PastaLean.PyExceptId Int := fun (x : Int) ↦ do
  if h_1 : x < (0 : Int) then
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  else
    let _ := ()
  let __py_ret_1 := x *ₚ (2 : Int)
  return __py_ret_1

-- CHECK: def validate_with_print : Int → PyExceptId Int
def validate_with_print : Int → PastaLean.PyExceptId Int := fun (x : Int) ↦ do
  let _ ← pyPrintNoop [pyPrintArg x]
  if h_1 : x < (0 : Int) then
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  else
    let _ := ()
  let __py_ret_1 := x *ₚ (2 : Int)
  return __py_ret_1

def validate_spec : ⦃⌜ n ≥ 0 ⌝⦄ validate n ⦃post⟨fun v => ⌜ v = 2 * n ⌝, fun _ => ⌜ False ⌝⟩⦄ := by
  mvcgen [validate] with grind [pyMul_int]
