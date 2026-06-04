import Std.Tactic.Do

open Std Do

set_option mvcgen.warning false

def mySum (arr : Array Nat) : Nat := Id.run do
  let mut total := 0
  for x in arr do
    total := total + x
  return total

theorem mySum_correct (arr : Array Nat) : mySum arr = arr.sum := by
  generalize h : mySum arr = x
  apply Id.of_wp_run_eq h
  mvcgen
  · exact Classical.ofNonempty
  · sorry
  · simp_all [mySum]
    sorry
  · simp_all [mySum]
    sorry
