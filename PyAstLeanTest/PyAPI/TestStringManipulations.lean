import PyAstLean.PyAPI.Core

open PyAstLean

/-- Helper to repeat a string for testing purposes. -/
def repeatStr (s : String) (n : Int) : String :=
  if n <= 0 then "" 
  else String.join (List.replicate n.toNat s)

/-- 
  Lean equivalent to:
  def foo():
      x = "hi"
      y = x[0]
      y *= 10
      z = y[2:-3]
      return z
-/
def foo : String :=
  let x := "hi"
  -- x[0]
  let y_char := match pyStringGetItem x 0 with | some c => c.toString | none => ""
  -- y *= 10
  let y := repeatStr y_char 10
  -- y[2:-3]
  let z := pyStringSlice y (some 2) (some (-3))
  z

/-- info: "hhhhh" -/
#guard_msgs in
#eval foo

/-- info: "h" -/
#guard_msgs in
#eval pyStringGetItem "hi" 0 |>.map (fun c => c.toString) |>.getD ""

/-- info: "hi" -/
#guard_msgs in
#eval pyStringSlice "hi" (some 0) (some 2)
