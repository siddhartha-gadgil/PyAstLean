import PastaLean.PyAPI.Builtins.Casting

open PastaLean

/-- info: 42 -/
#guard_msgs in
#eval pyInt "42"

/-- info: -7 -/
#guard_msgs in
#eval pyInt "  -7  "

/-- info: 1 -/
#guard_msgs in
#eval pyInt true

/-- info: 0 -/
#guard_msgs in
#eval pyInt "oops"

-- `float(str)` must actually parse decimals (a stub once returned 0.0 for everything but
-- inf/nan, silently breaking `float(input())`). Only exact-in-binary values are guarded.
#guard pyFloat "2.75" == (2.75 : Float)
#guard pyFloat "  -0.5 " == (-0.5 : Float)
#guard pyFloat "10" == (10.0 : Float)
#guard pyFloat "oops" == (0.0 : Float)

/-- info: "[1, 2, 3]" -/
#guard_msgs in
#eval pyStr ([1, 2, 3] : List Int)

/-- info: "True" -/
#guard_msgs in
#eval pyStr true

/-- info: "None" -/
#guard_msgs in
#eval pyStr (none : Option Int)

/-- info: ["a", "b", "c"] -/
#guard_msgs in
#eval pyList "abc"

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval pyList ([1, 2, 3] : List Int)

/-- info: [1, 2] -/
#guard_msgs in
#eval pyList ((1, 2) : Int × Int)
