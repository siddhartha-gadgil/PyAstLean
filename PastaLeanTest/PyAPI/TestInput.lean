import PastaLean.PyAPI.Input

open PastaLean

/-- info: 42 -/
#guard_msgs in
#eval pyInt "42"

/-- info: -7 -/
#guard_msgs in
#eval pyInt "  -7  "

/-- info: 5 -/
#guard_msgs in
#eval pyInt (5 : Int)

/-- info: 1 -/
#guard_msgs in
#eval pyInt true

/-- info: 0 -/
#guard_msgs in
#eval pyInt "oops"
