import PastaLean.PyAPI.PyPrint

open PastaLean

/-- info: "hello" -/
#guard_msgs in
#eval pyPrintStr "hello"

/-- info: "True" -/
#guard_msgs in
#eval pyPrintStr true

/-- info: "None" -/
#guard_msgs in
#eval pyPrintStr (none : Option Int)

/-- info: "[1, 2, 3]" -/
#guard_msgs in
#eval pyPrintStr ([1, 2, 3] : List Int)

/-- info: "(7, ok)" -/
#guard_msgs in
#eval pyPrintStr ((7 : Int), "ok")

/-- info: "{a: 1, b: 2}" -/
#guard_msgs in
#eval pyPrintStr (Std.HashMap.ofList [("b", 2), ("a", 1)] : Std.HashMap String Int)

/-- info: "<function>" -/
#guard_msgs in
#eval pyPrintStr (fun x : Int => x + 1)

/-- info: "[a, b, c]" -/
#guard_msgs in
#eval pyPrintStr (['a', 'b', 'c'] : List Char)

/-- info: print me -/
#guard_msgs in
#eval pyPrintIO ["print me"]

/-- info: alpha 3 True -/
#guard_msgs in
#eval pyPrintIO ["alpha", (3 : Int), true]

/-- info: left|right! -/
#guard_msgs in
#eval pyPrintIO ["left", "right"] "|" "!"

/-- info: sum 3 4 -/
#guard_msgs in
#eval pyPrintIO ["sum", (3 : Int), (4 : Int)]

/--
info: [4, 5]
---
info: 9
-/
#guard_msgs in
#eval (pyPrintIO [[4, 5]] *> pure (9 : Int))
