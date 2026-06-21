import PastaLean.PyAPI.Builtins
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.Operators
import Libraries.functools.FunctoolsDef

open PastaLean

/-- info: [2, 3, 4] -/
#guard_msgs in
#eval pyMap (fun x : Int => x +ₚ (1 : Int)) ([1, 2, 3] : List Int)

/-- info: "ABC" -/
#guard_msgs in
#eval String.join <| pyMap (fun c : String => c.toUpper) "abc"

/-- info: [2, 4] -/
#guard_msgs in
#eval pyFilter (fun x : Int => x %ₚ (2 : Int) == (0 : Int)) ([1, 2, 3, 4] : List Int)

/-- info: ["a", "c"] -/
#guard_msgs in
#eval pyFilter (fun x : String => x != "b") (["a", "b", "c"] : List String)

/-- info: [(1, 10), (2, 20)] -/
#guard_msgs in
#eval pyZip ([1, 2, 3] : List Int) ([10, 20] : List Int)

/-- info: [("a", 1), ("b", 2)] -/
#guard_msgs in
#eval pyZip "ab" ([1, 2, 3] : List Int)

/-- info: [(0, "x"), (1, "y")] -/
#guard_msgs in
#eval pyEnumerate (["x", "y"] : List String)

/-- info: [(5, "c"), (6, "a"), (7, "b")] -/
#guard_msgs in
#eval pyEnumerate "cab" 5

/-- info: 10 -/
#guard_msgs in
#eval pySum ([1, 2, 3, 4] : List Int)

/-- info: 20 -/
#guard_msgs in
#eval pySum ([1, 2, 3, 4] : List Int) (10 : Int)

/-- info: 1 -/
#guard_msgs in
#eval pyMin ([3, 1, 4, 2])

/-- info: "a" -/
#guard_msgs in
#eval pyMin "cab"

/-- info: 9 -/
#guard_msgs in
#eval pyMax ([3, 1, 9, 2] : List Int)

/-- info: "z" -/
#guard_msgs in
#eval pyMax "ayz"

/-- info: 16 -/
#guard_msgs in
#eval Libraries.functools.pyReduce ([1, 2, 3] : List Int) (fun acc x : Int => acc +ₚ x) (some (10 : Int))

/-- info: 6 -/
#guard_msgs in
#eval Libraries.functools.pyReduce ([1, 2, 3] : List Int) (fun a b : Int => a +ₚ b)

/-- info: ["a", "b"] -/
#guard_msgs in
#eval pyMap (fun s : String => s) (Std.HashMap.ofList [("b", 1), ("a", 2)] : Std.HashMap String Int) |>.mergeSort (fun a b => compare a b != Ordering.gt)
