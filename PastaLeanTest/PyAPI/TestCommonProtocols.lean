import PastaLean.PyAPI.CommonProtocols.Length
import PastaLean.PyAPI.CommonProtocols.Membership
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.CommonProtocols.Clear
import PastaLean.PyAPI.CommonProtocols.Pop
import PastaLean.PyAPI.CommonProtocols.Sorting
import PastaLean.PyAPI.CommonProtocols.Reversed

open PastaLean

private def sortStrings (xs : List String) : List String :=
  xs.mergeSort (fun a b => compare a b != Ordering.gt)

/-- info: 4 -/
#guard_msgs in
#eval pyLen [1, 2, 3, 4]

/-- info: 5 -/
#guard_msgs in
#eval pyLen "hello"

/-- info: 2 -/
#guard_msgs in
#eval pyLen (Std.HashMap.ofList [("a", 1), ("b", 2)] : Std.HashMap String Int)

/-- info: true -/
#guard_msgs in
#eval pyContains ([1, 2, 3] : List Nat) (2 : Nat)

/-- info: false -/
#guard_msgs in
#eval pyContains ([1, 2, 3] : List Nat) (9 : Nat)

/-- info: true -/
#guard_msgs in
#eval pyContains "analytics" "a"

/-- info: false -/
#guard_msgs in
#eval pyContains "analytics" "z"

/-- info: true -/
#guard_msgs in
#eval pyContains (Std.HashMap.ofList [("x", 1), ("y", 2)] : Std.HashMap String Int) "x"

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval pyIter [1, 2, 3]

/-- info: "abc" -/
#guard_msgs in
#eval String.join <| pyIter "abc"

/-- info: [] -/
#guard_msgs in
#eval pyClear [1, 2, 3]

/-- info: 0 -/
#guard_msgs in
#eval pyLen (pyClear (Std.HashMap.ofList [("k", 1)] : Std.HashMap String Int))

/-- info: (some 2, [1, 3]) -/
#guard_msgs in
#eval pyPop ([1, 2, 3] : List Int) (1 : Int)

/-- info: (some 50, [4, 5]) -/
#guard_msgs in
#eval pyPop ([4, 5] : List Int) (99 : Int) (some (50 : Int))

/-- info: (some 7, ["a"]) -/
#guard_msgs in
#eval
  let popped := pyPop (Std.HashMap.ofList [("a", 1), ("b", 7)] : Std.HashMap String Int) "b"
  (popped.1, sortStrings <| pyKeys popped.2)

/-- info: [1, 1, 3, 4, 5] -/
#guard_msgs in
#eval pySort [3, 1, 4, 1, 5]

/-- info: "abc" -/
#guard_msgs in
#eval String.join <| pySort "cba"

/-- info: ["a", "m", "z"] -/
#guard_msgs in
#eval pySort (Std.HashMap.ofList [("z", 1), ("a", 2), ("m", 3)] : Std.HashMap String Int)

/-- info: [2, 9] -/
#guard_msgs in
#eval pySort ((9, 2) : Int × Int)

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval pyIter (pyReversed ([1, 2, 3] : List Int))

/-- info: "cba" -/
#guard_msgs in
#eval String.join <| pyIter (pyReversed "abc")

/-- info: 13 -/
#guard_msgs in
#eval do
  let x := pyLen ([1, 2, 3] : List Nat)
  pure (x + 10)

/-- info: "count=3" -/
#guard_msgs in
#eval do
  let x := pyLen (Std.HashMap.ofList [("red", 1), ("green", 2), ("blue", 3)] : Std.HashMap String Int)
  pure s!"count={x}"

/-- info: [1, 2, 4, 7] -/
#guard_msgs in
#eval do
  let x := pySort ([7, 1, 4, 2] : List Int)
  pure x

/-- info: "abcd" -/
#guard_msgs in
#eval do
  let x := pySort "dbca"
  pure (String.join x)

/-- info: ("size=3", [1, 3, 5]) -/
#guard_msgs in
#eval do
  let sorted := pySort ([5, 1, 3] : List Int)
  let size := pyLen sorted
  pure (s!"size={size}", sorted)
