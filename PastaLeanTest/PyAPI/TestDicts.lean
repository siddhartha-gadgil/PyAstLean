import PastaLean.PyAPI.Dicts
import PastaLean.PyAPI.CommonProtocols.Length

open PastaLean

private def sortStrings (xs : List String) : List String :=
  xs.mergeSort (fun a b => compare a b != Ordering.gt)

private def sortInts (xs : List Int) : List Int :=
  xs.mergeSort (fun a b => compare a b != Ordering.gt)

private def itemStrings (m : Std.HashMap String Int) : List String :=
  sortStrings <| (pyItems m).map (fun (k, v) => s!"{k}={v}")

/-- info: ["a=1", "b=2", "c=3"] -/
#guard_msgs in
#eval itemStrings <| Std.HashMap.ofList [("b", 2), ("a", 1), ("c", 3)]

/-- info: ["ant", "bee", "cat"] -/
#guard_msgs in
#eval sortStrings <| pyKeys (Std.HashMap.ofList [("bee", 2), ("cat", 3), ("ant", 1)])

/-- info: [10, 20, 30] -/
#guard_msgs in
#eval sortInts <| pyValues (Std.HashMap.ofList [("x", 30), ("y", 10), ("z", 20)])

/-- info: 0 -/
#guard_msgs in
#eval pyLen (pyDictClear (Std.HashMap.ofList [("x", 1), ("y", 2)] : Std.HashMap String Int))

/-- info: (some 2, ["a=1"]) -/
#guard_msgs in
#eval
  let popped := pyDictPop (Std.HashMap.ofList [("a", 1), ("b", 2)] : Std.HashMap String Int) "b"
  (popped.1, itemStrings popped.2)

/-- info: (some 99, ["a=1"]) -/
#guard_msgs in
#eval
  let popped := pyDictPop (Std.HashMap.ofList [("a", 1)] : Std.HashMap String Int) "missing" (some 99)
  (popped.1, itemStrings popped.2)

/-- info: ["left=1", "right=2", "up=3"] -/
#guard_msgs in
#eval itemStrings <| pyUpdate (Std.HashMap.ofList [("left", 1)] : Std.HashMap String Int) [("right", 2), ("up", 3)]

/-- info: some 10 -/
#guard_msgs in
#eval pyGetOpt? (Std.HashMap.ofList [("apple", 10), ("banana", 20)] : Std.HashMap String Int) "apple"

/-- info: none -/
#guard_msgs in
#eval pyGetOpt? (Std.HashMap.ofList [("apple", 10), ("banana", 20)] : Std.HashMap String Int) "pear"

/-- info: 20 -/
#guard_msgs in
#eval pyGetD (Std.HashMap.ofList [("apple", 10), ("banana", 20)] : Std.HashMap String Int) "banana" 999

/-- info: 999 -/
#guard_msgs in
#eval pyGetD (Std.HashMap.ofList [("apple", 10), ("banana", 20)] : Std.HashMap String Int) "pear" 999
