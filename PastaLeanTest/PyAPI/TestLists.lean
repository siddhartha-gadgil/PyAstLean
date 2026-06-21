import PastaLean.PyAPI.Lists

open PastaLean

/-- info: [1, 2, 3, 4] -/
#guard_msgs in
#eval pyAppend [1, 2, 3] 4

/-- info: ["solo"] -/
#guard_msgs in
#eval pyAppend [] "solo"

/-- info: [1, 2, 3, 4, 5] -/
#guard_msgs in
#eval pyExtend [1, 2] [3, 4, 5]

/-- info: [1, 2] -/
#guard_msgs in
#eval pyExtend [1, 2] []

/-- info: (some 30, [10, 20, 40]) -/
#guard_msgs in
#eval pyListPop [10, 20, 30, 40] 2

/-- info: (some 99, [7, 8]) -/
#guard_msgs in
#eval pyListPop [7, 8] 5 (some 99)

/-- info: 1 -/
#guard_msgs in
#eval pyListIndex ["red", "blue", "green"] "blue"

/-- info: 3 -/
#guard_msgs in
#eval pyListCount [1, 2, 2, 3, 2] 2

/-- info: 0 -/
#guard_msgs in
#eval pyListCount ["a", "b"] "z"

/-- info: [4, 3, 2, 1] -/
#guard_msgs in
#eval pyReverse [1, 2, 3, 4]

/-- info: [] -/
#guard_msgs in
#eval pyReverse ([] : List Int)

/-- info: [] -/
#guard_msgs in
#eval pyListClear [1, 2, 3]

/-- info: ["x"] -/
#guard_msgs in
#eval pyInsert [] 0 "x"

/-- info: [1, 99, 2, 3] -/
#guard_msgs in
#eval pyInsert [1, 2, 3] 1 99

/-- info: [42, 1, 2, 3] -/
#guard_msgs in
#eval pyInsert [1, 2, 3] (-5) 42

/-- info: [1, 2, 3, 42] -/
#guard_msgs in
#eval pyInsert [1, 2, 3] 99 42
