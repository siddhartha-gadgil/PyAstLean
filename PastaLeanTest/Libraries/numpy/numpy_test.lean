import PastaLean

namespace Libraries.numpy

/-- info: 10.000000 -/
#guard_msgs in
#eval pyNumpySum [[1, 2], [3, 4]]

/-- info: 2.500000 -/
#guard_msgs in
#eval pyNumpyMean [[1, 2], [3, 4]]

/-- info: 5.000000 -/
#guard_msgs in
#eval pyNumpyTrace [[1, 2], [3, 4]]

/-- info: 32.000000 -/
#guard_msgs in
#eval pyNumpyDot [1, 2, 3] [4, 5, 6]

/-- info: [[1.000000, 2.000000], [3.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpyArray [[1, 2], [3, 4]]

/-- info: [[0.000000, 0.000000, 0.000000], [0.000000, 0.000000, 0.000000]] -/
#guard_msgs in
#eval pyNumpyZeros (2, 3)

/-- info: [[1.000000, 1.000000], [1.000000, 1.000000]] -/
#guard_msgs in
#eval pyNumpyOnes (2, 2)

/--
info: [[1.000000, 0.000000, 0.000000], [0.000000, 1.000000, 0.000000], [0.000000, 0.000000, 1.000000]]
-/
#guard_msgs in
#eval pyNumpyEye 3

/-- info: [[1.000000, 3.000000], [2.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpyTranspose [[1, 2], [3, 4]]

/-- info: [[6.000000, 8.000000], [10.000000, 12.000000]] -/
#guard_msgs in
#eval pyNumpyAdd [[1, 2], [3, 4]] [[5, 6], [7, 8]]

/-- info: [[4.000000, 4.000000], [4.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpySubtract [[5, 6], [7, 8]] [[1, 2], [3, 4]]

/-- info: [[5.000000, 12.000000], [21.000000, 32.000000]] -/
#guard_msgs in
#eval pyNumpyMultiply [[1, 2], [3, 4]] [[5, 6], [7, 8]]

/-- info: [[2.000000, 4.000000], [6.000000, 8.000000]] -/
#guard_msgs in
#eval pyNumpyScale 2 [[1, 2], [3, 4]]

/-- info: [[19.000000, 22.000000], [43.000000, 50.000000]] -/
#guard_msgs in
#eval pyNumpyMatmul [[1, 2], [3, 4]] [[5, 6], [7, 8]]

/-- info: [1.000000, 2.000000, 3.000000, 4.000000] -/
#guard_msgs in
#eval pyNumpyFlatten [[1, 2], [3, 4]]

end Libraries.numpy
