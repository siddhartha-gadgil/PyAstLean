import PyAstLean

namespace Libraries.numpy

#guard_msgs in
#eval pyNumpySum [[1, 2], [3, 4]]

#guard_msgs in
#eval pyNumpyMean [[1, 2], [3, 4]]

#guard_msgs in
#eval pyNumpyTrace [[1, 2], [3, 4]]

#guard_msgs in
#eval pyNumpyDot [1, 2, 3] [4, 5, 6]

#eval pyNumpyArray [[1, 2], [3, 4]]
#eval pyNumpyZeros (2, 3)
#eval pyNumpyOnes (2, 2)
#eval pyNumpyEye 3
#eval pyNumpyTranspose [[1, 2], [3, 4]]
#eval pyNumpyAdd [[1, 2], [3, 4]] [[5, 6], [7, 8]]
#eval pyNumpySubtract [[5, 6], [7, 8]] [[1, 2], [3, 4]]
#eval pyNumpyMultiply [[1, 2], [3, 4]] [[5, 6], [7, 8]]
#eval pyNumpyScale 2 [[1, 2], [3, 4]]
#eval pyNumpyMatmul [[1, 2], [3, 4]] [[5, 6], [7, 8]]
#eval pyNumpyFlatten [[1, 2], [3, 4]]

end Libraries.numpy
