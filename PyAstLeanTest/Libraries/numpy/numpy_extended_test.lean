import PyAstLean

namespace Libraries.numpy

-- ==================== Creation & Initialization ====================

/-- info: [[5.000000, 5.000000, 5.000000], [5.000000, 5.000000, 5.000000]] -/
#guard_msgs in
#eval pyNumpyFull (2, 3) 5

/-- info: [0.000000, 2.500000, 5.000000, 7.500000, 10.000000] -/
#guard_msgs in
#eval pyNumpyLinspace 0.0 10.0 5

/-- info: [[1.000000, 2.000000], [3.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpyReshape [[1, 2, 3, 4]] (2, 2)

/-- info: [[1.000000, 2.000000, 3.000000]] -/
#guard_msgs in
#eval pyNumpyExpandDims 0 [1.0, 2.0, 3.0]

/-- info: [[1.000000], [2.000000], [3.000000]] -/
#guard_msgs in
#eval pyNumpyExpandDims 1 [1.0, 2.0, 3.0]

/-- info: [1.000000, 2.000000, 3.000000] -/
#guard_msgs in
#eval pyNumpySqueeze [[1.0, 2.0, 3.0]]

/-- info: [[1.000000, 2.000000], [3.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpyVstack [[1.0, 2.0]] [[3.0, 4.0]]

/-- info: [[1.000000, 3.000000], [2.000000, 4.000000]] -/
#guard_msgs in
#eval pyNumpyHstack [[1.0], [2.0]] [[3.0], [4.0]]

-- ==================== Reduction & Statistics ====================

/-- info: 10.000000 -/
#guard_msgs in
#eval pyNumpySumVec [1, 2, 3, 4]

/-- info: 5.000000 -/
#guard_msgs in
#eval pyNumpyMeanVec [2, 4, 6, 8]

/-- info: 1.000000 -/
#guard_msgs in
#eval pyNumpyMin [5, 2, 8, 1, 9]

/-- info: 9.000000 -/
#guard_msgs in
#eval pyNumpyMax [5, 2, 8, 1, 9]

/-- info: 3 -/
#guard_msgs in
#eval pyNumpyArgmin [5, 2, 8, 1, 9]

/-- info: 4 -/
#guard_msgs in
#eval pyNumpyArgmax [5, 2, 8, 1, 9]

/-- info: 2.000000 -/
#guard_msgs in
#eval pyNumpyMedian [3, 1, 2]

/-- info: 2.500000 -/
#guard_msgs in
#eval pyNumpyMedian [1, 2, 3, 4]

/-- info: 2.000000 -/
#guard_msgs in
#eval pyNumpyVar [1, 2, 3, 4, 5]

/-- info: 2.236068 -/
#guard_msgs in
#eval pyNumpyStd [2, 4, 6, 8]

/-- info: 3.250000 -/
#guard_msgs in
#eval pyNumpyPercentile [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 25.0

/-- info: 7.750000 -/
#guard_msgs in
#eval pyNumpyPercentile [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 75.0

-- ==================== Element-wise Operations ====================

/-- info: [2.000000, 5.000000, 10.000000, 12.000000] -/
#guard_msgs in
#eval pyNumpyClip [1, 5, 10, 15] 2.0 12.0

/-- info: [1.000000, 2.000000, 3.000000, 3.000000] -/
#guard_msgs in
#eval pyNumpyRound [1.3, 1.5, 2.7, 3.2]

/-- info: [1.000000, 2.718282] -/
#guard_msgs in
#eval pyNumpyExp [0.0, 1.0]

/-- info: [0.000000, 1.000000] -/
#guard_msgs in
#eval pyNumpyLog [1.0, 2.718281828459045]

/-- info: [1.000000, 2.000000, 3.000000, 4.000000] -/
#guard_msgs in
#eval pyNumpySqrt [1.0, 4.0, 9.0, 16.0]

/-- info: 5.000000 -/
#guard_msgs in
#eval pyNumpyNorm [3.0, 4.0]

-- ==================== Boolean & Logic ====================

/-- info: true -/
#guard_msgs in
#eval pyNumpyAny [0, 0, 1, 0]

/-- info: true -/
#guard_msgs in
#eval pyNumpyAll [1, 1, 1, 1]

/-- info: [true, false, false] -/
#guard_msgs in
#eval pyNumpyLogicalAnd [true, true, false] [true, false, true]

/-- info: [true, false, true] -/
#guard_msgs in
#eval pyNumpyLogicalOr [true, false, false] [false, false, true]

/-- info: [false, true, false] -/
#guard_msgs in
#eval pyNumpyLogicalNot [true, false, true]

/-- info: [true, true, true] -/
#guard_msgs in
#eval pyNumpyIsclose [1.0, 2.0, 3.0] [1.0000001, 2.0000001, 3.0000001] 1e-5

-- ==================== Sorting & Searching ====================

/-- info: [1.000000, 1.000000, 3.000000, 4.000000, 5.000000] -/
#guard_msgs in
#eval pyNumpySort [3, 1, 4, 1, 5]

/-- info: [3, 1, 0, 2, 4] -/
#guard_msgs in
#eval pyNumpyArgsort [3, 1, 4, 1, 5]

/-- info: 2 -/
#guard_msgs in
#eval pyNumpySearchsorted [1.0, 3.0, 5.0, 7.0] 4.0

/-- info: [1.000000, 2.000000, 3.000000, 4.000000] -/
#guard_msgs in
#eval pyNumpyUnique [1, 2, 2, 3, 3, 3, 4]

-- ==================== Filtering & Selection ====================

/-- info: [1, 3, 4] -/
#guard_msgs in
#eval pyNumpyNonzero [0, 1, 0, 2, 3, 0]

/-- info: [1.000000, 20.000000, 3.000000] -/
#guard_msgs in
#eval pyNumpyWhere [true, false, true] [1, 2, 3] [10, 20, 30]

/-- info: [1.000000, 3.000000, 4.000000] -/
#guard_msgs in
#eval pyNumpyExtract [true, false, true, true] [1, 2, 3, 4]

/-- info: [10.000000, 30.000000, 50.000000] -/
#guard_msgs in
#eval pyNumpyTake [10, 20, 30, 40, 50] [0, 2, 4]

-- ==================== Linear Algebra ====================

/-- info: -2.000000 -/
#guard_msgs in
#eval pyNumpyDet [[1.0, 2.0], [3.0, 4.0]]

/-- info: [[-2.000000, 1.000000], [1.500000, -0.500000]] -/
#guard_msgs in
#eval pyNumpyInv [[1.0, 2.0], [3.0, 4.0]]

-- ==================== Utility Tests ====================

/-- info: [1.000000, 2.000000, 3.000000] -/
#guard_msgs in
#eval pyNumpyToFloats [1, 2, 3]

/-- info: [false, true, false, true] -/
#guard_msgs in
#eval pyNumpyIsin [1, 2, 3, 4] [2, 4, 6]

/-- info: [[1.000000, 2.000000, 1.000000, 2.000000], [1.000000, 2.000000, 1.000000, 2.000000]] -/
#guard_msgs in
#eval pyNumpyTile [[1.0, 2.0]] (2, 2)

end Libraries.numpy
