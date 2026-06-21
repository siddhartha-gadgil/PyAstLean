import Libraries.scipy.ScipyDef

namespace Libraries.scipy

-- scipy.special — exact combinatorics, returned as floats (scipy convention).
/-- info: 120.000000 -/
#guard_msgs in
#eval pyScipyFactorial 5

/-- info: 10.000000 -/
#guard_msgs in
#eval pyScipyComb 5 2

/-- info: 20.000000 -/
#guard_msgs in
#eval pyScipyPerm 5 2

-- gamma(5) = 4! = 24 ; gamma(1/2) = sqrt(pi). Guards use a tolerance (approximations).
#guard (pyScipyGamma (5.0 : Float) - 24.0).abs < 1e-6
#guard (pyScipyGamma (0.5 : Float) - 1.7724538509055159).abs < 1e-9

-- erf(0) = 0 ; erf(1) ≈ 0.8427 (Abramowitz–Stegun, |err| ≤ 1.5e-7).
#guard (pyScipyErf (0.0 : Float)).abs < 1e-9
#guard (pyScipyErf (1.0 : Float) - 0.8427007929497149).abs < 1e-6

-- scipy.constants
#guard (pyScipyPi - 3.141592653589793).abs < 1e-12
#guard (pyScipyGolden - 1.618033988749895).abs < 1e-12

-- scipy.stats
/-- info: 2.500000 -/
#guard_msgs in
#eval pyScipyTmean [1.0, 2.0, 3.0, 4.0]

/-- info: 4.000000 -/
#guard_msgs in
#eval pyScipyGmean [1.0, 4.0, 16.0]

#guard (pyScipyHmean [1.0, 2.0, 4.0] - 1.7142857142857142).abs < 1e-9

-- scipy.linalg
/-- info: 5.000000 -/
#guard_msgs in
#eval pyScipyNorm ([3.0, 4.0] : List Float)

/-- info: -2.000000 -/
#guard_msgs in
#eval pyScipyDet [[1.0, 2.0], [3.0, 4.0]]

/-- info: 9.000000 -/
#guard_msgs in
#eval pyScipyDet [[2.0, 0.0, 1.0], [1.0, 3.0, 2.0], [1.0, 0.0, 2.0]]

end Libraries.scipy
