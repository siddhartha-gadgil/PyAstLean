import Mathlib

namespace Libraries.math

/-- Internal helper for the float-oriented `math` runtime surface. -/
def ratToFloat (x : Rat) : Float :=
  Rat.toFloat x

/--
Python's `math` module is float-oriented. We therefore expose a computable `Float`-based
surface here, converting rational inputs when needed so generated Lean stays executable
without forcing downstream code to become `noncomputable`.
-/
def pyMathPi : Float :=
  3.141592653589793

/-- Computable `math.e` approximation for generated Lean code. -/
def pyMathE : Float :=
  2.718281828459045

/-- Python `math.sqrt`, using Lean's computable floating-point square root. -/
def pyMathSqrt (x : Rat) : Float :=
  Float.sqrt (Rat.toFloat x)

/-- Python `math.sin`, using Lean's computable floating-point sine. -/
def pyMathSin (x : Rat) : Float :=
  Float.sin (Rat.toFloat x)

/-- Python `math.cos`, using Lean's computable floating-point cosine. -/
def pyMathCos (x : Rat) : Float :=
  Float.cos (Rat.toFloat x)

/-- Python `math.tan`, using Lean's computable floating-point tangent. -/
def pyMathTan (x : Rat) : Float :=
  Float.tan (Rat.toFloat x)

/-- Python `math.log`, using Lean's computable floating-point natural logarithm. -/
def pyMathLog (x : Rat) : Float :=
  Float.log (Rat.toFloat x)

/-- Python `math.exp`, using Lean's computable floating-point exponential. -/
def pyMathExp (x : Rat) : Float :=
  Float.exp (Rat.toFloat x)

/-- Python `math.fabs`, returning a floating-point absolute value. -/
def pyMathFabs (x : Rat) : Float :=
  Float.abs (ratToFloat x)

/-- Python `math.floor`, returning the greatest integer less than or equal to the input. -/
def pyMathFloor (x : Rat) : Int :=
  Int.floor x

/-- Python `math.ceil`, returning the least integer greater than or equal to the input. -/
def pyMathCeil (x : Rat) : Int :=
  Int.ceil x

/-- Python `math.trunc`, truncating toward zero. -/
def pyMathTrunc (x : Rat) : Int :=
  if x < 0 then Int.ceil x else Int.floor x

/-- Python `math.pow`, returning a floating-point result. -/
def pyMathPow (x y : Rat) : Float :=
  Float.pow (ratToFloat x) (ratToFloat y)

/-- Python `math.atan2`, using Lean's computable floating-point implementation. -/
def pyMathAtan2 (y x : Rat) : Float :=
  Float.atan2 (ratToFloat y) (ratToFloat x)

/-- Python `math.hypot`, restricted to the common two-argument form. -/
def pyMathHypot (x y : Rat) : Float :=
  Float.sqrt (ratToFloat x * ratToFloat x + ratToFloat y * ratToFloat y)

/-- Python `math.log2`, via the natural logarithm. -/
def pyMathLog2 (x : Rat) : Float :=
  Float.log (ratToFloat x) / Float.log 2.0

/-- Python `math.log10`, via the natural logarithm. -/
def pyMathLog10 (x : Rat) : Float :=
  Float.log (ratToFloat x) / Float.log 10.0

/-- Python `math.radians`, converting degrees to radians. -/
def pyMathRadians (deg : Rat) : Float :=
  ratToFloat deg * pyMathPi / 180.0

/-- Python `math.degrees`, converting radians to degrees. -/
def pyMathDegrees (rad : Rat) : Float :=
  ratToFloat rad * 180.0 / pyMathPi

/-- Python `math.factorial`, restricted to nonnegative integers. -/
def pyMathFactorial (n : Int) : Int :=
  if n < 0 then
    panic! "ValueError: factorial() not defined for negative values"
  else
    Int.ofNat (Nat.factorial n.toNat)

/-- Python `math.gcd`, backed by Lean's integer gcd. -/
def pyMathGcd (a b : Int) : Int :=
  Int.gcd a b

/-- Python `math.lcm`, backed by Lean's integer lcm. -/
def pyMathLcm (a b : Int) : Int :=
  Int.lcm a b

/-- Python `math.isqrt`, restricted to nonnegative integers. -/
def pyMathIsqrt (n : Int) : Int :=
  if n < 0 then
    panic! "ValueError: isqrt() argument must be nonnegative"
  else
    Int.sqrt n

/-- Python `math.comb`, restricted to nonnegative integer arguments. -/
def pyMathComb (n k : Int) : Int :=
  if n < 0 || k < 0 then
    panic! "ValueError: comb() not defined for negative values"
  else
    Int.ofNat (Nat.choose n.toNat k.toNat)

/-- Python `math.perm`, restricted to the explicit two-argument form on nonnegative integers. -/
def pyMathPerm (n k : Int) : Int :=
  if n < 0 || k < 0 then
    panic! "ValueError: perm() not defined for negative values"
  else
    Int.ofNat (Nat.descFactorial n.toNat k.toNat)

end Libraries.math
