import Mathlib

namespace Libraries.math

/-- Types that can be fed to the float-oriented `math` runtime surface. -/
class PyMathFloatArg (α : Type) where
  toFloat : α → Float

export PyMathFloatArg (toFloat)

/-- Rational inputs convert exactly to Lean floats. -/
instance : PyMathFloatArg Rat where
  toFloat := Rat.toFloat

/-- Integer inputs are first viewed as rationals. -/
instance : PyMathFloatArg Int where
  toFloat x := Rat.toFloat (x : Rat)

/-- Natural inputs are first viewed as rationals. -/
instance : PyMathFloatArg Nat where
  toFloat x := Rat.toFloat (x : Rat)

/-- Floats are already in the target runtime representation. -/
instance : PyMathFloatArg Float where
  toFloat := id

/-- Boolean arguments follow Python's `True = 1`, `False = 0` convention. -/
instance : PyMathFloatArg Bool where
  toFloat b := if b then 1.0 else 0.0

/-- Convert a floating-point whole number result back to `Int`. -/
def floatToInt (x : Float) : Int :=
  Int64.toInt x.toInt64

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
def pyMathSqrt {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.sqrt (toFloat x)

/-- Python `math.sin`, using Lean's computable floating-point sine. -/
def pyMathSin {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.sin (toFloat x)

/-- Python `math.cos`, using Lean's computable floating-point cosine. -/
def pyMathCos {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.cos (toFloat x)

/-- Python `math.tan`, using Lean's computable floating-point tangent. -/
def pyMathTan {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.tan (toFloat x)

/-- Python `math.log`, using Lean's computable floating-point natural logarithm. -/
def pyMathLog {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.log (toFloat x)

/-- Python `math.exp`, using Lean's computable floating-point exponential. -/
def pyMathExp {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.exp (toFloat x)

/-- Python `math.fabs`, returning a floating-point absolute value. -/
def pyMathFabs {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.abs (toFloat x)

/-- Python `math.floor`, returning the greatest integer less than or equal to the input. -/
def pyMathFloor {α : Type} [PyMathFloatArg α] (x : α) : Int :=
  floatToInt (Float.floor (toFloat x))

/-- Python `math.ceil`, returning the least integer greater than or equal to the input. -/
def pyMathCeil {α : Type} [PyMathFloatArg α] (x : α) : Int :=
  floatToInt (Float.ceil (toFloat x))

/-- Python `math.trunc`, truncating toward zero. -/
def pyMathTrunc {α : Type} [PyMathFloatArg α] (x : α) : Int :=
  let xf := toFloat x
  if xf < 0.0 then
    floatToInt (Float.ceil xf)
  else
    floatToInt (Float.floor xf)

/-- Python `math.pow`, returning a floating-point result. -/
def pyMathPow {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β] (x : α) (y : β) : Float :=
  Float.pow (toFloat x) (toFloat y)

/-- Python `math.atan2`, using Lean's computable floating-point implementation. -/
def pyMathAtan2 {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β] (y : α) (x : β) : Float :=
  Float.atan2 (toFloat y) (toFloat x)

/-- Python `math.hypot`, restricted to the common two-argument form. -/
def pyMathHypot {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β] (x : α) (y : β) : Float :=
  let xf := toFloat x
  let yf := toFloat y
  Float.sqrt (xf * xf + yf * yf)

/-- Python `math.log2`, via the natural logarithm. -/
def pyMathLog2 {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.log (toFloat x) / Float.log 2.0

/-- Python `math.log10`, via the natural logarithm. -/
def pyMathLog10 {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.log (toFloat x) / Float.log 10.0

/-- Python `math.radians`, converting degrees to radians. -/
def pyMathRadians {α : Type} [PyMathFloatArg α] (deg : α) : Float :=
  toFloat deg * pyMathPi / 180.0

/-- Python `math.degrees`, converting radians to degrees. -/
def pyMathDegrees {α : Type} [PyMathFloatArg α] (rad : α) : Float :=
  toFloat rad * 180.0 / pyMathPi

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
