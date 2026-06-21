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

/-- Python `math.tau` (`2π`). -/
def pyMathTau : Float :=
  6.283185307179586

/-- Python `math.inf`. -/
def pyMathInf : Float :=
  1.0 / 0.0

/-- Python `math.nan`. -/
def pyMathNan : Float :=
  0.0 / 0.0

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

/-- Exact-mode `math.pow` with an integer exponent: `math.pow(x, n)` is *algebraic* (`xⁿ`), NOT
transcendental, so it stays in the base's type (`ℤ`/`ℚ`) and remains computable + provable — unlike
`Float.pow`. Keeps e.g. `sqrt(sum(pow(d, 2)))` rational under the `sqrt`. -/
def pyMathPowExact {α : Type} [Monoid α] (x : α) (y : Int) : α :=
  x ^ y.toNat

/-- Python `math.asin`, using Lean's computable floating-point arcsine. -/
def pyMathAsin {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.asin (toFloat x)

/-- Python `math.acos`, using Lean's computable floating-point arccosine. -/
def pyMathAcos {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.acos (toFloat x)

/-- Python `math.atan`, using Lean's computable floating-point arctangent. -/
def pyMathAtan {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.atan (toFloat x)

/-- Python `math.sinh`, the hyperbolic sine. -/
def pyMathSinh {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.sinh (toFloat x)

/-- Python `math.cosh`, the hyperbolic cosine. -/
def pyMathCosh {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.cosh (toFloat x)

/-- Python `math.tanh`, the hyperbolic tangent. -/
def pyMathTanh {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.tanh (toFloat x)

/-- Python `math.expm1` (`eˣ − 1`), via the floating-point exponential. -/
def pyMathExpm1 {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.exp (toFloat x) - 1.0

/-- Python `math.log1p` (`log(1 + x)`), via the natural logarithm. -/
def pyMathLog1p {α : Type} [PyMathFloatArg α] (x : α) : Float :=
  Float.log (1.0 + toFloat x)

/-- Python `math.isnan`, true when the argument is NaN. -/
def pyMathIsnan {α : Type} [PyMathFloatArg α] (x : α) : Bool :=
  (toFloat x).isNaN

/-- Python `math.isinf`, true when the argument is positive or negative infinity. -/
def pyMathIsinf {α : Type} [PyMathFloatArg α] (x : α) : Bool :=
  (toFloat x).isInf

/-- Python `math.isfinite`, true when the argument is neither NaN nor infinite. -/
def pyMathIsfinite {α : Type} [PyMathFloatArg α] (x : α) : Bool :=
  (toFloat x).isFinite

/-- Python `math.copysign`, returning `|x|` with the sign of `y`. -/
def pyMathCopysign {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β] (x : α) (y : β) : Float :=
  let xf := Float.abs (toFloat x)
  if toFloat y < 0.0 then -xf else xf

/-- Python `math.fmod`, the floating-point C-style remainder (sign follows the dividend). -/
def pyMathFmod {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β] (x : α) (y : β) : Float :=
  let xf := toFloat x
  let yf := toFloat y
  let q := xf / yf
  let qt := if q < 0.0 then Float.ceil q else Float.floor q
  xf - yf * qt

/-- Python `math.dist`, the Euclidean distance between two equal-length point vectors. -/
def pyMathDist {α β : Type} [PyMathFloatArg α] [PyMathFloatArg β]
    (p : List α) (q : List β) : Float :=
  if p.length = q.length then
    Float.sqrt ((List.zipWith (fun a b => (toFloat a - toFloat b) ^ 2) p q).foldl (· + ·) 0.0)
  else
    panic! "ValueError: dist() expects two points of the same dimension"

/-- Python `math.prod`, the product of an iterable of integers (with optional `start`). -/
def pyMathProd (xs : List Int) (start : Int := 1) : Int :=
  xs.foldl (· * ·) start

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

/-! ## Exact transcendentals over `ℝ` (default / non-`--approx` mode)

`noncomputable` `ℝ` counterparts of the `Float` transcendentals above, backed by Mathlib's
`Real.*`. Not runnable, but theorems about them are *true* (`Real.exp 0 = 1`, …). Codegen selects
these over the `Float` versions in exact mode. -/

/-- Inputs acceptable to the `ℝ`-valued math surface (`ℚ`/`ℤ`/`ℕ`/`ℝ` → `ℝ`). -/
class PyMathRealArg (α : Type) where
  toReal : α → ℝ

noncomputable instance : PyMathRealArg ℝ := ⟨id⟩
noncomputable instance : PyMathRealArg ℚ := ⟨fun q => (q : ℝ)⟩
noncomputable instance : PyMathRealArg Int := ⟨fun n => (n : ℝ)⟩
noncomputable instance : PyMathRealArg Nat := ⟨fun n => (n : ℝ)⟩

noncomputable def pyMathSqrtR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.sqrt (PyMathRealArg.toReal x)
noncomputable def pyMathExpR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.exp (PyMathRealArg.toReal x)
noncomputable def pyMathLogR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.log (PyMathRealArg.toReal x)
noncomputable def pyMathSinR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.sin (PyMathRealArg.toReal x)
noncomputable def pyMathCosR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.cos (PyMathRealArg.toReal x)
noncomputable def pyMathTanR {α : Type} [PyMathRealArg α] (x : α) : ℝ := Real.tan (PyMathRealArg.toReal x)
noncomputable def pyMathPiR : ℝ := Real.pi
noncomputable def pyMathER : ℝ := Real.exp 1

end Libraries.math
