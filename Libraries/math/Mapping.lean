import Mathlib
import Libraries.math.MathDef

namespace Libraries.math

/-- Library-local registry for Python's `math` module members. -/
def pythonMathMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "pi" => some ``pyMathPi
  | "e" => some ``pyMathE
  | "tau" => some ``pyMathTau
  | "inf" => some ``pyMathInf
  | "nan" => some ``pyMathNan
  | "sqrt" => some ``pyMathSqrt
  | "sin" => some ``pyMathSin
  | "cos" => some ``pyMathCos
  | "tan" => some ``pyMathTan
  | "asin" => some ``pyMathAsin
  | "acos" => some ``pyMathAcos
  | "atan" => some ``pyMathAtan
  | "sinh" => some ``pyMathSinh
  | "cosh" => some ``pyMathCosh
  | "tanh" => some ``pyMathTanh
  | "expm1" => some ``pyMathExpm1
  | "log1p" => some ``pyMathLog1p
  | "isnan" => some ``pyMathIsnan
  | "isinf" => some ``pyMathIsinf
  | "isfinite" => some ``pyMathIsfinite
  | "copysign" => some ``pyMathCopysign
  | "fmod" => some ``pyMathFmod
  | "dist" => some ``pyMathDist
  | "prod" => some ``pyMathProd
  | "log" => some ``pyMathLog
  | "log2" => some ``pyMathLog2
  | "log10" => some ``pyMathLog10
  | "exp" => some ``pyMathExp
  | "fabs" => some ``pyMathFabs
  | "floor" => some ``pyMathFloor
  | "ceil" => some ``pyMathCeil
  | "trunc" => some ``pyMathTrunc
  | "pow" => some ``pyMathPow
  | "atan2" => some ``pyMathAtan2
  | "hypot" => some ``pyMathHypot
  | "radians" => some ``pyMathRadians
  | "degrees" => some ``pyMathDegrees
  | "factorial" => some ``pyMathFactorial
  | "gcd" => some ``pyMathGcd
  | "lcm" => some ``pyMathLcm
  | "isqrt" => some ``pyMathIsqrt
  | "comb" => some ``pyMathComb
  | "perm" => some ``pyMathPerm
  | _ => none

/-- Exact (`ℝ`) versions of the transcendental members, used in the default numeric mode.
`none` for non-transcendental members (those keep their regular `pythonMathMemberMap?` mapping). -/
def pythonMathMemberMapReal? (member : String) : Option Lean.Name :=
  match member with
  | "sqrt" => some ``pyMathSqrtR
  | "exp" => some ``pyMathExpR
  | "log" => some ``pyMathLogR
  | "sin" => some ``pyMathSinR
  | "cos" => some ``pyMathCosR
  | "tan" => some ``pyMathTanR
  | "pi" => some ``pyMathPiR
  | "e" => some ``pyMathER
  | _ => none

/-- Exact-mode overrides that are computable + provable but NOT transcendental (so they go in their
own tier, not the `ℝ` real map): `math.pow` with an integer exponent stays in `ℚ`/`ℤ`. `none`
otherwise (keeps the regular `Float` mapping). -/
def pythonMathMemberMapExact? (member : String) : Option Lean.Name :=
  match member with
  | "pow" => some ``pyMathPowExact
  | _ => none

end Libraries.math
