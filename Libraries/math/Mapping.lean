import Mathlib
import Libraries.math.MathDef

namespace Libraries.math

/-- Library-local registry for Python's `math` module members. -/
def pythonMathMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "pi" => some ``pyMathPi
  | "e" => some ``pyMathE
  | "sqrt" => some ``pyMathSqrt
  | "sin" => some ``pyMathSin
  | "cos" => some ``pyMathCos
  | "tan" => some ``pyMathTan
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

end Libraries.math
