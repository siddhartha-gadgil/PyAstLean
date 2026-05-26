import Mathlib
import Libraries.numpy.NumpyDef

namespace Libraries.numpy

/-- Library-local registry for NumPy-style helpers. -/
def pythonNumpyMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "array" => some ``pyNumpyArray
  | "asarray" => some ``pyNumpyArray
  | "shape" => some ``pyNumpyShape
  | "zeros" => some ``pyNumpyZeros
  | "ones" => some ``pyNumpyOnes
  | "eye" => some ``pyNumpyEye
  | "identity" => some ``pyNumpyEye
  | "transpose" => some ``pyNumpyTranspose
  | "add" => some ``pyNumpyAdd
  | "subtract" => some ``pyNumpySubtract
  | "multiply" => some ``pyNumpyMultiply
  | "scale" => some ``pyNumpyScale
  | "dot" => some ``pyNumpyDot
  | "matmul" => some ``pyNumpyMatmul
  | "sum" => some ``pyNumpySum
  | "mean" => some ``pyNumpyMean
  | "trace" => some ``pyNumpyTrace
  | "flatten" => some ``pyNumpyFlatten
  | "ravel" => some ``pyNumpyFlatten
  | _ => none

end Libraries.numpy
