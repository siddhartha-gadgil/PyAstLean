import Mathlib

namespace Libraries.numpy

/-- Internal helper for float-oriented matrix inputs. -/
def ratToFloat (x : Rat) : Float :=
  Rat.toFloat x

/-- Convert a nonnegative `Int` dimension to `Nat`. -/
def pyNumpyNatFromInt (n : Int) : Nat :=
  if n < 0 then
    panic! "ValueError: numpy dimensions must be nonnegative"
  else
    n.toNat

/-- Number of rows in a matrix. -/
def pyNumpyRows {α} (matrix : List (List α)) : Nat :=
  matrix.length

/-- Number of columns in a matrix, taken from the first row. -/
def pyNumpyCols {α} (matrix : List (List α)) : Nat :=
  match matrix with
  | [] => 0
  | row :: _ => row.length

/-- Check that every row has the same length. -/
def pyNumpyIsRectangular {α} (matrix : List (List α)) : Bool :=
  match matrix with
  | [] => true
  | row :: rows => rows.all (fun r => r.length = row.length)

/-- Check that a matrix is square. -/
def pyNumpyIsSquare {α} (matrix : List (List α)) : Bool :=
  pyNumpyIsRectangular matrix &&
    match matrix with
    | [] => true
    | row :: _ => matrix.length = row.length

/-- Compare the shapes of two matrices. -/
def pyNumpySameShape? {α β} (lhs : List (List α)) (rhs : List (List β)) : Bool :=
  match lhs, rhs with
  | [], [] => true
  | l :: ls, r :: rs => l.length = r.length && pyNumpySameShape? ls rs
  | _, _ => false

/-- Normalize a matrix to `Float` entries. -/
def pyNumpyArray (matrix : List (List Rat)) : List (List Float) :=
  matrix.map (List.map ratToFloat)

/-- Return the matrix shape as `(rows, cols)`. -/
def pyNumpyShape (matrix : List (List Rat)) : Int × Int :=
  if pyNumpyIsRectangular matrix then
    (Int.ofNat matrix.length, Int.ofNat (pyNumpyCols matrix))
  else
    panic! "ValueError: shape() expects a rectangular matrix"

/-- Build a zero-filled matrix. -/
def pyNumpyZeros (shape : Int × Int) : List (List Float) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 0.0)

/-- Build a one-filled matrix. -/
def pyNumpyOnes (shape : Int × Int) : List (List Float) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 1.0)

/-- Build an identity matrix. -/
def pyNumpyEye (n : Int) : List (List Float) :=
  let n' := pyNumpyNatFromInt n
  (List.range n').map (fun i =>
    (List.range n').map (fun j => if i = j then 1.0 else 0.0))

/-- Transpose a rectangular matrix. -/
def pyNumpyTranspose (matrix : List (List Rat)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let normalized := pyNumpyArray matrix
    (List.range (pyNumpyCols matrix)).map (fun c =>
      normalized.map (fun row => row.getD c 0.0))
  else
    panic! "ValueError: transpose() expects a rectangular matrix"

/-- Element-wise binary matrix operation. -/
def pyNumpyBinaryMatrix
    (f : Float -> Float -> Float)
    (lhs rhs : List (List Rat)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpySameShape? lhs rhs then
    List.zipWith (fun lrow rrow =>
      List.zipWith f (lrow.map ratToFloat) (rrow.map ratToFloat)) lhs rhs
  else
    panic! "ValueError: matrices must have the same rectangular shape"

/-- Add two matrices element-wise. -/
def pyNumpyAdd (lhs rhs : List (List Rat)) : List (List Float) :=
  pyNumpyBinaryMatrix (· + ·) lhs rhs

/-- Subtract two matrices element-wise. -/
def pyNumpySubtract (lhs rhs : List (List Rat)) : List (List Float) :=
  pyNumpyBinaryMatrix (· - ·) lhs rhs

/-- Multiply two matrices element-wise. -/
def pyNumpyMultiply (lhs rhs : List (List Rat)) : List (List Float) :=
  pyNumpyBinaryMatrix (· * ·) lhs rhs

/-- Scale every element in a matrix by a scalar. -/
def pyNumpyScale (scalar : Rat) (matrix : List (List Rat)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let s := ratToFloat scalar
    (pyNumpyArray matrix).map (fun row => row.map (fun x => s * x))
  else
    panic! "ValueError: scale() expects a rectangular matrix"

/-- Dot product of two vectors. -/
def pyNumpyDotFloats : List Float -> List Float -> Float
  | [], [] => 0.0
  | x :: xs, y :: ys => x * y + pyNumpyDotFloats xs ys
  | _, _ => panic! "ValueError: dot() expects vectors of the same length"

/-- Dot product of two vectors, converting entries to `Float`. -/
def pyNumpyDot (lhs rhs : List Rat) : Float :=
  if lhs.length = rhs.length then
    pyNumpyDotFloats (lhs.map ratToFloat) (rhs.map ratToFloat)
  else
    panic! "ValueError: dot() expects vectors of the same length"

/-- Matrix multiplication. -/
def pyNumpyMatmul (lhs rhs : List (List Rat)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpyCols lhs = pyNumpyRows rhs then
    let lhsF := pyNumpyArray lhs
    let rhsT := pyNumpyTranspose rhs
    lhsF.map (fun row => rhsT.map (fun col => pyNumpyDotFloats row col))
  else
    panic! "ValueError: matmul() requires compatible rectangular matrices"

/-- Sum all entries in a matrix. -/
def pyNumpySum (matrix : List (List Rat)) : Float :=
  (pyNumpyArray matrix).flatten.foldl (· + ·) 0.0

/-- Mean of all entries in a matrix. -/
def pyNumpyMean (matrix : List (List Rat)) : Float :=
  let entries := (pyNumpyArray matrix).flatten
  if entries.isEmpty then
    panic! "ValueError: mean() of an empty matrix is undefined"
  else
    entries.foldl (· + ·) 0.0 / ratToFloat entries.length

/-- Trace of a square matrix. -/
def pyNumpyTrace (matrix : List (List Rat)) : Float :=
  if pyNumpyIsSquare matrix then
    let normalized := pyNumpyArray matrix
    (List.range normalized.length).foldl
      (fun acc i => acc + (normalized.getD i []).getD i 0.0)
      0.0
  else
    panic! "ValueError: trace() expects a square matrix"

/-- Flatten a matrix into a vector. -/
def pyNumpyFlatten (matrix : List (List Rat)) : List Float :=
  (pyNumpyArray matrix).flatten

end Libraries.numpy
