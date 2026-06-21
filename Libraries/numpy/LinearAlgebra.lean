import Libraries.numpy.NumpyDef

namespace Libraries.numpy

/-- Transpose a rectangular matrix. -/
def pyNumpyTranspose {α} [PyNumpyScalar α] (matrix : List (List α)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let normalized := pyNumpyArray matrix
    (List.range (pyNumpyCols matrix)).map (fun c =>
      normalized.map (fun row => row.getD c 0.0))
  else
    panic! "ValueError: transpose() expects a rectangular matrix"

/-- Element-wise binary matrix operation. -/
def pyNumpyBinaryMatrix
    {α β : Type} [PyNumpyScalar α] [PyNumpyScalar β]
    (f : Float -> Float -> Float)
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpySameShape? lhs rhs then
    List.zipWith (fun lrow rrow =>
      List.zipWith f (lrow.map toFloat) (rrow.map toFloat)) lhs rhs
  else
    panic! "ValueError: matrices must have the same rectangular shape"

/-- Add two matrices element-wise. -/
def pyNumpyAdd {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· + ·) lhs rhs

/-- Subtract two matrices element-wise. -/
def pyNumpySubtract {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· - ·) lhs rhs

/-- Multiply two matrices element-wise. -/
def pyNumpyMultiply {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· * ·) lhs rhs

/-- Scale every element in a matrix by a scalar. -/
def pyNumpyScale {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (scalar : α) (matrix : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let s := toFloat scalar
    (pyNumpyArray matrix).map (fun row => row.map (fun x => s * x))
  else
    panic! "ValueError: scale() expects a rectangular matrix"

/-- Dot product of two vectors. -/
def pyNumpyDotFloats : List Float -> List Float -> Float
  | [], [] => 0.0
  | x :: xs, y :: ys => x * y + pyNumpyDotFloats xs ys
  | _, _ => panic! "ValueError: dot() expects vectors of the same length"

/-- Dot product over an arbitrary numeric type. Only needs `+`, `*`, `0` — NOT `Field`
(crucially `Float` is not a Mathlib `Field`, but is `Add`/`Mul`/`Zero`). -/
def pyNumpyDotField {γ} [Add γ] [Mul γ] [Zero γ] [Inhabited γ] : List γ -> List γ -> γ
  | [], [] => 0
  | x :: xs, y :: ys => x * y + pyNumpyDotField xs ys
  | _, _ => panic! "ValueError: dot() expects vectors of the same length"

/-- Dot product of two vectors whose element types may DIFFER (e.g. `ℚ` data · `ℝ` weights in a
neural net under exact mode). Both element types join to a common compute type `γ` via
`PyNumpyJoin` (`(ℚ,ℝ)→ℝ`, same-type pairs → their `PyNumpyCompute` field). -/
def pyNumpyDot {α β γ} [PyNumpyJoin α β γ] [Add γ] [Mul γ] [Zero γ] [Inhabited γ]
    (lhs : List α) (rhs : List β) : γ :=
  if lhs.length = rhs.length then
    pyNumpyDotField (lhs.map (fun x => PyNumpyJoin.castL (β := β) x))
                    (rhs.map (fun y => PyNumpyJoin.castR (α := α) y))
  else
    panic! "ValueError: dot() expects vectors of the same length"

/-- Matrix multiplication. -/
def pyNumpyMatmul {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpyCols lhs = pyNumpyRows rhs then
    let lhsF := pyNumpyArray lhs
    let rhsT := pyNumpyTranspose rhs
    lhsF.map (fun row => rhsT.map (fun col => pyNumpyDotFloats row col))
  else
    panic! "ValueError: matmul() requires compatible rectangular matrices"

/-- Trace of a square matrix. -/
def pyNumpyTrace {α} [PyNumpyScalar α] (matrix : List (List α)) : Float :=
  if pyNumpyIsSquare matrix then
    let normalized := pyNumpyArray matrix
    (List.range normalized.length).foldl
      (fun acc i => acc + (normalized.getD i []).getD i 0.0)
      0.0
  else
    panic! "ValueError: trace() expects a square matrix"

/-- Euclidean norm of a vector. -/
def pyNumpyNorm {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := xs.map toFloat
  Float.sqrt (ys.foldl (fun acc x => acc + x * x) 0.0)

/-- Alias for Euclidean norm. -/
def pyNumpyLinalgNorm {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyNorm xs

/-- Remove a column from a row. -/
def pyNumpyRemoveIndex (xs : List Float) (idx : Nat) : List Float :=
  match xs, idx with
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, n + 1 => x :: pyNumpyRemoveIndex xs n

/-- Remove a row and column from a matrix. -/
def pyNumpyMinor (matrix : List (List Float)) (row col : Nat) : List (List Float) :=
  let rec goRows : List (List Float) -> Nat -> List (List Float)
    | [], _ => []
    | x :: xs, i =>
        if i = row then
          goRows xs (i + 1)
        else
          pyNumpyRemoveIndex x col :: goRows xs (i + 1)
  goRows matrix 0

/-- Determinant for square matrices, computed recursively. -/
partial def pyNumpyDet (matrix : List (List Float)) : Float :=
  if pyNumpyIsSquare matrix then
    match matrix with
    | [] => 1.0
    | [ [a] ] => a
    | [ [a, b], [c, d] ] => a * d - b * c
    | row :: _ =>
        let rec expand (cols : List Float) (j : Nat) : Float :=
          match cols with
          | [] => 0.0
          | a :: as =>
              let sign := if j % 2 = 0 then 1.0 else -1.0
              sign * a * pyNumpyDet (pyNumpyMinor matrix 0 j) + expand as (j + 1)
        expand row 0
  else
    panic! "ValueError: det() expects a square matrix"

/-- Inverse for 1x1 and 2x2 square matrices. -/
def pyNumpyInv (matrix : List (List Float)) : List (List Float) :=
  if pyNumpyIsSquare matrix then
    match matrix with
    | [ [a] ] =>
        if a == 0.0 then
          panic! "ValueError: singular matrix"
        else
          [[1.0 / a]]
    | [ [a, b], [c, d] ] =>
        let det := a * d - b * c
        if det == 0.0 then
          panic! "ValueError: singular matrix"
        else
          [[d / det, -b / det], [-c / det, a / det]]
    | _ => panic! "ValueError: inv() currently supports only 1x1 and 2x2 matrices"
  else
    panic! "ValueError: inv() expects a square matrix"

/-- Solve a linear system via a closed-form inverse. -/
def pyNumpySolve (matrix rhs : List (List Float)) : List (List Float) :=
  pyNumpyMatmul (pyNumpyInv matrix) rhs

end Libraries.numpy
