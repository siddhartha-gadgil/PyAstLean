import Libraries.pandas.Series

/-!
# pandas `Series` — statistics

Numeric reductions over a `Series`, extending the namespace from `Series.lean`. All follow pandas'
defaults: `skipna=True` (missing/non-numeric cells dropped via `Series.numeric`), sample standard
deviation (`ddof=1`), and linear-interpolated quantiles.

Dtype fidelity (matches pandas): `sum`/`min`/`max` **preserve** the column dtype — an integer column
reduces to an integer `Cell`. `mean`/`std`/`var`/`quantile`/`median`/`describe` are always float
(the `…F` helpers give the raw `Float`).
-/

namespace Libraries.pandas
namespace Series

/-- `NaN` literal. -/
def nanF : Float := (0.0 : Float) / 0.0

/-- Insertion sort for floats (small columns; avoids churny `List.mergeSort` signatures). -/
private def insertSorted (x : Float) : List Float → List Float
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Ascending sort of a float list. -/
def sortFloats (xs : List Float) : List Float := xs.foldr insertSorted []

/-- `s.count()` — number of non-missing entries. -/
def count (s : Series) : Nat := s.numeric.length

-- Raw `Float` reductions (used by `describe` and by dtype-preserving wrappers).

/-- Sum as a `Float`. -/
def sumF (s : Series) : Float := s.numeric.foldl (· + ·) 0.0

/-- Minimum as a `Float` (`NaN` when empty). -/
def minF (s : Series) : Float :=
  match s.numeric with
  | []      => nanF
  | x :: xs => xs.foldl (fun a b => if b < a then b else a) x

/-- Maximum as a `Float` (`NaN` when empty). -/
def maxF (s : Series) : Float :=
  match s.numeric with
  | []      => nanF
  | x :: xs => xs.foldl (fun a b => if b > a then b else a) x

-- Dtype-preserving public reductions (integer column ⇒ integer `Cell`).

/-- `s.sum()` — sum of non-missing values (`0` when there are none). Integer-dtype ⇒ integer cell. -/
def sum (s : Series) : Cell :=
  if s.dtype == DType.int then Cell.int ((intVals s.values).foldl (· + ·) 0)
  else Cell.float s.sumF

/-- `s.min()` — minimum non-missing value; integer-dtype ⇒ integer cell, `NaN` when empty. -/
def min (s : Series) : Cell :=
  if s.dtype == DType.int then
    match intVals s.values with
    | []      => Cell.float nanF
    | n :: ns => Cell.int (ns.foldl (fun a b => if b < a then b else a) n)
  else Cell.float s.minF

/-- `s.max()` — maximum non-missing value; integer-dtype ⇒ integer cell, `NaN` when empty. -/
def max (s : Series) : Cell :=
  if s.dtype == DType.int then
    match intVals s.values with
    | []      => Cell.float nanF
    | n :: ns => Cell.int (ns.foldl (fun a b => if b > a then b else a) n)
  else Cell.float s.maxF

/-- `s.mean()` — arithmetic mean, `NaN` when empty (always float). -/
def mean (s : Series) : Float :=
  let xs := s.numeric
  if xs.isEmpty then nanF else s.sumF / Float.ofNat xs.length

/-- Variance with the given delta-degrees-of-freedom. pandas defaults to `ddof=1`. -/
def var (s : Series) (ddof : Nat := 1) : Float :=
  let xs := s.numeric
  let n  := xs.length
  if n ≤ ddof then nanF
  else
    let m := s.mean
    let ss := xs.foldl (fun acc x => acc + (x - m) * (x - m)) 0.0
    ss / Float.ofNat (n - ddof)

/-- Sample standard deviation (`ddof=1` by default), matching pandas `.std()`. -/
def std (s : Series) (ddof : Nat := 1) : Float := (s.var ddof).sqrt

/-- Linear-interpolated quantile of the sorted non-missing values (pandas default method). -/
def quantile (s : Series) (q : Float) : Float :=
  let sorted := sortFloats s.numeric
  let n := sorted.length
  if n == 0 then nanF
  else if n == 1 then sorted[0]!
  else
    let pos := q * Float.ofNat (n - 1)
    let loF := pos.floor
    let loi := loF.toUInt64.toNat
    let hii := pos.ceil.toUInt64.toNat
    let lo := sorted[loi]!
    let hi := sorted[hii]!
    lo + (hi - lo) * (pos - loF)

/-- `s.median()` — the 0.5 quantile. -/
def median (s : Series) : Float := s.quantile 0.5

/-- `s.describe()` — count/mean/std/min/quartiles/max as a labelled `Series` (all float, as pandas). -/
def describe (s : Series) : Series :=
  ofCells
    [ Cell.float (Float.ofNat s.count), Cell.float s.mean, Cell.float s.std,
      Cell.float s.minF, Cell.float (s.quantile 0.25), Cell.float (s.quantile 0.5),
      Cell.float (s.quantile 0.75), Cell.float s.maxF ]
    (index := some ["count", "mean", "std", "min", "25%", "50%", "75%", "max"])
    (name := s.name)

end Series
end Libraries.pandas
