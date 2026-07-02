import PastaLean.PyAPI.PyPrint

/-!
# pandas cell values

A `Cell` is a single value stored in a `Series`/`DataFrame`. pandas columns are heterogeneous at the
Python level (int, float, str, bool, and missing `NaN`), so we model one tagged value type. Numeric
reductions read cells through `Cell.toFloat?` (yielding `none` for non-numeric/missing entries —
pandas' `skipna=True` default), while **dtype-preserving** reductions (`sum`/`min`/`max`/`cumsum`)
consult `dtypeOf` so an integer column stays integer, exactly as in pandas.
-/

namespace Libraries.pandas

/-- A single pandas value. `na` is the missing marker (Python `NaN`/`None`). -/
inductive Cell where
  | int   (n : Int)
  | float (f : Float)
  | str   (s : String)
  | bool  (b : Bool)
  | na
  deriving Repr, Inhabited, BEq

/-- pandas-style float repr: trims trailing zeros but keeps one decimal (`2.5`, `1.0`, not
`2.500000`); `NaN`/`inf` spelled as pandas does. -/
def formatFloat (f : Float) : String :=
  if f.isNaN then "NaN"
  else if f == (1.0 / 0.0) then "inf"
  else if f == (-1.0 / 0.0) then "-inf"
  else
    let s := toString f
    if s.contains '.' then
      let trimmed := String.ofList (s.toList.reverse.dropWhile (· == '0')).reverse
      if trimmed.endsWith "." then trimmed ++ "0" else trimmed
    else s

/-- Left-pad `s` with spaces to width `w` (right-justify), for numeric columns. -/
def padLeft (s : String) (w : Nat) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- Right-pad `s` with spaces to width `w` (left-justify), for index labels. -/
def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')

namespace Cell

/-- Numeric view of a cell for reductions. Non-numeric (`str`) and missing (`na`) cells are `none`,
so `skipna`-style aggregations drop them. `bool` follows Python: `True → 1.0`, `False → 0.0`. -/
def toFloat? : Cell → Option Float
  | .int n   => some (Float.ofInt n)
  | .float f => if f.isNaN then none else some f
  | .bool b  => some (if b then 1.0 else 0.0)
  | .str _   => none
  | .na      => none

/-- Is this cell missing (`NaN`/`None`)? A `float` NaN also counts as missing. -/
def isNA : Cell → Bool
  | .na      => true
  | .float f => f.isNaN
  | _        => false

/-- pandas-style textual form of a cell (floats trimmed, missing shown as `NaN`). -/
def toStr : Cell → String
  | .int n   => toString n
  | .float f => formatFloat f
  | .str s   => s
  | .bool b  => if b then "True" else "False"
  | .na      => "NaN"

instance : ToString Cell := ⟨toStr⟩

end Cell

/-- Inferred column dtype, following pandas: all-int (or bool) ⇒ `int`; any float **or a missing
value** ⇒ `float` (a `NaN` upcasts an int column to `float64`, as pandas does); any string ⇒
`object`. -/
inductive DType where
  | int | float | object
  deriving Repr, BEq

/-- pandas dtype name. -/
def DType.toStr : DType → String
  | .int => "int64" | .float => "float64" | .object => "object"

instance : ToString DType := ⟨DType.toStr⟩

/-- Infer the dtype of a column of cells (empty ⇒ `float64`, as for an empty numeric column). -/
def dtypeOf : List Cell → DType
  | [] => .float
  | cells =>
    if cells.all (fun c => match c with | .int _ | .bool _ => true | _ => false) then .int
    else if cells.all (fun c => match c with | .str _ => false | _ => true) then .float
    else .object

/-- Integer view of the numeric cells (`int` and `bool`), for integer-dtype reductions. -/
def intVals (cells : List Cell) : List Int :=
  cells.filterMap fun c => match c with
    | .int n  => some n
    | .bool b => some (if b then 1 else 0)
    | _       => none

/-- Build a `Cell` from a concrete Lean value. Lets `Series`/`DataFrame` be constructed from ordinary
Lean literals (`[1, 2, 3]`, `["a", "b"]`, …) that transpiled Python produces. -/
class ToCell (α : Type) where
  toCell : α → Cell

instance : ToCell Cell   := ⟨id⟩
instance : ToCell Int    := ⟨Cell.int⟩
instance : ToCell Nat    := ⟨fun n => Cell.int (Int.ofNat n)⟩
instance : ToCell Float  := ⟨Cell.float⟩
instance : ToCell String := ⟨Cell.str⟩
instance : ToCell Bool   := ⟨Cell.bool⟩

/-- Lift a Lean list to a list of cells. -/
def toCells {α} [ToCell α] (xs : List α) : List Cell :=
  xs.map ToCell.toCell

end Libraries.pandas
