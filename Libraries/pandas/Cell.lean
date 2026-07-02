import PastaLean.PyAPI.PyPrint

/-!
# pandas cell values

A `Cell` is a single value stored in a `Series`/`DataFrame`. pandas columns are heterogeneous at the
Python level (int, float, str, bool, and missing `NaN`), so we model one tagged value type rather
than a fixed Lean type. Numeric reductions (`sum`, `mean`, …) read cells through `Cell.toFloat?`,
which yields `none` for non-numeric / missing entries — matching pandas' `skipna=True` default.
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

/-- pandas-style textual form of a cell (used for printing frames). -/
def toStr : Cell → String
  | .int n   => toString n
  | .float f => toString f
  | .str s   => s
  | .bool b  => if b then "True" else "False"
  | .na      => "NaN"

instance : ToString Cell := ⟨toStr⟩

end Cell

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
