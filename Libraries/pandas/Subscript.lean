import PastaLean.PyAPI.CommonProtocols.GetItem
import Libraries.pandas.DataFrameStats

/-!
# Subscript access (`df["col"]`, `s[i]`)

The codegen already lowers `x[key]` to `PastaLean.pyGetItem x key`, so making transpiled subscripts
work on pandas types is just a matter of providing `PyGetItem` instances — no codegen change.

Note the protocol's index type is an `outParam`, i.e. **one `PyGetItem` instance per container
type**: a `DataFrame` can key by *either* a column name *or* a boolean mask, not both. We choose
column access (`df["col"] → Series`), the far more common form and the one that also builds the masks
for filtering. Boolean-mask filtering (`df[mask]`) is therefore exposed as a method
(`DataFrame.filter`) instead of a second subscript overload.
-/

namespace Libraries.pandas
open PastaLean

/-- `df["col"]` → the column as a `Series`. -/
instance : PyGetItem DataFrame String Series where
  getItem df name := df.getColumn name

/-- `s[i]` → the cell at position `i` (Python negative-index semantics). -/
instance : PyGetItem Series Int Cell where
  getItem s i := s.iloc i

/-- Build a boolean mask by comparing each numeric cell against a scalar (`df["a"] > 2` etc.).
Non-numeric / missing cells compare `false`. -/
private def cmpScalar (s : Series) (k : Float) (p : Float → Float → Bool) : Series :=
  { s with values := s.values.map fun c => match c.toFloat? with
      | some v => Cell.bool (p v k)
      | none   => Cell.bool false }

def Series.gtScalar (s : Series) (k : Float) : Series := cmpScalar s k (fun a b => a > b)
def Series.ltScalar (s : Series) (k : Float) : Series := cmpScalar s k (fun a b => a < b)
def Series.geScalar (s : Series) (k : Float) : Series := cmpScalar s k (fun a b => a ≥ b)
def Series.leScalar (s : Series) (k : Float) : Series := cmpScalar s k (fun a b => a ≤ b)
def Series.eqScalar (s : Series) (k : Float) : Series := cmpScalar s k (fun a b => a == b)

/-- Keep only the rows where `mask` (a boolean-valued `Series`, e.g. from `df["a"] > 2`) is true —
the value behind pandas' `df[mask]`. Exposed as a method because the subscript slot is taken by
column access (see the note above). -/
def DataFrame.filter (df : DataFrame) (mask : Series) : DataFrame :=
  let keep := mask.values.map fun c => match c with | .bool b => b | _ => (c.toFloat?).getD 0.0 != 0.0
  let pick : List Cell → List Cell := fun cells =>
    (cells.zip keep).filterMap fun p => if p.2 then some p.1 else none
  { cols := df.cols.map fun col => (col.1, pick col.2),
    index := (df.index.zip keep).filterMap fun p => if p.2 then some p.1 else none }

end Libraries.pandas
