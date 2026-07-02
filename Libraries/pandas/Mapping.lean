import Libraries.pandas.Dispatch
import Libraries.pandas.CSV
import Libraries.pandas.Subscript

namespace Libraries.pandas

/-- Registry mapping imported `pandas` members (and DataFrame/Series methods) to Lean runtime
functions. `DataFrame`/`Series` are the module constructors; the remaining entries are the
method/attribute names dispatched on a frame or series value.

Methods that exist on **both** `Series` and `DataFrame` (`sum`, `mean`, `head`, …) map to the
overload typeclass methods from `Dispatch.lean`, so instance resolution selects the right
implementation from the receiver's type. Methods unique to one type map to it directly. -/
def pythonPandasMemberMap? (memberName : String) : Option Lean.Name :=
  match memberName with
  -- Constructors & I/O
  | "DataFrame" => some ``Libraries.pandas.DataFrame.pyDataFrame
  | "Series"    => some ``Libraries.pandas.Series.ofList
  | "read_csv"  => some ``Libraries.pandas.readCsv
  | "to_csv"    => some ``Libraries.pandas.DataFrame.toCsv
  | "groupby"   => some ``Libraries.pandas.DataFrame.groupby
  -- Overloaded methods (Series *and* DataFrame) — dispatched by instance on the receiver type
  | "sum"       => some ``Libraries.pandas.PySum.pySum
  | "mean"      => some ``Libraries.pandas.PyMean.pyMean
  | "min"       => some ``Libraries.pandas.PyMin.pyMin
  | "max"       => some ``Libraries.pandas.PyMax.pyMax
  | "std"       => some ``Libraries.pandas.PyStd.pyStd
  | "describe"  => some ``Libraries.pandas.PyDescribe.pyDescribe
  | "head"      => some ``Libraries.pandas.PyHead.pyHead
  | "tail"      => some ``Libraries.pandas.PyTail.pyTail
  -- DataFrame-only attributes / access
  | "columns"   => some ``Libraries.pandas.DataFrame.getColumns
  | "index"     => some ``Libraries.pandas.DataFrame.getIndex
  | "shape"     => some ``Libraries.pandas.DataFrame.shape
  | "empty"     => some ``Libraries.pandas.DataFrame.empty
  | "at"        => some ``Libraries.pandas.DataFrame.getAt
  | "iat"       => some ``Libraries.pandas.DataFrame.iat
  | "insert"    => some ``Libraries.pandas.DataFrame.insert
  | "drop"      => some ``Libraries.pandas.DataFrame.dropColumn
  -- Series-only access
  | "iloc"      => some ``Libraries.pandas.Series.iloc
  | "loc"       => some ``Libraries.pandas.Series.loc
  | _ => none

end Libraries.pandas
