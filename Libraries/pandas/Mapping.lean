import Libraries.pandas.DataFrameStats

namespace Libraries.pandas

/-- Registry mapping imported `pandas` members (and DataFrame/Series methods) to Lean runtime
functions. `DataFrame` is the module constructor; the remaining entries are the method/attribute
names dispatched on a frame or series value. -/
def pythonPandasMemberMap? (memberName : String) : Option Lean.Name :=
  match memberName with
  -- Constructors
  | "DataFrame" => some ``Libraries.pandas.DataFrame.pyDataFrame
  | "Series"    => some ``Libraries.pandas.Series.ofList
  -- DataFrame attributes / access
  | "columns"   => some ``Libraries.pandas.DataFrame.getColumns
  | "index"     => some ``Libraries.pandas.DataFrame.getIndex
  | "shape"     => some ``Libraries.pandas.DataFrame.shape
  | "empty"     => some ``Libraries.pandas.DataFrame.empty
  | "head"      => some ``Libraries.pandas.DataFrame.head
  | "tail"      => some ``Libraries.pandas.DataFrame.tail
  | "at"        => some ``Libraries.pandas.DataFrame.getAt
  | "iat"       => some ``Libraries.pandas.DataFrame.iat
  | "insert"    => some ``Libraries.pandas.DataFrame.insert
  | "drop"      => some ``Libraries.pandas.DataFrame.dropColumn
  -- DataFrame column-wise reductions (return a Series over the columns)
  | "sum"       => some ``Libraries.pandas.DataFrame.sum
  | "mean"      => some ``Libraries.pandas.DataFrame.mean
  | "min"       => some ``Libraries.pandas.DataFrame.min
  | "max"       => some ``Libraries.pandas.DataFrame.max
  | "std"       => some ``Libraries.pandas.DataFrame.std
  | "describe"  => some ``Libraries.pandas.DataFrame.describe
  | _ => none

end Libraries.pandas
