import Libraries.pandas.DataFrame

namespace Libraries.pandas
def pythonPandasMemberMap? (memberName : String) : Option Lean.Name :=
  match memberName with
  | "DataFrame" => some ``Libraries.pandas.pyDataFrame
  -- | "Series" => some ``Libraries.pandas.pySeries
  -- | "read_csv" => some ``Libraries.pandas.pyReadCsv
  -- | "to_csv" => some ``Libraries.pandas.pyToCsv
  -- | "head" => some ``Libraries.pandas.pyHead
  -- | "tail" => some ``Libraries.pandas.pyTail
  -- | "describe" => some ``Libraries.pandas.pyDescribe
  -- | "info" => some ``Libraries.pandas.pyInfo
  -- | "groupby" => some ``Libraries.pandas.pyGroupBy
  -- | "merge" => some ``Libraries.pandas.pyMerge
  -- | "concat" => some ``Libraries.pandas.pyConcat
  | "columns" => some ``Libraries.pandas.DataFrame.getColumns
  | "index" => some ``Libraries.pandas.DataFrame.getIndex
  | "shape" => some ``Libraries.pandas.DataFrame.shape
  | "empty" => some ``Libraries.pandas.DataFrame.empty
  | "head" => some ``Libraries.pandas.DataFrame.head
  | "at" => some ``Libraries.pandas.DataFrame.at
  | "insert" => some ``Libraries.pandas.DataFrame.insert
  | _ => none
