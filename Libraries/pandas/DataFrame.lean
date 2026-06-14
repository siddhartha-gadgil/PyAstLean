import PyAstLean.PyAPI.CommonProtocols.Iterable
import PyAstLean.PyAPI.PyPrint
import PyAstLean.PyAPI.Core

namespace Libraries.pandas

/-- DataFrame structure representing a 2D labeled data structure -/
structure DataFrame where
  /-- Column name to column data mapping -/
  columns : Std.HashMap String (List String)
  /-- Row index labels -/
  index : List String
  deriving Repr

instance : Inhabited DataFrame where
  default := { columns := {}, index := [] }

/-- Helper function to construct DataFrame from raw data -/
def pyDataFrameFunc {α β γ} [PyAstLean.PyIterable α β] [PyAstLean.PyIterable β γ] [PyAstLean.PyPrintable γ] [Inhabited β]
  (data : α) (index : Option (List String)) (columns : Option (List String))
    : DataFrame :=
  let rows := PyAstLean.pyIter data|>.map (fun row => PyAstLean.pyIter row|>.map (fun val => PyAstLean.PyPrintable.pyStringify val))
  match index, columns with
  | some idx, some cols =>
    if rows.length != idx.length || rows.length != cols.length then
      panic! "ValueError: DataFrame constructor expects data, index, and columns to have the same length"
    else
      { columns := Std.HashMap.ofList (List.zip cols rows), index := idx }
  | some idx, none =>
    if rows.length != idx.length then
      panic! "ValueError: DataFrame constructor expects data and index to have the same length"
    else
      let defaultCols := List.range (PyAstLean.pyIter (PyAstLean.pyIter data).head!).length|>.map (fun i => "col" ++ toString i)
      { columns := Std.HashMap.ofList (List.zip defaultCols rows), index := idx }
  | none, some cols =>
    if rows.length != cols.length then
      panic! "ValueError: DataFrame constructor expects data and columns to have the same length"
    else
      let defaultIdx := List.range rows.length|>.map (fun i => "row" ++ toString i)
      { columns := Std.HashMap.ofList (List.zip cols rows), index := defaultIdx }
  | none, none =>
    let defaultIdx := List.range rows.length|>.map (fun i => "row" ++ toString i)
    let defaultCols := List.range (PyAstLean.pyIter (PyAstLean.pyIter data).head!).length|>.map (fun i => "col" ++ toString i)
    { columns := Std.HashMap.ofList (List.zip defaultCols rows), index := defaultIdx }

instance : Coe (Array String) (Option (List String)) where
  coe a := some a.toList

instance : Coe (List String) (Option (List String)) where
  coe l := some l

set_option linter.unusedVariables false in
/-- Main DataFrame constructor with optional parameters -/
def pyDataFrame {α β γ} [PyAstLean.PyIterable α β] [PyAstLean.PyIterable β γ] [PyAstLean.PyPrintable γ] [Inhabited β]
  (data : α)
  (index : Option (List String) := none) (columns : Option (List String) := none) (dtype copy : Unit := ())
    : DataFrame :=
  pyDataFrameFunc data index columns

/-- Accessor for column names -/
def DataFrame.getColumns (df : DataFrame) : List String :=
  df.columns.keys

/-- Accessor for row indices -/
def DataFrame.getIndex (df : DataFrame) : List String :=
  df.index

/-- Get a specific column by name -/
def DataFrame.getColumn? (df : DataFrame) (colName : String) : Option (List String) :=
  df.columns.get? colName

def DataFrame.shape (df : DataFrame) : Int × Int :=
  let nRows := df.index.length
  let nCols := df.columns.size
  (nRows, nCols)

def DataFrame.empty (df : DataFrame) : Bool :=
  df.columns.isEmpty

def DataFrame.head (df : DataFrame) (n : Nat := 5) : DataFrame :=
  let nRows := min n df.index.length
  let newIndex := df.index.take nRows
  let newColumns := df.columns.map fun _ colData => (colData.take nRows)
  { columns := Std.HashMap.ofList newColumns.toList, index := newIndex }

def DataFrame.at (df : DataFrame) (rowLabel : String) (colName : String) : String :=
  match df.index.idxOf? rowLabel, df.columns.get? colName with
  | some rowIndex, some colData =>
    colData[rowIndex]!
  | _, _ => panic! "KeyError: Row label or column name not found in DataFrame"

set_option linter.unusedVariables false in
def DataFrame.insert (df : DataFrame) (loc : Nat) (colName : String) (colData : List String) (ad : Bool) : DataFrame :=
  if colData.length != df.index.length then
    panic! "ValueError: Length of new column data must match number of rows in DataFrame"
  else
    let newColumns := df.columns.insert colName colData
    { columns := newColumns, index := df.index }

def prettyPrintdf (df : DataFrame) : IO Unit := do
  let colNames := df.getColumns
  let indexLabels := df.getIndex
  let numRows := indexLabels.length

  -- Build header
  let header := "      | " ++ String.intercalate " | " colNames

  -- Build rows
  let rows := List.range numRows |>.map fun i =>
    let label := indexLabels[i]? |>.getD ""
    let rowValues := colNames.map fun colName =>
      let colData := df.columns.getD colName []
      colData[i]? |>.getD "NaN"
    label ++ " | " ++ String.intercalate " | " rowValues

  -- Combine header and rows
  IO.println (String.intercalate "\n" (header :: rows))

-- end Libraries.pandas
def l := pyDataFrame [[1, 2], [3, 4]]  (columns := ["col1", "col2"])
#eval prettyPrintdf ( l.head )
#eval l.at "row0" "col1"  -- Should return "1"
#eval [1,2].find? (fun x => x > 1)
