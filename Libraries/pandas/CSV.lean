import Libraries.pandas.DataFrame
import PastaLean.PyAPI.Builtins.Casting

/-!
# pandas CSV I/O (`read_csv` / `to_csv`)

Parsing and rendering are pure (`parseCsvString` / `toCsvString`) so they're unit-testable; `readCsv`
/ `toCsv` are the thin `IO` wrappers over file access. Each field is type-inferred per cell (int →
float → string), so numeric columns come back with the right dtype. This is a simple comma splitter:
it does not yet handle quoted fields containing commas or newlines.
-/

namespace Libraries.pandas

/-- Infer a cell from a raw CSV field: empty → missing, then int, then float, else string. -/
def parseCell (raw : String) : Cell :=
  let s := raw.trimAscii.toString
  if s.isEmpty then Cell.na
  else match s.toInt? with
    | some n => Cell.int n
    | none =>
      if s.any (·.isDigit) &&
         s.all (fun c => c.isDigit || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E')
      then Cell.float (PastaLean.pyFloat s)
      else Cell.str s

/-- Parse CSV text into a `DataFrame`: first non-empty line is the header, the rest are rows. -/
def parseCsvString (content : String) : DataFrame :=
  let lines := (content.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  match lines with
  | [] => { cols := [], index := [] }
  | header :: rows =>
    let colNames := (header.splitOn ",").map (fun s => s.trimAscii.toString)
    let parsedRows := rows.map (fun line => (line.splitOn ",").map parseCell)
    let cols := (List.range colNames.length).map fun j =>
      (colNames[j]!, parsedRows.map (fun r => r.getD j Cell.na))
    { cols, index := (List.range parsedRows.length).map toString }

/-- Render a frame as CSV text (header + rows, no index column), values in pandas cell form. -/
def DataFrame.toCsvString (df : DataFrame) : String :=
  let header := String.intercalate "," df.getColumns
  let rows := (List.range df.index.length).map fun i =>
    String.intercalate "," (df.cols.map fun col => (col.2.getD i Cell.na).toStr)
  String.intercalate "\n" (header :: rows)

/-- `pd.read_csv(path)`. -/
def readCsv (path : String) : IO DataFrame := do
  return parseCsvString (← IO.FS.readFile path)

/-- `df.to_csv(path)`. -/
def DataFrame.toCsv (df : DataFrame) (path : String) : IO Unit :=
  IO.FS.writeFile path (df.toCsvString ++ "\n")

end Libraries.pandas
