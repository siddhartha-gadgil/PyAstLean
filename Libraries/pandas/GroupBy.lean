import Libraries.pandas.DataFrameStats

/-!
# pandas `groupby`

`df.groupby("k")` splits rows by the distinct values of column `k`, then an aggregation
(`sum`/`mean`/`min`/`max`/`count`) reduces each remaining column within each group, returning a
`DataFrame` indexed by the (sorted) group keys — matching pandas' default `sort=True`. Group keys are
compared numerically when the key column is numeric, lexicographically otherwise.
-/

namespace Libraries.pandas

/-- The result of `df.groupby(col)`: the source frame plus the sorted distinct group keys. -/
structure GroupBy where
  byCol : String
  keys  : List String
  df    : DataFrame

/-- Order two key cells: numeric keys by value, others lexicographically. -/
private def cellLe (a b : Cell) : Bool :=
  match a.toFloat?, b.toFloat? with
  | some x, some y => decide (x ≤ y)
  | _, _           => compare a.toStr b.toStr != Ordering.gt

private def insCell (x : Cell) : List Cell → List Cell
  | []      => [x]
  | y :: ys => if cellLe x y then x :: y :: ys else y :: insCell x ys

private def sortCells (xs : List Cell) : List Cell := xs.foldr insCell []

/-- `df.groupby(col)` — distinct values of `col`, sorted, become the group keys. -/
def DataFrame.groupby (df : DataFrame) (byCol : String) : GroupBy :=
  let keyCells := (df.colCells? byCol).getD []
  let distinct := keyCells.foldl
    (fun acc c => if acc.any (fun d => d.toStr == c.toStr) then acc else acc ++ [c]) []
  { byCol, keys := (sortCells distinct).map Cell.toStr, df }

/-- Aggregate every non-key column within each group with `f`, producing a frame indexed by keys. -/
def GroupBy.agg (g : GroupBy) (f : Series → Cell) : DataFrame :=
  let keyCells := (g.df.colCells? g.byCol).getD []
  let others := g.df.cols.filter (fun col => col.1 != g.byCol)
  let aggCols := others.map fun col =>
    let perKey := g.keys.map fun k =>
      let selected := (keyCells.zip col.2).filterMap fun p => if p.1.toStr == k then some p.2 else none
      f { values := selected, index := [], name := col.1 }
    (col.1, perKey)
  { cols := aggCols, index := g.keys }

/-- `g.sum()` per group (dtype-preserving). -/
def GroupBy.sum (g : GroupBy) : DataFrame := g.agg Series.sum

/-- `g.mean()` per group. -/
def GroupBy.mean (g : GroupBy) : DataFrame := g.agg (fun s => Cell.float s.mean)

/-- `g.min()` per group. -/
def GroupBy.min (g : GroupBy) : DataFrame := g.agg Series.min

/-- `g.max()` per group. -/
def GroupBy.max (g : GroupBy) : DataFrame := g.agg Series.max

/-- `g.count()` per group. -/
def GroupBy.count (g : GroupBy) : DataFrame := g.agg (fun s => Cell.int (Int.ofNat s.count))

end Libraries.pandas
