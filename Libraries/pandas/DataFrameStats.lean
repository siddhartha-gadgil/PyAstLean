import Libraries.pandas.DataFrame
import Libraries.pandas.SeriesStats

/-!
# pandas `DataFrame` — statistics

Column-wise reductions. Each treats a column as a `Series` and reduces it, returning a `Series`
indexed by the column names (exactly like pandas' `df.sum()`, `df.mean()`, …). `describe` returns a
`DataFrame` whose rows are the summary statistics.
-/

namespace Libraries.pandas
namespace DataFrame

/-- Column-wise reduction to a `Series` indexed by column name. -/
private def reduceCols (df : DataFrame) (f : Series → Float) : Series :=
  let names := df.getColumns
  let vals  := df.cols.map fun (nm, c) => Cell.float (f { values := c, index := df.index, name := nm })
  { values := vals, index := names, name := "" }

/-- `df.sum()` per column. -/
def sum (df : DataFrame) : Series := reduceCols df Series.sum

/-- `df.mean()` per column. -/
def mean (df : DataFrame) : Series := reduceCols df Series.mean

/-- `df.min()` per column. -/
def min (df : DataFrame) : Series := reduceCols df Series.min

/-- `df.max()` per column. -/
def max (df : DataFrame) : Series := reduceCols df Series.max

/-- `df.std()` per column (sample, `ddof=1`). -/
def std (df : DataFrame) : Series := reduceCols df (Series.std ·)

/-- `df.describe()` — per-column count/mean/std/min/quartiles/max as a `DataFrame`
(rows are the statistics, columns are the original columns). -/
def describe (df : DataFrame) : DataFrame :=
  let stats := ["count", "mean", "std", "min", "25%", "50%", "75%", "max"]
  let describedCols := df.cols.map fun (nm, c) =>
    (nm, (Series.describe { values := c, index := df.index, name := nm }).values)
  { cols := describedCols, index := stats }

end DataFrame
end Libraries.pandas
