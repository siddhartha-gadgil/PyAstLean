import Libraries.pandas.DataFrame
import Libraries.pandas.SeriesStats

/-!
# pandas `DataFrame` — statistics

Column-wise reductions. Each treats a column as a `Series` and reduces it, returning a `Series`
indexed by the column names (like pandas' `df.sum()`, `df.mean()`, …). Dtype fidelity carries
through: `df.sum()`/`min`/`max` keep each integer column integer; `mean`/`std` are float. `describe`
returns a `DataFrame` whose rows are the summary statistics.
-/

namespace Libraries.pandas
namespace DataFrame

/-- Column-wise reduction to a `Series` (of cells) indexed by column name. -/
private def reduceCols (df : DataFrame) (f : Series → Cell) : Series :=
  { values := df.cols.map fun (nm, c) => f { values := c, index := df.index, name := nm },
    index := df.getColumns, name := "" }

/-- `df.sum()` per column (dtype-preserving). -/
def sum (df : DataFrame) : Series := reduceCols df Series.sum

/-- `df.mean()` per column (float). -/
def mean (df : DataFrame) : Series := reduceCols df (fun s => Cell.float s.mean)

/-- `df.min()` per column (dtype-preserving). -/
def min (df : DataFrame) : Series := reduceCols df Series.min

/-- `df.max()` per column (dtype-preserving). -/
def max (df : DataFrame) : Series := reduceCols df Series.max

/-- `df.std()` per column (sample, `ddof=1`, float). -/
def std (df : DataFrame) : Series := reduceCols df (fun s => Cell.float s.std)

/-- `df.describe()` — per-column count/mean/std/min/quartiles/max as a `DataFrame`
(rows are the statistics, columns are the original columns). -/
def describe (df : DataFrame) : DataFrame :=
  let stats := ["count", "mean", "std", "min", "25%", "50%", "75%", "max"]
  let describedCols := df.cols.map fun (nm, c) =>
    (nm, (Series.describe { values := c, index := df.index, name := nm }).values)
  { cols := describedCols, index := stats }

end DataFrame
end Libraries.pandas
