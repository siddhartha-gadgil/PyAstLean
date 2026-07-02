import Libraries.pandas.DataFrameStats
import Libraries.pandas.SeriesStats
import Libraries.pandas.Dispatch
import Libraries.pandas.GroupBy
import Libraries.pandas.CSV
import Libraries.pandas.Subscript

/-!
# pandas library tests

Behaviour checks against real pandas semantics: `skipna=True` reductions, sample std (`ddof=1`),
linear-interpolated quantiles, ordered columns, and value-preserving transforms. Numeric results
`#eval` as `Float` (6-decimal repr); cell results use `Cell.toStr` for readable output.
-/

namespace Libraries.pandas

/-- A small integer series `[1, 2, 3, 4]`. -/
def s : Series := Series.ofList [1, 2, 3, 4]

-- ==================== Series: reductions ====================

-- Integer column ⇒ integer result (dtype preserved), rendered pandas-style via `Cell.toStr`.
/-- info: "10" -/
#guard_msgs in #eval s.sum.toStr

/-- info: 2.500000 -/
#guard_msgs in #eval s.mean

/-- info: "1" -/
#guard_msgs in #eval s.min.toStr

/-- info: "4" -/
#guard_msgs in #eval s.max.toStr

/-- info: 4 -/
#guard_msgs in #eval s.count

/-- info: 4 -/
#guard_msgs in #eval s.size

-- Sample standard deviation (ddof = 1): sqrt((1.5²+0.5²+0.5²+1.5²)/3) = sqrt(5/3).
/-- info: 1.290994 -/
#guard_msgs in #eval s.std

/-- info: 2.500000 -/
#guard_msgs in #eval s.median

-- Linear-interpolated quartiles over [1,2,3,4].
/-- info: 1.750000 -/
#guard_msgs in #eval s.quantile 0.25

/-- info: 3.250000 -/
#guard_msgs in #eval s.quantile 0.75

-- describe() as (numeric values, labels).
/-- info: [4.000000, 2.500000, 1.290994, 1.000000, 1.750000, 2.500000, 3.250000, 4.000000] -/
#guard_msgs in #eval s.describe.numeric

/-- info: ["count", "mean", "std", "min", "25%", "50%", "75%", "max"] -/
#guard_msgs in #eval s.describe.index

-- ==================== Series: skipna (missing values) ====================

/-- A series with a missing entry: `[1, NaN, 3]`. -/
def sNA : Series := Series.ofCells [Cell.int 1, Cell.na, Cell.int 3]

-- sum/mean drop the NaN; count excludes it but size includes it. The NaN also upcasts the int
-- column to float64 (pandas rule), so the sum prints as "4.0", not "4".
/-- info: "4.0" -/
#guard_msgs in #eval sNA.sum.toStr

/-- info: 2.000000 -/
#guard_msgs in #eval sNA.mean

/-- info: 2 -/
#guard_msgs in #eval sNA.count

/-- info: 3 -/
#guard_msgs in #eval sNA.size

-- ==================== Series: transforms ====================

/-- info: [2.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in #eval (s.apply (· * 2)).numeric

/-- info: [1.000000, 3.000000, 6.000000, 10.000000] -/
#guard_msgs in #eval s.cumsum.numeric

/-- info: [11.000000, 22.000000, 33.000000] -/
#guard_msgs in #eval (Series.add (Series.ofList [1, 2, 3]) (Series.ofList [10, 20, 30])).numeric

/-- info: [1.000000, 2.000000, 3.000000] -/
#guard_msgs in #eval (Series.ofList [3, 1, 2]).sortValues.numeric

/-- info: [3.000000, 2.000000, 1.000000] -/
#guard_msgs in #eval (Series.ofList [3, 1, 2]).sortValues (ascending := false) |>.numeric

/-- info: [1.000000, 2.000000, 3.000000] -/
#guard_msgs in #eval (Series.ofList [1, 1, 2, 3, 3]).unique.numeric

/-- info: [1.200000, 5.700000] -/
#guard_msgs in #eval (Series.ofList [1.234, 5.678]).round 1 |>.numeric

-- Positional / label access (Python-style negative index).
/-- info: "10" -/
#guard_msgs in #eval (Series.ofList [10, 20, 30] |>.iloc 0).toStr

/-- info: "30" -/
#guard_msgs in #eval (Series.ofList [10, 20, 30] |>.iloc (-1)).toStr

-- ==================== DataFrame: construction & access ====================

/-- `pd.DataFrame([[1,2],[3,4]], columns=["a","b"])` (rows: [1,2] then [3,4]). -/
def df : DataFrame := DataFrame.pyDataFrame [[1, 2], [3, 4]] (columns := some ["a", "b"])

/-- info: ["a", "b"] -/
#guard_msgs in #eval df.getColumns

/-- info: (2, 2) -/
#guard_msgs in #eval df.shape

/-- info: ["0", "1"] -/
#guard_msgs in #eval df.getIndex

-- Column `a` is the first entry of each row: [1, 3].
/-- info: [1.000000, 3.000000] -/
#guard_msgs in #eval (df.getColumn "a").numeric

/-- info: "1" -/
#guard_msgs in #eval (df.getAt "0" "a").toStr

/-- info: "4" -/
#guard_msgs in #eval (df.iat 1 1).toStr

-- ==================== DataFrame: column-wise reductions ====================

-- Per-column sums: a → 1+3 = 4, b → 2+4 = 6 (integer columns stay integer).
/-- info: ["4", "6"] -/
#guard_msgs in #eval df.sum.values.map (·.toStr)

/-- info: ["2.0", "3.0"] -/
#guard_msgs in #eval df.mean.values.map (·.toStr)

/-- info: ["1", "2"] -/
#guard_msgs in #eval df.min.values.map (·.toStr)

/-- info: ["3", "4"] -/
#guard_msgs in #eval df.max.values.map (·.toStr)

-- describe() keeps column order and labels the statistic rows.
/-- info: ["a", "b"] -/
#guard_msgs in #eval df.describe.getColumns

/-- info: ["count", "mean", "std", "min", "25%", "50%", "75%", "max"] -/
#guard_msgs in #eval df.describe.getIndex

-- ==================== DataFrame: mutation (order preserved) ====================

/-- info: ["a", "b", "c"] -/
#guard_msgs in #eval (df.insertColumn "c" [Cell.int 5, Cell.int 6]).getColumns

/-- info: ["b"] -/
#guard_msgs in #eval (df.dropColumn "a").getColumns

-- ==================== Overloaded dispatch (one name, both types) ====================

-- `PySum.pySum` resolves to `Series.sum` (→ Cell) on a series …
/-- info: "10" -/
#guard_msgs in #eval (PySum.pySum s).toStr

-- … and to `DataFrame.sum` (→ Series over columns) on a frame, from the *same* name.
/-- info: ["4", "6"] -/
#guard_msgs in #eval (PySum.pySum df).values.map (·.toStr)

/-- info: 2.500000 -/
#guard_msgs in #eval (PyMean.pyMean s : Float)

/-- info: [2.000000, 3.000000] -/
#guard_msgs in #eval (PyMean.pyMean df).numeric

-- head/tail dispatch (same-type result), with an explicit n.
/-- info: [1.000000, 2.000000] -/
#guard_msgs in #eval (PyHead.pyHead s 2).numeric

/-- info: ["a", "b"] -/
#guard_msgs in #eval (PyHead.pyHead df 1).getColumns

-- ==================== pandas-style repr (print) ====================

/--
info: 0    1
1    2
2    3
3    4
dtype: int64
-/
#guard_msgs in #eval s.printSeries

/--
info:    a  b
0  1  2
1  3  4
-/
#guard_msgs in #eval df.printDf

-- ==================== groupby ====================

/-- Key column `k` = ["a","b","a","b"], value column `v` = [1,2,3,4]. -/
def dfg : DataFrame :=
  DataFrame.ofColumns [("k", toCells ["a", "b", "a", "b"]), ("v", toCells [1, 2, 3, 4])]

-- Groups: a → rows 0,2 (v = 1,3); b → rows 1,3 (v = 2,4). Keys sorted.
/-- info: ["a", "b"] -/
#guard_msgs in #eval (dfg.groupby "k").sum.getIndex

-- sum per group: a → 4, b → 6 (integer dtype preserved).
/-- info: ["4", "6"] -/
#guard_msgs in #eval ((dfg.groupby "k").sum.getColumn "v").values.map (·.toStr)

-- mean per group: a → 2.0, b → 3.0.
/-- info: ["2.0", "3.0"] -/
#guard_msgs in #eval ((dfg.groupby "k").mean.getColumn "v").values.map (·.toStr)

-- count per group.
/-- info: ["2", "2"] -/
#guard_msgs in #eval ((dfg.groupby "k").count.getColumn "v").values.map (·.toStr)

/--
info:    v
a  4
b  6
-/
#guard_msgs in #eval (dfg.groupby "k").sum.printDf

-- ==================== CSV round-trip ====================

/-- info: ["a", "b"] -/
#guard_msgs in #eval (parseCsvString "a,b\n1,2\n3,4").getColumns

-- Numeric fields infer the right dtype: integers …
/-- info: "int64" -/
#guard_msgs in #eval ((parseCsvString "a,b\n1,2\n3,4").getColumn "a").dtype.toStr

-- … floats …
/-- info: "float64" -/
#guard_msgs in #eval ((parseCsvString "x\n1.5\n2.5").getColumn "x").dtype.toStr

-- … and non-numeric fields stay strings (object dtype).
/-- info: "object" -/
#guard_msgs in #eval ((parseCsvString "n\nhi\nyo").getColumn "n").dtype.toStr

-- render back to CSV text (header + rows, no index).
/-- info: "a,b\n1,2\n3,4" -/
#guard_msgs in #eval df.toCsvString

-- ==================== subscript & boolean filtering ====================

-- `df["a"]` via the `PyGetItem` instance (what transpiled `df["a"]` lowers to).
/-- info: ["1", "3"] -/
#guard_msgs in #eval (PastaLean.pyGetItem df "a" : Series).values.map (·.toStr)

-- `s[i]` cell access through the subscript protocol.
/-- info: "20" -/
#guard_msgs in #eval (PastaLean.pyGetItem (Series.ofList [10, 20, 30]) (1 : Int)).toStr

-- Boolean filtering: keep rows where column `a` > 1 (mask from `gtScalar`). Row 0 (a=1) drops.
/-- info: ["3"] -/
#guard_msgs in #eval (df.filter ((df.getColumn "a").gtScalar 1) |>.getColumn "a").values.map (·.toStr)

/-- info: ["4"] -/
#guard_msgs in #eval (df.filter ((df.getColumn "a").gtScalar 1) |>.getColumn "b").values.map (·.toStr)

end Libraries.pandas
