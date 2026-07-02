import Libraries.pandas.DataFrameStats
import Libraries.pandas.SeriesStats

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

/-- info: 10.000000 -/
#guard_msgs in #eval s.sum

/-- info: 2.500000 -/
#guard_msgs in #eval s.mean

/-- info: 1.000000 -/
#guard_msgs in #eval s.min

/-- info: 4.000000 -/
#guard_msgs in #eval s.max

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

-- sum/mean drop the NaN; count excludes it but size includes it.
/-- info: 4.000000 -/
#guard_msgs in #eval sNA.sum

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

-- Per-column sums: a → 1+3 = 4, b → 2+4 = 6.
/-- info: [4.000000, 6.000000] -/
#guard_msgs in #eval df.sum.numeric

/-- info: [2.000000, 3.000000] -/
#guard_msgs in #eval df.mean.numeric

/-- info: [1.000000, 2.000000] -/
#guard_msgs in #eval df.min.numeric

/-- info: [3.000000, 4.000000] -/
#guard_msgs in #eval df.max.numeric

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

end Libraries.pandas
