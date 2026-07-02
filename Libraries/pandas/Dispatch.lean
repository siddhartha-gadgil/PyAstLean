import Libraries.pandas.GroupBy

/-!
# Overloaded method dispatch (`df.sum()` vs `s.sum()`)

The codegen member map (`pythonPandasMemberMap?`) can only return one Lean name per Python method,
but `sum`/`mean`/`head`/… exist on both `Series` and `DataFrame` with *different* result types
(`Series.sum : Float`, `DataFrame.sum : Series`). So instead of mapping to a concrete function, we
map to a small typeclass method and let instance resolution pick the implementation from the
receiver's type. The result type is an `outParam` so callers never annotate it — the same pattern the
runtime protocols in `PyAPI/CommonProtocols` use.
-/

namespace Libraries.pandas

/-- `x.sum()`. -/
class PySum      (α : Type) (β : outParam Type) where pySum      : α → β
/-- `x.mean()`. -/
class PyMean     (α : Type) (β : outParam Type) where pyMean     : α → β
/-- `x.min()`. -/
class PyMin      (α : Type) (β : outParam Type) where pyMin      : α → β
/-- `x.max()`. -/
class PyMax      (α : Type) (β : outParam Type) where pyMax      : α → β
/-- `x.std()`. -/
class PyStd      (α : Type) (β : outParam Type) where pyStd      : α → β
/-- `x.describe()`. -/
class PyDescribe (α : Type) (β : outParam Type) where pyDescribe : α → β
/-- `x.head(n=5)`. -/
class PyHead     (α : Type) where pyHead : α → optParam Nat 5 → α
/-- `x.tail(n=5)`. -/
class PyTail     (α : Type) where pyTail : α → optParam Nat 5 → α

instance : PySum      Series    Cell      := ⟨Series.sum⟩
instance : PySum      DataFrame Series    := ⟨DataFrame.sum⟩
instance : PyMean     Series    Float     := ⟨Series.mean⟩
instance : PyMean     DataFrame Series    := ⟨DataFrame.mean⟩
instance : PyMin      Series    Cell      := ⟨Series.min⟩
instance : PyMin      DataFrame Series    := ⟨DataFrame.min⟩
instance : PyMax      Series    Cell      := ⟨Series.max⟩
instance : PyMax      DataFrame Series    := ⟨DataFrame.max⟩
instance : PyStd      Series    Float     := ⟨fun s => s.std⟩
instance : PyStd      DataFrame Series    := ⟨DataFrame.std⟩
instance : PyDescribe Series    Series    := ⟨Series.describe⟩
instance : PyDescribe DataFrame DataFrame := ⟨DataFrame.describe⟩
instance : PyHead     Series              := ⟨fun s n => s.head n⟩
instance : PyHead     DataFrame           := ⟨fun df n => df.head n⟩
instance : PyTail     Series              := ⟨fun s n => s.tail n⟩
instance : PyTail     DataFrame           := ⟨fun df n => df.tail n⟩

-- GroupBy aggregations (`df.groupby(k).mean()`, …) → a frame indexed by the group keys.
instance : PySum      GroupBy   DataFrame := ⟨GroupBy.sum⟩
instance : PyMean     GroupBy   DataFrame := ⟨GroupBy.mean⟩
instance : PyMin      GroupBy   DataFrame := ⟨GroupBy.min⟩
instance : PyMax      GroupBy   DataFrame := ⟨GroupBy.max⟩

end Libraries.pandas
