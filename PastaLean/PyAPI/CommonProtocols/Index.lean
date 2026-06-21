import Mathlib
import PastaLean.PyAPI.Strings
import PastaLean.PyAPI.Lists

namespace PastaLean
class PyIndex (α β: Type) where
  /-- For `index()`, return the index of the first occurrence of the given element. -/
  pyIndex : α → β → Int

/- Public runtime for `index()`-/
def pyIndex {α β} [PyIndex α β] : α → β → Int :=
  PyIndex.pyIndex

instance [DecidableEq α] : PyIndex (List α) α where
  pyIndex := pyListIndex

instance : PyIndex String String where
  pyIndex := pyStringIndex

end PastaLean
