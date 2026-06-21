import Mathlib
import PastaLean.PyAPI.Strings
import PastaLean.PyAPI.Lists
import PastaLean.PyAPI.Dicts

namespace PastaLean

class PyCount (α β: Type) where
  /-- For `count()`, return the number of occurrences of the given element. -/
  pyCount : α → β → Int

/- Public runtime for `count()`-/
def pyCount {α β} [PyCount α β] : α → β → Int :=
  PyCount.pyCount

instance : PyCount String String where
  pyCount := pyStringCount

instance [DecidableEq α] : PyCount (List α) α where
  pyCount := pyListCount

end PastaLean
