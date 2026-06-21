import Mathlib
import PastaLean.PyAPI.Strings
import PastaLean.PyAPI.Lists

namespace PastaLean

class PyFind (α β: Type) where
  /-- For `find()`, return the index of the first occurrence of the given element, or `none` if not found. -/
  pyFind : α → β → Int

def pyFind {α β} [PyFind α β] : α → β → Int :=
  PyFind.pyFind

instance [DecidableEq α] : PyFind (List α) α where
  pyFind := pyListFind

instance : PyFind String String where
  pyFind := pyStringFind
