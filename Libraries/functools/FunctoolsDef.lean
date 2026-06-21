import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace Libraries.functools

/--
Runtime helper for `functools.reduce(function, iterable[, initializer])`.

The iterable comes first in the Lean helper so instance resolution can learn the
element type before elaborating the reducer lambda. That keeps overloaded arithmetic
inside generated lambdas much more predictable.
-/
def pyReduce {α β : Type} [inst : PastaLean.PyIterable α β] [Inhabited β] (xs : α)
    (f : β → β → β) (init : Option β := none) : β :=
  match init, PastaLean.pyIter xs with
  | some start, items => items.foldl f start
  | none, [] => panic! "TypeError: reduce() of empty iterable with no initial value"
  | none, x :: rest => rest.foldl f x

end Libraries.functools
