import Mathlib
import PastaLean.PyAPI.CommonProtocols.Bool
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/-
This file defines the `PyAny` protocol, which is for python's `any` function. The output of this function is simply False if all elements are 0, empty, or None, and True otherwise.
-/

class PyAny (α : Type) where
  pyAny : α → Bool

def pyAny {α : Type} [PyAny α] (x : α) : Bool :=
  PyAny.pyAny x

instance {α β : Type} [PyIterable α β] [PyBool β] : PyAny α where
  pyAny x :=
    (pyIter x).any pyBool

/-
The `PyAll` protocol is Python's `all` function: `True` iff every element is truthy
(an empty iterable is `True`).
-/

class PyAll (α : Type) where
  pyAll : α → Bool

def pyAll {α : Type} [PyAll α] (x : α) : Bool :=
  PyAll.pyAll x

instance {α β : Type} [PyIterable α β] [PyBool β] : PyAll α where
  pyAll x :=
    (pyIter x).all pyBool
