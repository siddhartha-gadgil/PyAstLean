import Mathlib
import PyAstLean.PyAPI.CommonProtocols.Bool
import PyAstLean.PyAPI.CommonProtocols.Iterable

namespace PyAstLean

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
