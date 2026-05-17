import Mathlib

namespace PyAstLean

/-- Minimal runtime value for translated Python exceptions. -/
structure PyException where
  kind : String
  msg : String
  deriving Inhabited, Repr, BEq

namespace PyException

/-- Smart constructor used by codegen so generated Lean does not need to expose `.mk`. -/
def Raise (kind : String) (msg : String := "") : PyException :=
  .mk kind msg

/-- Accessor used by generated code when matching caught exceptions by kind. -/
def OfKind (exc : PyException) : String :=
  exc.kind

end PyException

/-- Concrete exception monad used for translated Python code that can raise. -/
abbrev PyExcept (α : Type) := ExceptT PyException Id α

instance : ToString PyException where
  toString exc :=
    if exc.msg.isEmpty then
      exc.kind
    else
      s!"{exc.kind}: {exc.msg}"

/-- Current lightweight runtime stub for Python-style printing. -/
def pyPrint {α : Type} [ToString α] (_ : α) : Unit := ()

/-- Python-style `range` supporting positive and negative steps. -/
def pyRange (stop : Int) (start : Int := 0) (step : Int := 1) : List Int := do
  if step > 0 then
    List.map (fun i => start + i) (List.range' 0 ((stop - start) / step + (stop - start) % step).toNat step.toNat)
  else if step < 0 then
    List.map (fun i => start - i) (List.range' 0 ((start - stop) / (-step) + (start - stop) % (-step)).toNat (-step).toNat)
  else
    []

end PyAstLean
