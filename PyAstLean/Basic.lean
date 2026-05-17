import Lean
open Lean

def hello := "world"

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

def pyPrint {α : Type} [ToString α] (_ : α) : Unit := ()

end PyAstLean
