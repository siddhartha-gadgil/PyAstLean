import PyAstLean.PyAPI.CommonAPI.Length
import PyAstLean.PyAPI.CommonAPI.Membership
import PyAstLean.PyAPI.CommonAPI.Iterable

/-!
Cross-type Python-style runtime APIs shared by several Lean datatypes.

Use this directory for operations where codegen should emit one stable Lean name such
as `pyLen` or `pyContains`, and Lean should pick the concrete implementation from the
argument type via typeclass resolution.
-/
