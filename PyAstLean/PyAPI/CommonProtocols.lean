import PyAstLean.PyAPI.CommonProtocols.Length
import PyAstLean.PyAPI.CommonProtocols.Membership
import PyAstLean.PyAPI.CommonProtocols.Iterable

/-!
Intentionally extensible runtime protocols shared by several Lean datatypes.

Use this directory only when a Python operation should expose one stable public Lean
name, while the concrete implementation should vary by argument type through
typeclass resolution.

Examples:
- `pyLen`
- `pyContains`
- `pyIter`

Do not put every reusable helper here. String-only, list-only, or dict-only runtime
functions should stay in their type-specific files until there is a deliberate need
to promote them into a shared protocol.
-/
