import PastaLean.PyAPI.CommonProtocols.Length
import PastaLean.PyAPI.CommonProtocols.SetItem
import PastaLean.PyAPI.CommonProtocols.GetItem
import PastaLean.PyAPI.CommonProtocols.Membership
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.CommonProtocols.Clear
import PastaLean.PyAPI.CommonProtocols.Pop
import PastaLean.PyAPI.CommonProtocols.Sorting
import PastaLean.PyAPI.CommonProtocols.Count
import PastaLean.PyAPI.CommonProtocols.Find
import PastaLean.PyAPI.CommonProtocols.Index
import PastaLean.PyAPI.CommonProtocols.Bool
import PastaLean.PyAPI.CommonProtocols.AnyFunc
import PastaLean.PyAPI.CommonProtocols.Reversed
import PastaLean.PyAPI.CommonProtocols.Truthy

/-!
Intentionally extensible runtime protocols shared by several Lean datatypes.

Use this directory only when a Python operation should expose one stable public Lean
name, while the concrete implementation should vary by argument type through
typeclass resolution.

Examples:
- `pyLen`
- `pyContains`
- `pyPop`
etc.

Do not put every reusable helper here. String-only, list-only, or dict-only runtime
functions should stay in their type-specific files until there is a deliberate need
to promote them into a shared protocol.
-/
