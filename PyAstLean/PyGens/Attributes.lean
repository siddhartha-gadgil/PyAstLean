import PyAstLean.Attributes

/-!
Compatibility wrapper for older imports.

The method-dispatch table now lives in `PyAstLean.Attributes`, but much of the
codegen layer still imports `PyAstLean.PyGens.Attributes`. Keeping this wrapper
preserves that import path while the runtime/codegen layout evolves.
-/
