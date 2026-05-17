import PyAstLean.PyAPI

/-!
Compatibility runtime import for the project.

`PyAstLean.Basic` remains the stable entrypoint used across the code generator, while
the actual Lean implementations of translated Python runtime behavior now live in the
typed modules under `PyAstLean/PyAPI/`.
-/
