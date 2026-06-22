# PastaLeanCHECK START
# TARGET: command
# CHECK: private def _main :=
# CHECK: "helper"
# CHECK: def main' :=
# CHECK: _main
# CHECK: def main : IO Unit := do
# CHECK: PastaLean.pyPrintIO [main']
# CHECK-NOT: private def main'
# PastaLeanCHECK END

# Regression: a user-defined `_main` helper must not collide with the renamed entry point.
# Python's `main()` is renamed to `main'` (not `_main`) when it coexists with a `__main__`
# guard, precisely so the existing `_main` helper is left untouched. Here `_main` stays a
# `private def _main` (its own name), `main` becomes `main'`, the call `main()` inside the
# guard is rewritten to `main'`, and the guard owns Lean's `def main : IO Unit`.

def _main():
    return "helper"

def main():
    return _main()

if __name__ == "__main__":
    print(main())
