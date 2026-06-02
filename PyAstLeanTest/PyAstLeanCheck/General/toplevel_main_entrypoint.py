# PYASTLEANCHECK START
# TARGET: command
# CHECK: def _main :=
# CHECK: "hello"
# CHECK: def main : IO Unit := do
# CHECK: PyAstLean.pyPrintIO [_main]
# CHECK: pure ()
# PYASTLEANCHECK END

# Lean reserves `main` for the executable entry point, while Python's `main()` is just a
# function. When both a `def main()` and an `if __name__ == "__main__"` guard exist, the
# Python function yields the name to the guard: it is renamed to `_main` (along with every
# call site), and the guard body becomes Lean's `def main : IO Unit`.

def main():
    return "hello"

if __name__ == "__main__":
    print(main())
