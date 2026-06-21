# PastaLeanCHECK START
# TARGET: command
# CHECK: def main' :=
# CHECK: "hello"
# CHECK: def main : IO Unit := do
# CHECK: PastaLean.pyPrintIO [main']
# CHECK: pure ()
# PastaLeanCHECK END

# Lean reserves `main` for the executable entry point, while Python's `main()` is just a
# function. When both a `def main()` and an `if __name__ == "__main__"` guard exist, the
# Python function yields the name to the guard: it is renamed to `main'` (along with every
# call site), and the guard body becomes Lean's `def main : IO Unit`. We use `main'` rather
# than `_main` because `'` is unusable in a Python identifier, so it can never collide with
# a user-defined helper (a `_main` helper, by contrast, is perfectly legal Python).

def main():
    return "hello"

if __name__ == "__main__":
    print(main())
