# PastaLeanCHECK START
# TARGET: command
# CHECK: def read_line : IO String := do
# CHECK: let mut raw := (← PastaLean.pyInputIO "")
# CHECK: return raw
# CHECK: def read_prompted : IO String := do
# CHECK: return ((← PastaLean.pyInputIO "n = "))
# CHECK: def read_nested_int :=
# CHECK: let mut a := PastaLean.pyInt (← PastaLean.pyInputIO "")
# CHECK: let mut b := PastaLean.pyInt (← PastaLean.pyInputIO "")
# CHECK: let mut c := (← PastaLean.pyInputIO "")
# CHECK: a := a +ₚ b
# CHECK: return ((a, c))
# CHECK: def echo_input : IO Int := do
# CHECK: let __py_input0 ← PastaLean.pyInputIO ""
# CHECK: let __py_result ← PastaLean.pyPrintIO [__py_input0]
# CHECK: return (0 : Int)
# CHECK: def input_inside_print :=
# CHECK: let __py_input0 ← PastaLean.pyInputIO ""
# CHECK: PastaLean.pyPrintIO
# CHECK: Enter a number:
# CHECK: PastaLean.pyInt __py_input0
# PastaLeanCHECK END

def read_line():
    raw = input()
    return raw


def read_prompted():
    return input("n = ")


def read_nested_int():
    a = int(input())
    b = int(input())
    c = input()
    a += b
    return (a,c)


def echo_input():
    print(input())
    return 0

def input_inside_print():
    print(f"Enter a number: {int(input())}")
