# PastaLeanCHECK START
# TARGET: command
# CHECK: def read_int_list : IO (List Int) := do
# CHECK: let mut xs :=
# CHECK: pyList
# CHECK: pyMap pyInt
# CHECK: PastaLean.pyStringSplit
# CHECK: PastaLean.pyInputIO ""
# CHECK: return xs
# PastaLeanCHECK END

def read_int_list():
    xs = list(map(int, input().split()))
    return xs
