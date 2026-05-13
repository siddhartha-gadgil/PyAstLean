# PYASTLEANCHECK START
# TARGET: term
# CHECK: fun x ↦
# CHECK: if x > (0 : Int) then
# CHECK: (1 : Int)
# CHECK: else
# CHECK: (2 : Int)
# PYASTLEANCHECK END

def choose(x):
    if x > 0:
        return 1
    return 2
