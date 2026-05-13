# PYASTLEANCHECK START
# TARGET: term
# CHECK: fun n ↦
# CHECK: Id.run
# CHECK: let mut total := (0 : Int)
# CHECK: while total < n do
# CHECK: total := total +ₚ (1 : Int)
# CHECK: return total
# PYASTLEANCHECK END

def count_to(n):
    total = 0
    while total < n:
        total += 1
    return total
