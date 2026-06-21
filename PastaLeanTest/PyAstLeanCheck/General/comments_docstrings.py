# PastaLeanCHECK START
# TARGET: command
# CHECK: -- module comment
# CHECK: /-
# CHECK: module doc
# CHECK: second line
# CHECK: -/
# CHECK: def f := fun x ↦
# CHECK: -- function comment
# CHECK: /-
# CHECK: function doc
# CHECK: -/
# CHECK: -- before assign
# CHECK: let y := x +ₚ (1 : Int)
# CHECK: -- before return
# CHECK: y
# PastaLeanCHECK END

# module comment
"""module doc
second line"""

def f(x):
    # function comment
    """function doc"""
    # before assign
    y = x + 1
    # before return
    return y











