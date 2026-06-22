# PastaLeanCHECK START
# TARGET: command
# CHECK: def floor_demo := fun x ↦ Libraries.math.pyMathFloor x
# CHECK: def ceil_demo := fun x ↦ Libraries.math.pyMathCeil x
# CHECK: def trunc_demo := fun x ↦ Libraries.math.pyMathTrunc x
# CHECK: def fabs_demo := fun x ↦ Libraries.math.pyMathFabs x
# CHECK: def pow_demo := fun x ↦ fun y ↦ Libraries.math.pyMathPow x y
# CHECK: def atan2_demo := fun y ↦ fun x ↦ Libraries.math.pyMathAtan2 y x
# CHECK: def hypot_demo := fun x ↦ fun y ↦ Libraries.math.pyMathHypot x y
# CHECK: def log_demo := fun x ↦ Libraries.math.pyMathLog2 x +ₚ Libraries.math.pyMathLog10 x
# CHECK: def angle_demo := fun x ↦ Libraries.math.pyMathDegrees x +ₚ Libraries.math.pyMathRadians x
# CHECK: def comb_perm_demo := fun n ↦ fun k ↦ Libraries.math.pyMathComb n k +ₚ Libraries.math.pyMathPerm n k
# PastaLeanCHECK END

import math
from math import ceil, trunc, fabs, log2, log10, degrees, radians


def floor_demo(x):
    x = x if x >= 0 else x - 1
    return math.floor(x)

def ceil_demo(x):
    return ceil(x)


def trunc_demo(x):
    return trunc(x)


def fabs_demo(x):
    return fabs(x)


def pow_demo(x, y):
    return math.pow(x, y)


def atan2_demo(y, x):
    return math.atan2(y, x)


def hypot_demo(x, y):
    return math.hypot(x, y)


def log_demo(x):
    return log2(x) + log10(x)


def angle_demo(x):
    return degrees(x) + radians(x)


def comb_perm_demo(n, k):
    return math.comb(n, k) + math.perm(n, k)
