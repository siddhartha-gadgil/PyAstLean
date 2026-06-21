# PastaLeanCHECK START
# TARGET: command
# CHECK: def factorial_demo := fun n ↦ Libraries.math.pyMathFactorial n
# CHECK: def alias_demo := fun a ↦ fun b ↦ Libraries.math.pyMathGcd a b
# CHECK: def from_import_demo := fun n ↦ fun a ↦ fun b ↦ Libraries.math.pyMathFactorial n +ₚ Libraries.math.pyMathGcd a b
# CHECK: def constant_demo :=
# CHECK: Libraries.math.pyMathPi
# CHECK: def sqrt_demo := fun x ↦ Libraries.math.pyMathSqrt x
# PastaLeanCHECK END

import math
import math as m
from math import factorial, gcd, sqrt


def factorial_demo(n):
    return math.factorial(n)


def alias_demo(a, b):
    return m.gcd(a, b)


def from_import_demo(n, a, b):
    return factorial(n) + gcd(a, b)


def constant_demo():
    return math.pi


def sqrt_demo(x):
    return sqrt(x)
