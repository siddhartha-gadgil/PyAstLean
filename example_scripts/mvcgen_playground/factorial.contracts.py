from contracts import *


def factorial(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() >= 1)
    result = 1
    i = 1
    while i <= n:
        Invariant(i >= 1)
        Invariant(n - i + 1 >= 0)
        Invariant(result >= 1)
        Decreases(n - i + 1)
        result = result * i
        i = i + 1
    return result