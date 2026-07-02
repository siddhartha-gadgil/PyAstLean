

# While-loop product accumulator with an explicit termination measure (Decreases).
# Maintainable invariant: the running product stays >= 1 (so it is never zero / negative).
def factorial(n: int) -> int:
    result = 1
    i = 1
    while i <= n:
        result = result * i
        i = i + 1
    return result
