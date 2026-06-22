# Assert statements: inline (inside a function) and top-level (outside any function).
GREETING: str = "hi"

# top-level assert — outside any function
assert len(GREETING) == 2


def checked_add(a: int, b: int) -> int:
    # inline asserts inside a function body
    assert a == a
    assert a + b >= a + b
    return a + b
