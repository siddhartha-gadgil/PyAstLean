#!/usr/bin/env python3
"""Test that pure exceptions (no IO) use PyExceptId in prove mode."""

# CHECK: def validate : Int → PyExceptId Int
def validate(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x * 2

# CHECK: def validate_with_print : Int → PyExceptId Int
def validate_with_print(x: int) -> int:
    print(x)  # In prove mode, this should not force IO
    if x < 0:
        raise ValueError("negative")
    return x * 2
