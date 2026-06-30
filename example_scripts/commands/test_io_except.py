#!/usr/bin/env python3
"""Test that exceptions with real IO use PyExcept."""

# CHECK: def get_validated : PyExcept Int
def get_validated() -> int:
    x = int(input())  # Real IO - should force PyExcept even in prove mode
    if x < 0:
        raise ValueError("negative")
    return x
