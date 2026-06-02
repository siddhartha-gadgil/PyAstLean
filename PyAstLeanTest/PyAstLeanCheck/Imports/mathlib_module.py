# A "library" Python module: it defines public functions/constants that another file
# imports, plus private (`_`-prefixed) helpers that must NOT be importable.
#
# When converted to Lean this becomes a module whose top-level `def`s are globally
# available after `import`, except the `private def`s (the `_`/`__`-prefixed names).

def add(a, b):
    return a + b

def scale(xs, factor):
    return [x * factor for x in xs]

PUBLIC_CONST = 42

def __version__():
    return 1

def _internal_helper(x):
    return x + 1

__SECRET = 99
