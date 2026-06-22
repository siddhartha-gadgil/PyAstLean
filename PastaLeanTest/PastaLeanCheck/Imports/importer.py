# Imports the public names from `mathlib_module` and uses them. The generated Lean must
# emit `import Mathlib_module` (capitalized module path) and resolve the public names,
# while the private (`_`/`__`-prefixed) names stay unreachable across the import boundary.

from mathlib_module import add, scale, PUBLIC_CONST

def compute():
    doubled = scale([1, 2, 3], 2)
    return add(PUBLIC_CONST, doubled[0])
