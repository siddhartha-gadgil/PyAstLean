# PYASTLEANCHECK START
# TARGET: command
# CHECK: def string_pipeline :=
# CHECK: let s := "  Py Ast Lean  "
# CHECK: let trimmed := PyAstLean.pyStringStrip s
# CHECK: let lowered := PyAstLean.pyStringLower trimmed
# CHECK: let parts := PyAstLean.pyStringSplit lowered
# CHECK: let glued := PyAstLean.pyStringJoin "-" parts
# CHECK: glued
# CHECK: def list_pipeline :=
# CHECK: let mut xs := [(3 : Int), (1 : Int)]
# CHECK: xs := PyAstLean.pyAppend xs (2 : Int)
# CHECK: xs := PyAstLean.pySort xs
# CHECK: let mut count := pyLen xs
# CHECK: return ((xs, count))
# PYASTLEANCHECK END

def string_pipeline():
    s = "  Py Ast Lean  "
    trimmed = s.strip()
    lowered = trimmed.lower()
    parts = lowered.split()
    glued = "-".join(parts)
    return glued


def list_pipeline():
    xs = [3, 1]
    xs.append(2)
    xs.sort()
    count = len(xs)
    return xs, count
