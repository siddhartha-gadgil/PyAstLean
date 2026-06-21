# PastaLeanCHECK START
# TARGET: command
# CHECK: def string_pipeline :=
# CHECK: let s := "  Py Ast Lean  "
# CHECK: let trimmed := PastaLean.pyStringStrip s
# CHECK: let lowered := PastaLean.pyStringLower trimmed
# CHECK: let parts := PastaLean.pyStringSplit lowered
# CHECK: let glued := PastaLean.pyStringJoin "-" parts
# CHECK: glued
# CHECK: def list_pipeline :=
# CHECK: let mut xs := [(3 : Int), (1 : Int)]
# CHECK: xs := PastaLean.pyAppend xs (2 : Int)
# CHECK: xs := PastaLean.pySort xs
# CHECK: let mut count := pyLen xs
# CHECK: return ((xs, count))
# PastaLeanCHECK END

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
