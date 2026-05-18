# PYASTLEANCHECK START
# TARGET: command
# CHECK: def builtin_len_sorted :=
# CHECK: let xs := [(5 : Int), (1 : Int), (3 : Int)]
# CHECK: let s := "dbca"
# CHECK: let d := Std.HashMap.ofList
# CHECK: let lx := pyLen xs
# CHECK: let ls := pyLen s
# CHECK: let ld := pyLen d
# CHECK: let sx := pySort xs
# CHECK: let ss := pySort s
# CHECK: let sd := pySort d
# CHECK: (lx, (ls, (ld, (sx, (ss, sd)))))
# CHECK: def in_place_sort :=
# CHECK: let mut xs := [(4 : Int), (1 : Int), (3 : Int), (2 : Int)]
# CHECK: xs := PyAstLean.pySort xs
# CHECK: return xs
# PYASTLEANCHECK END

def builtin_len_sorted():
    xs = [5, 1, 3]
    s = "dbca"
    d = {"z": 9, "a": 1, "m": 4}
    lx = len(xs)
    ls = len(s)
    ld = len(d)
    sx = sorted(xs)
    ss = sorted(s)
    sd = sorted(d)
    return lx, ls, ld, sx, ss, sd


def in_place_sort():
    xs = [4, 1, 3, 2]
    xs.sort()
    return xs
