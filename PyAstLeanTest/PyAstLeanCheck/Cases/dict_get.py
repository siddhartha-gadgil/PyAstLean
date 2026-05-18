# PYASTLEANCHECK START
# TARGET: command
# CHECK: def dict_get_variants :=
# CHECK: let d := Std.HashMap.ofList
# CHECK: let found := PyAstLean.pyGetOpt d "apple"
# CHECK: let missing := PyAstLean.pyGetOpt d "pear"
# CHECK: let fallback := PyAstLean.pyGetD d "pear" (999 : Int)
# CHECK: (found, (missing, fallback))
# CHECK: def dict_get_len_mix :=
# CHECK: let d := Std.HashMap.ofList
# CHECK: let got := PyAstLean.pyGetD d "x" (0 : Int)
# CHECK: let size := pyLen d
# CHECK: (got, size)
# PYASTLEANCHECK END

def dict_get_variants():
    d = {"apple": 10, "banana": 20}
    found = d.get("apple")
    missing = d.get("pear")
    fallback = d.get("pear", 999)
    return found, missing, fallback


def dict_get_len_mix():
    d = {"x": 7, "y": 9}
    got = d.get("x", 0)
    size = len(d)
    return got, size
