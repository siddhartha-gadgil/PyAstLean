# PYASTLEANCHECK START
# TARGET: command
# CHECK: def dict_views :=
# CHECK: let d := Std.HashMap.ofList
# CHECK: let its := PyAstLean.pyItems d
# CHECK: let ks := PyAstLean.pyKeys d
# CHECK: let vs := PyAstLean.pyValues d
# CHECK: def dict_len :=
# CHECK: pyLen d
# PYASTLEANCHECK END

def dict_views():
    d = {"a": 1, "b": 2, "c": 3}
    its = d.items()
    ks = d.keys()
    vs = d.values()
    return its, ks, vs

def dict_len():
    d = {"x": 10, "y": 20}
    return len(d)
