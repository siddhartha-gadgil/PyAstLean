# PastaLeanCHECK START
# TARGET: command
# CHECK: def dict_views :=
# CHECK: let d := Std.HashMap.ofList
# CHECK: let its := PastaLean.pyItems d
# CHECK: let ks := PastaLean.pyKeys d
# CHECK: let vs := PastaLean.pyValues d
# CHECK: def dict_len :=
# CHECK: pyLen d
# PastaLeanCHECK END

def dict_views():
    d = {"a": 1, "b": 2, "c": 3}
    its = d.items()
    ks = d.keys()
    vs = d.values()
    return its, ks, vs

def dict_len():
    d = {"x": 10, "y": 20}
    return len(d)
