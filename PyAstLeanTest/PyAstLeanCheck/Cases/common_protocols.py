# PYASTLEANCHECK START
# TARGET: command
# CHECK: def len_protocols :=
# CHECK: let xs := [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: let s := "hello"
# CHECK: let d := Std.HashMap.ofList
# CHECK: let lx := pyLen xs
# CHECK: let ls := pyLen s
# CHECK: let ld := pyLen d
# CHECK: def iteration_protocols :=
# CHECK: List.map (fun x => x) xs
# PYASTLEANCHECK END

def len_protocols():
    xs = [1, 2, 3]
    s = "hello"
    d = {"a": 1}
    lx = len(xs)
    ls = len(s)
    ld = len(d)
    return lx, ls, ld

def iteration_protocols():
    xs = [4, 5, 6]
    return [x for x in xs]
