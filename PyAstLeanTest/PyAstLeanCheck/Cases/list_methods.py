# PYASTLEANCHECK START
# TARGET: command
# CHECK: def list_append_once :=
# CHECK: Id.run
# CHECK: let mut xs := [(1 : Int), (2 : Int)]
# CHECK: xs := PyAstLean.pyAppend xs (3 : Int)
# CHECK: return
# CHECK: def list_append_twice :=
# CHECK: Id.run
# CHECK: xs := PyAstLean.pyAppend xs (4 : Int)
# CHECK: xs := PyAstLean.pyAppend xs (5 : Int)
# CHECK: def list_len :=
# CHECK: pyLen xs
# CHECK: def list_membership :=
# CHECK: let present := decide ((2 : Int) ∈ xs)
# CHECK: let missing := decide ((9 : Int) ∈ xs)
# PYASTLEANCHECK END

def list_append_once():
    xs = [1, 2]
    xs.append(3)
    return xs

def list_append_twice():
    xs = [1, 2, 3]
    xs.append(4)
    xs.append(5)
    return xs

def list_len():
    xs = [10, 20, 30, 40]
    return len(xs)

def list_membership():
    xs = [1, 2, 3]
    present = 2 in xs
    missing = 9 in xs
    return present, missing
