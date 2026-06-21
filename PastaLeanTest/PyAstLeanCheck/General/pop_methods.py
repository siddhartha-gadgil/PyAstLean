# PastaLeanCHECK START
# TARGET: command
# CHECK: def list_pop_last :=
# CHECK: Id.run
# CHECK: let mut xs := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
# CHECK: let mut last := PastaLean.pyPopValue xs
# CHECK: xs := PastaLean.pyPopRest xs
# CHECK: def list_pop_index :=
# CHECK: let mut first := PastaLean.pyPopValue ys (0 : Int)
# CHECK: ys := PastaLean.pyPopRest ys (0 : Int)
# CHECK: def set_pop :=
# CHECK: let mut seen := PastaLean.pySet [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: seen := PastaLean.pySetDiscard seen (2 : Int)
# CHECK: let mut x := PastaLean.pyPopValue seen
# CHECK: seen := PastaLean.pyPopRest seen
# CHECK: return x
# PastaLeanCHECK END

# `list.pop()` removes and returns the last element; `list.pop(i)` the element at index i.
# Both lower to a value read (`pyPopValue`) plus a container update (`pyPopRest`), since the
# runtime containers are immutable values. `pop` mutates its receiver, so the function body is
# threaded monadically (`Id.run do`) with the container bound `let mut`.

def list_pop_last():
    xs = [10, 20, 30, 40]
    last = xs.pop()
    return last

def list_pop_index():
    ys = [10, 20, 30, 40]
    first = ys.pop(0)
    return first

# Sets are modelled as deduplicated lists; `set.pop()` removes an arbitrary element.
def set_pop():
    seen = set([1, 2, 3])
    seen.discard(2)
    x = seen.pop()
    return x
