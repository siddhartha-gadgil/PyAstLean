# PYASTLEANCHECK START
# TARGET: command
# CHECK: def nested_loops := fun n ↦
# CHECK: Id.run
# CHECK: let mut total := (0 : Int)
# CHECK: for i in PyAstLean.pyRange n do
# CHECK: for j in PyAstLean.pyRange i do
# CHECK: total := total +ₚ j
# CHECK: return total
# CHECK: def super_nested_loops := fun n ↦
# CHECK: Id.run
# CHECK: let mut res := (0 : Int)
# CHECK: for i in PyAstLean.pyRange n do
# CHECK: for j in PyAstLean.pyRange n do
# CHECK: for k in PyAstLean.pyRange n do
# CHECK: for l in PyAstLean.pyRange n do
# CHECK: res := res +ₚ (((i +ₚ j) +ₚ k) +ₚ l)
# CHECK: return res
# CHECK: def while_in_for := fun n ↦
# CHECK: Id.run
# CHECK: let mut count := (0 : Int)
# CHECK: for i in PyAstLean.pyRange n do
# CHECK: let mut j := i
# CHECK: while j > (0 : Int) do
# CHECK: count := count +ₚ (1 : Int)
# CHECK: j := j -ₚ (1 : Int)
# CHECK: return count
# PYASTLEANCHECK END

def nested_loops(n):
    total = 0
    for i in range(n):
        for j in range(i):
            total += j
    return total

def super_nested_loops(n):
    res = 0
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    res += i + j + k + l
    return res

def while_in_for(n):
    count = 0
    for i in range(n):
        j = i
        while j > 0:
            count += 1
            j -= 1
    return count
