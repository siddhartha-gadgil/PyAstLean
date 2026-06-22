# PastaLeanCHECK START
# TARGET: command
# CHECK: def arr : List Int :=
# CHECK:   [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: def result : Int :=
# CHECK:   PastaLean.pyListGetItem arr (0 : Int)
# PastaLeanCHECK END

arr = [1, 2, 3]
result = arr[0]

# PastaLeanCHECK START
# TARGET: command
# CHECK: def foo : IO String :=
# CHECK:   Id.run
# CHECK:     (do
# CHECK:       let mut x : String := "hi"
# CHECK:       let mut y : String := PastaLean.pyListGetItem x (0 : Int)
# CHECK:       y := y *ₚ (10 : Int)
# CHECK:       let mut z : String := PastaLean.pyStringSlice y (some (2 : Int)) (some (-3))
# CHECK:       return z)
# PastaLeanCHECK END

def foo():
    x = "hi"
    y = x[0]
    y *= 10
    z = y[2:-3]
    return z

# PastaLeanCHECK START
# TARGET: command
# CHECK: def bar : IO String :=
# CHECK:   let x : String := "hi"
# CHECK:   let y : String := PastaLean.pyStringSlice x (some (100 : Int)) (some (-2000))
# CHECK:   y
# PastaLeanCHECK END

def bar():
    x = "hi"
    y = x[100:-2000]
    return y
