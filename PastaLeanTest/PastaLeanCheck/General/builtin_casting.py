# PastaLeanCHECK START
# TARGET: command
# CHECK: def builtin_casting :=
# CHECK: let a := PastaLean.pyInt "42"
# CHECK: let b := PastaLean.pyStr [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: let c := PastaLean.pyList "abc"
# CHECK: let d := PastaLean.pyStr Bool.true
# CHECK: let e := PastaLean.pyList ((1 : Int), (2 : Int))
# PastaLeanCHECK END

def builtin_casting():
    a = int("42")
    b = str([1, 2, 3])
    c = list("abc")
    d = str(True)
    e = list((1, 2))
    return a, b, c, d, e
