# PastaLeanCHECK START
# TARGET: command
# CHECK: def check_nesting := fun n ↦
# CHECK: fun m ↦
# CHECK: if n > (0 : Int) then
# CHECK: if m >= (0 : Int) then
# CHECK: "Both positive"
# CHECK: else
# CHECK: "n positive, m non-positive"
# CHECK: else
# CHECK: if m > (0 : Int) then
# CHECK: "n non-positive, m positive"
# CHECK: else
# CHECK: "Both non-positive"
# CHECK: def super_nested_if := fun (a : Bool) ↦
# CHECK: fun (b : Bool) ↦
# CHECK: fun (c : Bool) ↦
# CHECK: fun (d : Bool) ↦
# CHECK: if a then
# CHECK: if b then
# CHECK: if c then
# CHECK: if d then
# CHECK: (1 : Int)
# CHECK: else
# CHECK: (2 : Int)
# CHECK: else
# CHECK: (3 : Int)
# CHECK: else
# CHECK: (4 : Int)
# CHECK: else
# CHECK: (5 : Int)
# CHECK: def complex_branching := fun x ↦
# CHECK: if x == (1 : Int) then
# CHECK: "one"
# CHECK: else
# CHECK: if x == (2 : Int) then
# CHECK: "two"
# CHECK: else
# CHECK: if x == (3 : Int) then
# CHECK: "three"
# CHECK: else
# CHECK: "other"
# PastaLeanCHECK END

def check_nesting(n, m):
    if n > 0:
        if m >= 0:
            return "Both positive"
        else:
            return "n positive, m non-positive"
    else:
        if m > 0:
            return "n non-positive, m positive"
        else:
            return "Both non-positive"

def super_nested_if(a: bool, b: bool, c: bool, d: bool):
    if a:
        if b:
            if c:
                if d:
                    return 1
                else:
                    return 2
            else:
                return 3
        else:
            return 4
    else:
        return 5

def complex_branching(x):
    if x == 1:
        return "one"
    elif x == 2:
        return "two"
    elif x == 3:
        return "three"
    else:
        return "other"
