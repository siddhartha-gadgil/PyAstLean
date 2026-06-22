# PastaLeanCHECK START
# TARGET: command
# CHECK: def GLOBAL_VAR := (42 : Int)
# CHECK: def get_global :=
# CHECK: GLOBAL_VAR
# CHECK: def pass_func :=
# CHECK: Id.run do
# CHECK: if Bool.true then 
# CHECK: let _ := ()
# CHECK: else
# CHECK: let _ := ()
# CHECK: let mut x := (1 : Int)
# CHECK: x := x +ₚ (1 : Int)
# CHECK: let _ := ()
# CHECK: def answer :=
# CHECK: (42 : Int)
# CHECK: def fruits :=
# CHECK: ["apple", "banana", "cherry"]
# CHECK: def scores :=
# CHECK: Std.HashMap.ofList
# CHECK: def greet := fun (name : Int) ↦
# CHECK: ToString.toString name
# CHECK: def calculate_sum :=
# CHECK: for i in PastaLean.pyRange
# CHECK: total := total +ₚ i
# CHECK: def not_sure :=
# CHECK: if answer == (42 : Int) then
# CHECK: else
# CHECK: if answer < (42 : Int) then
# CHECK: def main := Id.run do
# CHECK: for _ in PastaLean.pyRange (10 : Int)
# CHECK: let _ := pyPrint (greet (1 : Int))
# CHECK: let _ := calculate_sum
# CHECK: let _ := get_global
# PastaLeanCHECK END

GLOBAL_VAR = 42

def get_global():
    return GLOBAL_VAR

def pass_func():
    if True:
        pass
    x = 1
    x += 1
    pass

answer = 42

fruits = ["apple", "banana", "cherry"]
scores = {"math": 95, "science": 90}

def greet(name: int):
  return f"Hello, {name}!"

def calculate_sum():
    total = 0
    for i in range(10):
        total += i
    return total

def not_sure():
    if answer == 42:
        return "The answer to the Ultimate Question of Life, The Universe, and Everything."
    elif answer < 42:
        return "The sky is the limit."
    else:
        return "I don't know the answer."

if __name__ == "__main__":
    for _ in range(10):
        print(greet(1))
        calculate_sum()

    get_global()
