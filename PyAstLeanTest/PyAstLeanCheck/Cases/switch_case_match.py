# PYASTLEANCHECK START
# TARGET: command
# CHECK: def basic_switch := fun (num : Int) ↦
# CHECK: match num with
# CHECK: | (1 : Int) => "one"
# CHECK: | (2 : Int) => "two"
# CHECK: | _ => "other"
# CHECK: def switch_with_guard := fun (num : Int) ↦
# CHECK: let x := num
# CHECK: if x < (0 : Int) then "negative"
# CHECK: def switch_with_pattern := fun (num : Int) ↦
# CHECK: match num with
# CHECK: | (0 : Int) => "zero"
# CHECK: | (1 : Int) => "small number"
# CHECK: | (2 : Int) => "small number"
# CHECK: | (3 : Int) => "small number"
# CHECK: | _ => "other number"
# CHECK: def switch_with_tuple := fun point ↦
# CHECK: match point with
# CHECK: | ((0 : Int), (0 : Int)) => "origin"
# CHECK: | (x, (0 : Int)) => String.append
# CHECK: | ((0 : Int), y) => String.append
# CHECK: | (x, y) =>
# CHECK: def switch_with_default := fun (num : Int) ↦
# CHECK: match num with
# CHECK: | (1 : Int) => if num == (1 : Int) then "one" else "not one"
# CHECK: | (2 : Int) => "two"
# CHECK: | _ => "other"
# PYASTLEANCHECK END

def basic_switch(num):
    match num:
        case 1:
            return "one"
        case 2:
            return "two"
        case _:
            return "other"

def switch_with_guard(num):
    match num:
        case x if x < 0:
            return "negative"
        case 0:
            return "zero"
        case x if x > 0:
            return "positive"
        case _:
            return "other"
        
def switch_with_pattern(num):
    match num:
        case 0:
            return "zero"
        case 1 | 2 | 3:
            return "small number"
        case _:
            return "other number"
        
def switch_with_tuple(point):
    match point:
        case (0, 0):
            return "origin"
        case (x, 0):
            return f"x-axis at {x}"
        case (0, y):
            return f"y-axis at {y}"
        case (x, y):
            return f"point at ({x}, {y})"
        
def switch_with_default(num):
    match num:
        case 1:
            if num == 1:
                return "one"
            else:
                return "not one"
        case 2:
            return "two"
        case _:
            return "other"
