# PYASTLEANCHECK START
# TARGET: command
# CHECK: def GLOBAL_VAR := (42 : Int)
# CHECK: def get_global := fun ↦
# CHECK: GLOBAL_VAR
# CHECK: def pass_func :=
# CHECK: Id.run do
# CHECK: if Bool.true then 
# CHECK: let _ := ()
# CHECK: else
# CHECK: pure. ()
# CHECK: let mut x := (1 : Int)
# CHECK: x := x +ₚ (1 : Int)
# CHECK: let _ := ()
# CHECK: def main := Id.run do
# CHECK: let _ := get_global
# PYASTLEANCHECK END

GLOBAL_VAR = 42

def get_global():
    return GLOBAL_VAR

def pass_func():
    if True:
        pass
    x = 1
    x += 1
    pass

if __name__ == "__main__":
    get_global()
