# PYASTLEANCHECK START
# TARGET: command
# CHECK: def basic_types := Id.run do
# CHECK: let [[MUT1:(mut )?]]a := (1 : Int)
# CHECK: let [[MUT2:(mut )?]]b := ((25 : Int) : Rat) / 10
# CHECK: let [[MUT3:(mut )?]]c := "hello"
# CHECK: let [[MUT4:(mut )?]]d := Bool.true
# CHECK: let [[MUT5:(mut )?]]e := [(1 : Int), (2 : Int)]
# CHECK: let [[MUT6:(mut )?]]f := ((1 : Int), "a")
# CHECK: def annotated_vars := fun ↦
# CHECK: let [[MUT7:(mut )?]]x := (10 : Int)
# CHECK: let [[MUT8:(mut )?]]y := (20 : Int)
# CHECK: x +ₚ y
# PYASTLEANCHECK END

def basic_types():
    a = 1
    b = 2.5
    c = "hello"
    d = True
    e = [1, 2]
    f = (1, "a")

def annotated_vars():
    x: int = 10
    y: int = 20
    return x + y
