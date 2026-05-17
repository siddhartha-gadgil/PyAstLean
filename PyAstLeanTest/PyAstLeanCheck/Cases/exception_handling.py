# PYASTLEANCHECK START
# TARGET: command
# CHECK: def fail := fun x ↦
# CHECK: if x < (0 : Int) then
# CHECK: throw (PyAstLean.PyException.Raise "ValueError"
# CHECK: ToString.toString "negative")
# CHECK: return
# CHECK: String.append
# CHECK: PyAstLean.PyExcept _)
# CHECK: def call_fail := fun x ↦
# CHECK: let mut y := (← fail x)
# CHECK: return y
# CHECK: PyAstLean.PyExcept _)
# CHECK: def safe := fun n ↦
# CHECK: try
# CHECK: return ((← fail n))
# CHECK: catch caught =>
# CHECK: if (caught).OfKind == "ValueError" then
# CHECK: let err := caught
# CHECK: return
# CHECK: String.append
# CHECK: PyAstLean.PyExcept _)
# CHECK: def simple_catch :=
# CHECK: let mut x := (1 : Int)
# CHECK: let helper := fun (x : Int) ↦ x +ₚ (1 : Int)
# CHECK: x := helper x
# CHECK: throw (PyAstLean.PyException.Raise "Exception"
# CHECK: Caught exception:
# CHECK: def fixed_catch :=
# CHECK: if (caught).OfKind == "ZeroDivisionError" then
# CHECK: return
# CHECK: String.append
# CHECK: Caught ZeroDivisionError:
# CHECK: Caught other exception:
# CHECK: def nested_try :=
# CHECK: Caught inner ZeroDivisionError:
# CHECK: Caught outer exception:
# CHECK: def try_with_else_finally := fun num ↦
# CHECK: throw (PyAstLean.PyException.Raise "ValueError"
# CHECK: throw (PyAstLean.PyException.Raise "ZeroDivisionError"
# CHECK: Caught ValueError:
# CHECK: Caught ZeroDivisionError:
# CHECK: finally
# CHECK: pyPrint "Finally block executed"
# CHECK: def raise_error := fun num ↦
# CHECK: throw (PyAstLean.PyException.Raise "ValueError"
# CHECK: throw (PyAstLean.PyException.Raise "ZeroDivisionError"
# CHECK: return
# CHECK: String.append (String.append "" "Number is ")
# CHECK: def catch_loop := fun num ↦
# CHECK: for i in PyAstLean.pyRange num do
# CHECK: if (caught).OfKind == "ValueError" then
# CHECK: Caught ValueError at i=
# CHECK: if (caught).OfKind == "ZeroDivisionError" then
# CHECK: Caught ZeroDivisionError at i=
# PYASTLEANCHECK END

def fail(x):
    if x < 0:
        raise ValueError("negative")
    return f"value {x}"

def call_fail(x):
    y = fail(x)
    return y

def safe(n):
    try:
        return fail(n)
    except ValueError as err:
        return f"bad value: {err}"

def simple_catch():
    x = 1
    def helper(x):
        return x+1
    x = helper(x)
    try:
        raise Exception("boom")
    except Exception as e:
        return f"Caught exception: {e}"

def fixed_catch(): 
    try:
        _ = 1 / 0
        return "1 just got divided by 0"
    except ZeroDivisionError as e:
        return f"Caught ZeroDivisionError: {e}"
    except Exception as e:
        return f"Caught other exception: {e}"
    return "No exception"

def nested_try():
    try:
        try:
            _ = 1 / 0
            return "1 just got divided by 0"
        except ZeroDivisionError as e:
            return f"Caught inner ZeroDivisionError: {e}"
    except Exception as e:
        return f"Caught outer exception: {e}"
    return "No exception"

def try_with_else_finally(num):
    try:
        if num < 0:
            raise ValueError("Negative number")
        elif num == 0:
            raise ZeroDivisionError("Zero is not allowed")
        else:
            return f"Number is {num}"
    except ValueError as e:
        return f"Caught ValueError: {e}"
    except ZeroDivisionError as e:
        return f"Caught ZeroDivisionError: {e}"
    else:
        return "No exceptions, else block executed"
    finally:
        print("Finally block executed")
 
def raise_error(num):
    if num < 0:
        raise ValueError("Negative number")
    elif num == 0:
        raise ZeroDivisionError("Zero is not allowed")
    else:
        return f"Number is {num}"


def catch_loop(num):
    for i in range(num):
        try:
            if i == 3:
                raise ValueError("i cannot be 3")
            elif i == 5:
                raise ZeroDivisionError("i cannot be 5")
        except ValueError as e:
            print(f"Caught ValueError at i={i}: {e}")
        except ZeroDivisionError as e:
            print(f"Caught ZeroDivisionError at i={i}: {e}")
