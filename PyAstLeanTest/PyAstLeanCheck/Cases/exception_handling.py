def simple_catch():
    try:
        _ = 1 / 0
    except Exception as e:
        return f"Caught exception: {e}"
    return "No exception"

def fixed_catch():
    try:
        _ = 1 / 0
    except ZeroDivisionError as e:
        return f"Caught ZeroDivisionError: {e}"
    except Exception as e:
        return f"Caught other exception: {e}"
    return "No exception"

def nested_try():
    try:
        try:
            _ = 1 / 0
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

