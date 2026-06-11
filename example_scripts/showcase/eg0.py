def fibonacci (n: int) :
    if n <= 0 :
        return 0
    elif n == 1 :
        return 1
    else :
        return fibonacci (n - 1) + fibonacci (n - 2)

def funnyfoo (x: int) :
    return (x * x + x) ** x