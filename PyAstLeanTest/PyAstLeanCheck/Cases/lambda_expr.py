
# PYASTLEANCHECK START
# TARGET: command
# CHECK: def lmbda_expr := fun x ↦ x +ₚ (1 : Int)
# CHECK: def lmbda_with_array :=
# CHECK: if decide (x ∈ a) then some (x *ₚ x) else none
# CHECK: def nested_lmbda := fun () ↦ fun x ↦ x *ₚ x
# CHECK: def lmbda_with_tuple_unpacking := fun {α β} [ToString α] [ToString β] (pair : α × β) ↦
# CHECK: ToString.toString (Prod.fst pair)
# CHECK: ToString.toString (Prod.snd pair)
# CHECK: def lmbda_with_generator_expression := fun () ↦
# CHECK: List.map (fun x => x *ₚ x)
# PYASTLEANCHECK END

def lmbda_expr():
    return lambda x: x + 1

def lmbda_with_condition():
    return lambda x: x + 1 if x % 2 == 0 else x - 1

def lmbda_with_array():
    a = [1, 2, 3, 4, 5]
    b = lambda x: x * x if x in a else None
    c =b
    return c

def lmbda_with_string():
    s = "hello"
    return lambda char: char in (s + " world")

def nested_lmbda():
    return lambda: (lambda x: x * x)

def lmbda_with_function_call():
    def add_one(x):
        return x + 1
    
    return lambda x: add_one(x)

def lmbda_ds():
    return lambda x: [x, x * 2, x * 3]

def lmbda_with_nested_conditions():
    return lambda x: x + 1 if (x % 2 == 0 and x % 3 == 0) or x % 5 == 0 else x - 1

def lmbda_with_tuple_unpacking():
    return lambda pair: f"{pair[0]}:{pair[1]}"

def lmbda_with_side_effects():
    result= []
    for x in range(5):
        result.append(x * x)
    return lambda y: result

def lmbda_with_generator_expression():
    return lambda: [x * x for x in (i for i in range(5))]
