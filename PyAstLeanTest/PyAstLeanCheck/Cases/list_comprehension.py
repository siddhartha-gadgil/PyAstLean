
# PYASTLEANCHECK START
# TARGET: command
# CHECK: def simple_lc :=
# CHECK: List.map (fun x => x) (PyAstLean.pyRange (10 : Int))
# CHECK: def lc_with_condition :=
# CHECK: List.filter (fun x => x %ₚ (2 : Int) == (0 : Int))
# CHECK: def nested_lc :=
# CHECK: List.map (fun _ => List.map (fun x => x)
# CHECK: def lc_with_tuple_unpacking :=
# CHECK: let another_pairs :=
# CHECK: let (num, char) := _pair
# CHECK: def lc_with_side_effects :=
# CHECK: Id.run
# CHECK: result := PyAstLean.pyAppend result (x *ₚ x)
# CHECK: def lc_with_dict :=
# CHECK: PyAstLean.pyItems d
# CHECK: def lc_multi_list :=
# CHECK: List.flatMap
# PYASTLEANCHECK END

def simple_lc():
    return [x for x in range(10)]

def lc_with_condition():
    return [x for x in range(10) if x % 2 == 0]

def lc_with_array():
    a = [1, 2, 3, 4, 5]
    return [x * x for x in a]

def lc_with_string():
    s = "hello"
    return [char for char in (s + " world")]

def nested_lc():
    a= [[x for x in range(5)] for _ in range(3)]
    return a

def lc_with_function_call():
    def add_one(x):
        return x + 1
    
    a = [add_one(x) for x in range(5)] 
    return a

def lc_with_multiple_conditions():
    return [x for x in range(20) if x % 2 == 0 and x % 3 == 0]

def lc_with_tuple_unpacking():
    pairs= [(1, 'a'), (2, 'b'), (3, 'c')]
    another_pairs= [(4, 'd'), (5, 'e')]
    another_pairs= [(num, char) for num, char in another_pairs if num % 2 == 0]
    _ = another_pairs 
    return [f"{num}:{char}" for num, char in pairs]

def lc_with_nested_conditions():
    return [x for x in range(20) if (x % 2 == 0 and x % 3 == 0) or x % 5 == 0]

def lc_with_side_effects():
    result= []
    for x in range(5):
        result.append(x * x)
    return [y for y in result]

def lc_with_generator_expression():
    return [x * x for x in (i for i in range(5))]

def lc_with_if_else():
    a = [x for x in range(10)]
    return [x if x % 2 == 0 else -x for x in range(10)]

def lc_with_string_literal_list():
    return [x for x in ["me", "you"]]

def lc_with_dict():
    d = {'a': 1, 'b': 2, 'c': 3}
    return [f"{k}:{v}" for k, v in d.items()]

def lc_multi_list():
    ll = [x * y for a in [[1, 2], [3,4]] for x in a for y in a]
    lt = [x * y for x in ll for y in ll]
    return ll, lt

def lc_multi_invoke():
    a = [x * y * z for x in range(5) for y in range(5) for z in range(5)]
    b = [(x, y, z) for x in range(5) for y in range(5) for z in range(5)]
    return a, b
