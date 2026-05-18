d = {"apple": 1, "banana": 2}

d.clear()
z = ["hi"]
z.insert(-10, "hello")
x = "hello"
print(z)

import ast

code="""
x = len([1, 2, 3])
print(x)
x.extend([4, 5])
"""
ast.parse(code)
print(ast.dump(ast.parse(code), indent=4))