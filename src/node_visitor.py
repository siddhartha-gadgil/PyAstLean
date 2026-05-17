import json
import sys
import ast

BINOP_MAP = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.Pow: "pow",
    ast.Div: "div",
    ast.BitOr: "bitor",
    ast.Mod : "mod",
}

BOOLOP_MAP = {
    ast.And: "and",
    ast.Or: "or",
}

UNARYOP_MAP = {
    ast.USub: "neg",
    ast.UAdd: "pos",
    ast.Not: "not",
}

COMPAREOP_MAP = {
    ast.Eq: "eq",
    ast.NotEq: "ne",
    ast.Lt: "lt",
    ast.LtE: "le",
    ast.Gt: "gt",
    ast.GtE: "ge",
    ast.In: "in",
    ast.NotIn: "notin",
}

AUGASSIGN_MAP = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.MatMult: "matmul",
    ast.Pow: "pow",
    ast.Mod: "mod",
    ast.LShift: "lshift",
    ast.RShift: "rshift",
    ast.BitAnd: "and",
    ast.BitOr: "or",
    ast.BitXor: "xor",
    ast.Div: "div",
    ast.FloorDiv: "floordiv",
}


"""
Use auto-serialize for nodes whose JSON form is basically:
- node_type = AST class name
- every field can just be recursively visited
- no normalization, remapping, filtering, or validation is needed
"""
AUTO_SERIALIZED_NODE_NAMES = {
    "ExceptHandler",
    "match_case",
}

FUNCTION_DEF_SCHEMA = {
    "node_type": "FunctionDef",
    "name": "str",
    "args": {
        "node_type": "arguments",
        "posonlyargs": ["arg"],
        "args": ["arg"],
        "vararg": "arg | None",
        "kwonlyargs": ["arg"],
        "kw_defaults": ["Json | None"],
        "kwarg": "arg | None",
        "defaults": ["Json"]
    },
    "body": ["Json"],
    "decorator_list": ["Json"],
    "returns": "Json | None",
    "type_comment": "str | None",
    "type_params": ["Json"]
}

class ASTToJsonLeanVisitorBase:
    def _map_ast_type(self, node_or_type, mapping, label):
        """Map an AST node type through a shared lookup table."""
        node_type = type(node_or_type) if isinstance(node_or_type, ast.AST) else node_or_type
        mapped = mapping.get(node_type)
        if mapped is None:
            raise NotImplementedError(f"{label} {node_type.__name__} not supported.")
        return mapped

    def _serialize_node_fields(self, node):
        """Serialize an AST node by visiting all of its fields recursively."""
        result: dict[str, object] = {"node_type": type(node).__name__}
        for field_name, value in ast.iter_fields(node):
            result[field_name] = self._serialize_field_value(value)
        return result

    def _serialize_field_value(self, value):
        """Recursively serialize one AST field value."""
        if isinstance(value, ast.AST):
            return self.visit(value)
        if isinstance(value, list):
            return [self._serialize_field_value(item) for item in value]
        return value

    def _visit_match_node(self, node):
        """Generic serializer for Python structural pattern-matching AST nodes."""
        return self._serialize_node_fields(node)

    def _visit_auto_serialized_node(self, node):
        """Generic serializer for explicitly whitelisted AST nodes."""
        return self._serialize_node_fields(node)

    def visit_statements(self, statements):
        """Translate a statement list, skipping declaration-only annotations."""
        result = []
        for stmt in statements:
            if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
                continue
            result.append(self.visit(stmt))
        return result

    def visit(self, node):
        """
        The dynamic dispatcher. Routes an AST node to its specific visit_X method.
        """
        # Base case: raw primitives
        if not isinstance(node, ast.AST):
            return node
            
        # Determine the name of the method we need
        method_name = f"visit_{type(node).__name__}"
        
        # Fetch the specific method, falling back to generic_visit if it doesn't exist
        visitor = getattr(self, method_name, None)
        if visitor is None and (
            type(node).__name__.startswith("Match") or type(node).__name__ == "match_case"
        ):
            visitor = self._visit_match_node
        if visitor is None and type(node).__name__ in AUTO_SERIALIZED_NODE_NAMES:
            visitor = self._visit_auto_serialized_node
        if visitor is None:
            visitor = self.generic_visit
        # print(f"Visiting node type: {type(node).__name__} with visitor method: {visitor.__name__}", file=sys.stderr)  # Debugging output
        
        return visitor(node)

    def generic_visit(self, node):
        """Strict fallback to prevent unsupported syntax from leaking into the IR."""
        raise NotImplementedError(f"Translation for {type(node).__name__} is not supported in the current subset.")
    

    def visit_BinOp(self, node):
        """Translates ast.BinOp (e.g., a + b) to a JSON IR node."""
        left_json = self.visit(node.left)
        right_json = self.visit(node.right)
        op = self._map_ast_type(node.op, BINOP_MAP, "Operator")
            
        return {
            "node_type": "BinOp",
            "op": op,
            "left": left_json,
            "right": right_json
        }
    
    def visit_BoolOp(self, node):
        """Translates ast.BoolOp (e.g., a and b) to a JSON IR node."""
        op = self._map_ast_type(node.op, BOOLOP_MAP, "Boolean operator")
        
        return {
            "node_type": "BoolOp",
            "op": op,
            "values": [self.visit(value) for value in node.values]
        }

    def visit_UnaryOp(self, node):
        """Translates ast.UnaryOp (e.g., -a) to a JSON IR node."""
        op = self._map_ast_type(node.op, UNARYOP_MAP, "Unary operator")
        
        return {
            "node_type": "UnaryOp",
            "op": op,
            "operand": self.visit(node.operand)
        }

    def visit_Compare(self, node):
        """Translates ast.Compare (e.g., a <= b) to a JSON IR node."""
        if len(node.ops) != 1 or len(node.comparators) != 1:
            raise NotImplementedError("Chained comparisons are not supported.")
        op = self._map_ast_type(node.ops[0], COMPAREOP_MAP, "Comparison operator")

        return {
            "node_type": "Compare",
            "op": op,
            "left": self.visit(node.left),
            "right": self.visit(node.comparators[0])
        }
    
    def visit_Constant(self, node):
        """Translates ast.Constant (e.g., 42, "hello") to a JSON IR node."""
        return {
            "node_type": "Constant",
            "value": node.value
        }
        
    def visit_Expr(self, node):
        """Translates ast.Expr (e.g., a standalone expression) to a JSON IR node."""
        return self.visit(node.value)

    def visit_Pass(self, node):
        """Translates ast.Pass to a JSON IR no-op node."""
        return {
            "node_type": "Pass"
        }

    def visit_Break(self, node):
        """Translates ast.Break to a JSON IR node."""
        return {
            "node_type": "Break"
        }

    def visit_Continue(self, node):
        """Translates ast.Continue to a JSON IR node."""
        return {
            "node_type": "Continue"
        }
    
    def visit_Name(self, node):
        """Translates ast.Name (e.g., variable names) to a JSON IR node."""
        return {
            "node_type": "Name",
            "id": node.id
        }
    def visit_Call(self, node):
        """Translates ast.Call (e.g., function calls) to a JSON IR node."""
        func_json = self.visit(node.func)
        args_json = [self.visit(arg) for arg in node.args]
        keywords_json = {kw.arg: self.visit(kw.value) for kw in node.keywords}
        if func_json.get("node_type") == "Name" and func_json.get("id") == "range":
            return {
                "node_type": "Range",
                "func": func_json,
                "args": args_json,
                "keywords": keywords_json
            }
        return {
            "node_type": "Call",
            "func": func_json,
            "args": args_json,
            "keywords": keywords_json
        }
    
    def visit_Attribute(self, node):
        """Translates ast.Attribute (e.g., object.attribute) to a JSON IR node."""
        value_json = self.visit(node.value)
        return {
            "node_type": "Attribute",
            "value": value_json,
            "attr": node.attr
        }

    def visit_Subscript(self, node):
        """Translates ast.Subscript (e.g., list[int]) to a JSON IR node."""
        return {
            "node_type": "Subscript",
            "value": self.visit(node.value),
            "slice": self.visit(node.slice)
        }

    def visit_List(self, node):
        """Translates ast.List to a JSON IR node."""
        return {
            "node_type": "List",
            "elts": [self.visit(elt) for elt in node.elts]
        }

    def visit_Dict(self, node):
        """Translates ast.Dict to a JSON IR node."""
        entries = []
        for key, value in zip(node.keys, node.values):
            if key is None:
                raise NotImplementedError("Dictionary unpacking is not supported.")
            entries.append({
                "key": self.visit(key),
                "value": self.visit(value),
            })
        return {
            "node_type": "Dict",
            "entries": entries
        }

    def visit_Tuple(self, node):
        """Translates ast.Tuple (e.g., tuple slices) to a JSON IR node."""
        return {
            "node_type": "Tuple",
            "elts": [self.visit(elt) for elt in node.elts]
        }

    def visit_JoinedStr(self, node):
        """Translates f-strings to a JSON IR node."""
        return {
            "node_type": "JoinedStr",
            "values": [self.visit(value) for value in node.values]
        }

    def visit_FormattedValue(self, node):
        """Translates one interpolated f-string segment."""
        if node.conversion != -1:
            raise NotImplementedError("FormattedValue conversions are not supported.")
        if node.format_spec is not None:
            raise NotImplementedError("FormattedValue format specs are not supported.")
        return {
            "node_type": "FormattedValue",
            "value": self.visit(node.value)
        }

    def visit_Module(self, node):
        """Translates ast.Module to a JSON IR node."""
        return {
            "node_type": "Module",
            "body": self.visit_statements(node.body)
        }

    def visit_FunctionDef(self, node):
        """Translates ast.FunctionDef to a JSON IR node."""
        body_json = self.visit_statements(node.body)
        return {
            "node_type": "FunctionDef",
            "name": node.name,
            "args": self.visit(node.args),
            "body": body_json,
            "decorator_list": [self.visit(decorator) for decorator in node.decorator_list],
            "returns": self.visit(node.returns) if node.returns is not None else None,
            "type_comment": node.type_comment,
            "type_params": [self.visit(type_param) for type_param in getattr(node, "type_params", [])]
        }
    def visit_Lambda(self, node):
        """Translates ast.Lambda to a JSON IR node."""
        return {
            "node_type": "Lambda",
            "args": self.visit(node.args),
            "body": self.visit(node.body)
        }
    
    def visit_arguments(self, node):
        """Translates ast.arguments to a JSON IR node."""
        return {
            "node_type": "arguments",
            "posonlyargs": [self.visit(arg) for arg in node.posonlyargs],
            "args": [self.visit(arg) for arg in node.args],
            "vararg": self.visit(node.vararg) if node.vararg is not None else None,
            "kwonlyargs": [self.visit(arg) for arg in node.kwonlyargs],
            "kw_defaults": [
                self.visit(default) if default is not None else None
                for default in node.kw_defaults
            ],
            "kwarg": self.visit(node.kwarg) if node.kwarg is not None else None,
            "defaults": [self.visit(default) for default in node.defaults]
        }

    def visit_arg(self, node):
        """Translates ast.arg to a JSON IR node."""
        return {
            "node_type": "arg",
            "arg": node.arg,
            "annotation": self.visit(node.annotation) if node.annotation is not None else None,
            "type_comment": node.type_comment
        }

    def visit_Assign(self, node):
        """Translates ast.Assign (e.g., x = y) to a JSON IR node."""
        if len(node.targets) != 1:
            raise NotImplementedError("Multiple assignment targets are not supported.")
        return {
            "node_type": "Assign",
            "target": self.visit(node.targets[0]),
            "value": self.visit(node.value)
        }
    
    def visit_AnnAssign(self, node):
        """Translates ast.AnnAssign (e.g., x: int = 42) to a JSON IR node.

        We normalize the common initialized form `x: T = v` to the same IR node as
        `x = v`, because the current Lean backend does not yet use Python-side type
        annotations during code generation. We keep declaration-only annotated
        assignments (`x: T`) distinct so the backend can decide how to handle them.
        """
        if node.simple != 1:
            raise NotImplementedError("Only simple annotated assignments are supported.")
        if node.value is not None:
            return {
                "node_type": "Assign",
                "target": self.visit(node.target),
                "value": self.visit(node.value)
            }
        return {
            "node_type": "AnnAssign",
            "target": self.visit(node.target),
            "annotation": self.visit(node.annotation),
            "value": None
        }

    def visit_AugAssign(self, node):
        """Translates ast.AugAssign (e.g., x += y) to a JSON IR node."""
        op = self._map_ast_type(node.op, AUGASSIGN_MAP, "Augmented operator")
        return {
            "node_type": "AugAssign",
            "target": self.visit(node.target),
            "op": op,
            "value": self.visit(node.value)
        }

    def visit_For(self, node):
        """Translates ast.For to a JSON IR node."""
        return {
            "node_type": "For",
            "target": self.visit(node.target),
            "iter": self.visit(node.iter),
            "body": self.visit_statements(node.body),
            "orelse": self.visit_statements(node.orelse)
        }

    def visit_If(self, node):
        """Translates ast.If to a JSON IR node."""
        return {
            "node_type": "If",
            "test": self.visit(node.test),
            "body": self.visit_statements(node.body),
            "orelse": self.visit_statements(node.orelse)
        }

    def visit_IfExp(self, node):
        """Translates ast.IfExp (ternary expressions) to a JSON IR node."""
        return {
            "node_type": "IfExp",
            "test": self.visit(node.test),
            "body": self.visit(node.body),
            "orelse": self.visit(node.orelse)
        }

    def visit_With(self, node):
        """Translates ast.With to a JSON IR node."""
        return {
            "node_type": "With",
            "items": [self.visit(item) for item in node.items],
            "body": self.visit_statements(node.body)
        }
        
    def visit_withitem(self, node):
        """Translates ast.withitem (the context manager part of with statements) to a JSON IR node."""
        return {
            "node_type": "withitem",
            "context_expr": self.visit(node.context_expr),
            "optional_vars": self.visit(node.optional_vars) if node.optional_vars is not None else None
        }

    def visit_While(self, node):
        """Translates ast.While to a JSON IR node."""
        return {
            "node_type": "While",
            "test": self.visit(node.test),
            "body": self.visit_statements(node.body),
            "orelse": self.visit_statements(node.orelse)
        }

    def visit_Return(self, node):
        """Translates ast.Return to a JSON IR node."""
        return {
            "node_type": "Return",
            "value": None if node.value is None else self.visit(node.value)
        }

    def visit_Try(self, node):
        """Translates ast.Try (Exception handling) to a JSON IR node."""
        return {
            "node_type": "Try",
            "body": self.visit_statements(node.body),
            "handlers": [self.visit(handler) for handler in node.handlers],
            "orelse": self.visit_statements(node.orelse),
            "finalbody": self.visit_statements(node.finalbody)
        }

    def visit_Raise(self, node):
        """Translates ast.Raise to a JSON IR node."""
        return {
            "node_type": "Raise",
            "exc": None if node.exc is None else self.visit(node.exc),
            "cause": None if node.cause is None else self.visit(node.cause),
        }
    
    def visit_ListComp(self, node):
        """Translates ast.ListComp (list comprehensions) to a JSON IR node."""
        return {
            "node_type": "ListComp",
            "elt": self.visit(node.elt),
            "generators": [self.visit(gen) for gen in node.generators]
        }

    def visit_GeneratorExp(self, node):
        """Translates ast.GeneratorExp using the same IR shape as comprehensions."""
        return {
            "node_type": "GeneratorExp",
            "elt": self.visit(node.elt),
            "generators": [self.visit(gen) for gen in node.generators]
        }
    
    def visit_comprehension(self, node):
        """Translates ast.comprehension (the generator part of comprehensions) to a JSON IR node."""
        return {
            "node_type": "comprehension",
            "target": self.visit(node.target),
            "iter": self.visit(node.iter),
            "ifs": [self.visit(if_cond) for if_cond in node.ifs],
            "is_async": node.is_async
        }

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python node_visitor.py <python_file.py>")
        sys.exit(1)

    input_file = sys.argv[1]
    with open(input_file, "r") as f:
        source_code = f.read()

    # Parse the source code into an AST
    tree = ast.parse(source_code)
    print(ast.dump(tree, indent = 4))  # Debugging output to verify AST structure
    visitor = ASTToJsonLeanVisitorBase()
    json_ir = visitor.visit(tree)

    print(json.dumps(json_ir, indent=2))
