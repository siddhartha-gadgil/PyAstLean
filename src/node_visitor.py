import ast

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
        visitor = getattr(self, method_name, self.generic_visit)
        # print(f"Visiting node type: {type(node).__name__} with visitor method: {visitor.__name__}", file=sys.stderr)  # Debugging output
        
        return visitor(node)

    def generic_visit(self, node):
        """Strict fallback to prevent unsupported syntax from leaking into the IR."""
        raise NotImplementedError(f"Translation for {type(node).__name__} is not supported in the current subset.")
    

    def visit_BinOp(self, node):
        """Translates ast.BinOp (e.g., a + b) to a JSON IR node."""
        left_json = self.visit(node.left)
        right_json = self.visit(node.right)
        
        # Map Python operators to Lean-compatible strings
        if isinstance(node.op, ast.Add):
            op = "add"
        elif isinstance(node.op, ast.Sub):
            op = "sub"
        elif isinstance(node.op, ast.Mult):
            op = "mul"
        elif isinstance(node.op, ast.Pow):
            op = "pow"
        else:
            raise NotImplementedError(f"Operator {type(node.op).__name__} not supported.")
            
        return {
            "node_type": "BinOp",
            "op": op,
            "left": left_json,
            "right": right_json
        }
    
    def visit_BoolOp(self, node):
        """Translates ast.BoolOp (e.g., a and b) to a JSON IR node."""
        op_type = type(node.op)
        if op_type == ast.And:
            op = "and"
        elif op_type == ast.Or:
            op = "or"
        else:
            raise NotImplementedError(f"Boolean operator {op_type.__name__} not supported.")
        
        return {
            "node_type": "BoolOp",
            "op": op,
            "values": [self.visit(value) for value in node.values]
        }

    def visit_UnaryOp(self, node):
        """Translates ast.UnaryOp (e.g., -a) to a JSON IR node."""
        if isinstance(node.op, ast.USub):
            op = "neg"
        elif isinstance(node.op, ast.UAdd):
            op = "pos"
        elif isinstance(node.op, ast.Not):
            op = "not"
        else:
            raise NotImplementedError(f"Unary operator {type(node.op).__name__} not supported.")
        
        return {
            "node_type": "UnaryOp",
            "op": op,
            "operand": self.visit(node.operand)
        }

    def visit_Compare(self, node):
        """Translates ast.Compare (e.g., a <= b) to a JSON IR node."""
        if len(node.ops) != 1 or len(node.comparators) != 1:
            raise NotImplementedError("Chained comparisons are not supported.")

        if isinstance(node.ops[0], ast.Eq):
            op = "eq"
        elif isinstance(node.ops[0], ast.NotEq):
            op = "ne"
        elif isinstance(node.ops[0], ast.Lt):
            op = "lt"
        elif isinstance(node.ops[0], ast.LtE):
            op = "le"
        elif isinstance(node.ops[0], ast.Gt):
            op = "gt"
        elif isinstance(node.ops[0], ast.GtE):
            op = "ge"
        else:
            raise NotImplementedError(f"Comparison operator {type(node.ops[0]).__name__} not supported.")

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
        if isinstance(node.op, ast.Add):
            op = "add"
        elif isinstance(node.op, ast.Sub):
            op = "sub"
        elif isinstance(node.op, ast.Mult):
            op = "mul"
        else:
            raise NotImplementedError(f"Augmented operator {type(node.op).__name__} not supported.")
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
