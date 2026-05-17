from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any as TypingAny

try:
    import libcst as cst
    HAS_LIBCST: bool = True
except ImportError:
    HAS_LIBCST = False

    class _DummyTransformer:
        pass

    class _DummyVisitor:
        pass

    class _DummyParserSyntaxError(Exception):
        pass

    class _DummyCST:
        CSTTransformer = _DummyTransformer
        CSTVisitor = _DummyVisitor
        ParserSyntaxError = _DummyParserSyntaxError

    cst = _DummyCST()

MAX_FLOW_PASSES: int = 5

def run_command(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, capture_output=True, text=True)


def node_to_str(node: TypingAny) -> str:
    """Normalize a small LibCST type node to a comparable string form."""
    if isinstance(node, cst.Name):
        return node.value
    if isinstance(node, cst.SimpleString):
        return node.value
    if isinstance(node, cst.Subscript):
        val: str = node_to_str(node.value)
        if not node.slice:
            return f"{val}[]"
        sl: str = node_to_str(
            node.slice[0].slice.value if hasattr(node.slice[0].slice, "value") else node.slice[0].slice
        )
        return f"{val}[{sl}]"
    if isinstance(node, cst.BinaryOperation) and isinstance(node.operator, cst.BitOr):
        return f"{node_to_str(node.left)} | {node_to_str(node.right)}"
    return "Any"


def split_top_level(text: str, delimiter: str) -> list[str]:
    """Split a type string on a delimiter while respecting bracket nesting."""
    parts: list[str] = []
    curr: str = ""
    bracket_level: int = 0
    for char in text:
        if char == "[":
            bracket_level += 1
        elif char == "]":
            bracket_level -= 1
        if char == delimiter and bracket_level == 0:
            parts.append(curr.strip())
            curr = ""
        else:
            curr += char
    if curr.strip():
        parts.append(curr.strip())
    return parts


def normalize_union(type_str: str) -> str:
    """Normalize a union like `A | B | A` into a stable deduplicated representation."""
    parts: list[str] = [p.strip() for p in split_top_level(type_str, "|") if p.strip()]
    if not parts:
        return "Any"
    unique_set: set[str] = set(parts)
    if len(unique_set) > 1 and "Any" in unique_set:
        unique_set.remove("Any")

    # Prefer concrete container element types over their Any variants.
    for prefix in ("list", "set", "generator"):
        any_variant: str = f"{prefix}[Any]"
        if any_variant in unique_set and any(
            t.startswith(f"{prefix}[") and t != any_variant for t in unique_set
        ):
            unique_set.remove(any_variant)
    if "dict[Any, Any]" in unique_set and any(
        t.startswith("dict[") and t != "dict[Any, Any]" for t in unique_set
    ):
        unique_set.remove("dict[Any, Any]")

    unique: list[str] = sorted(unique_set)
    return " | ".join(unique)


def extract_generic_inner(type_str: str, prefix: str) -> str | None:
    """Return the inner payload of `prefix[...]` if the string matches that shape."""
    pfx: str = f"{prefix}["
    if not (type_str.startswith(pfx) and type_str.endswith("]")):
        return None
    return type_str[len(pfx):-1]


def tuple_type_parts(type_str: str) -> list[str] | None:
    """Parse `tuple[T1, T2, ...]` into component type strings."""
    inner: str | None = extract_generic_inner(type_str, "tuple")
    if inner is None:
        return None
    return split_top_level(inner, ",")


def iter_cst_nodes(node: cst.CSTNode) -> TypingAny:
    """Yield one CST node and all descendants."""
    yield node
    for child in node.children:
        yield from iter_cst_nodes(child)


def iter_comprehension_exprs(expr: cst.BaseExpression | None) -> TypingAny:
    """Yield all comprehension expressions nested anywhere inside `expr`."""
    if expr is None:
        return
    for node in iter_cst_nodes(expr):
        if isinstance(node, (cst.ListComp, cst.SetComp, cst.GeneratorExp)):
            yield node


def extract_comp_target_names(comp_for: cst.CompFor) -> list[str]:
    """Collect target variable names from one comprehension for-chain."""
    names: list[str] = []
    if isinstance(comp_for.target, cst.Name):
        if comp_for.target.value != "_":
            names.append(comp_for.target.value)
    elif isinstance(comp_for.target, (cst.Tuple, cst.List)):
        for element in comp_for.target.elements:
            if isinstance(element.value, cst.Name) and element.value.value != "_":
                names.append(element.value.value)
    if comp_for.inner_for_in is not None:
        names.extend(extract_comp_target_names(comp_for.inner_for_in))
    return names


def stub_fingerprint(stub_data: dict[str, TypingAny]) -> tuple[tuple[str, str, tuple[tuple[str, str], ...]], ...]:
    """Create a stable comparable snapshot of function stub state across passes."""
    rows: list[tuple[str, str, tuple[tuple[str, str], ...]]] = []
    functions: dict[str, TypingAny] = stub_data.get("functions", {})
    for fn_name in sorted(functions.keys()):
        fn_data: dict[str, TypingAny] = functions[fn_name]
        ret_str: str = node_to_str(fn_data["returns"]) if fn_data.get("returns") else ""
        params: dict[str, TypingAny] = fn_data.get("params", {})
        param_rows: list[tuple[str, str]] = []
        for p_name in sorted(params.keys()):
            param_rows.append((p_name, node_to_str(params[p_name])))
        rows.append((fn_name, ret_str, tuple(param_rows)))
    return tuple(rows)


class Lean4Annotator(cst.CSTTransformer):
    """Rewrite the source CST using stub information plus local flow-based hints."""
    def __init__(
        self,
        stub_annotations: dict[str, TypingAny],
        flow_types: dict[tuple[str | None, str | None, str], str],
    ) -> None:
        self.stub_annotations: dict[str, TypingAny] = stub_annotations
        self.flow_types: dict[tuple[str | None, str | None, str], str] = flow_types
        self.current_class: str | None = None
        self.current_function: str | None = None
        self.function_stack: list[str] = []
        self.unpack_counter: int = 0

    def visit_ClassDef(self, node: cst.ClassDef) -> bool:
        self.current_class = node.name.value
        return True

    def leave_ClassDef(self, original_node: cst.ClassDef, updated_node: cst.ClassDef) -> cst.ClassDef:
        self.current_class = None
        return updated_node

    def visit_FunctionDef(self, node: cst.FunctionDef) -> bool:
        if self.current_function is not None:
            self.function_stack.append(self.current_function)
        self.current_function = node.name.value
        return True

    def leave_FunctionDef(self, original_node: cst.FunctionDef, updated_node: cst.FunctionDef) -> cst.FunctionDef:
        func_name: str = updated_node.name.value
        lookup_name: str = f"{self.current_class}.{func_name}" if self.current_class else func_name

        # First prefer stub-derived signatures so functions have explicit parameter
        # and return annotations before we rewrite statements in the body.
        if lookup_name in self.stub_annotations["functions"]:
            data: dict[str, TypingAny] = self.stub_annotations["functions"][lookup_name]
            new_returns: cst.Annotation | cst.BaseExpression | None = (
                self._simplify_type(data["returns"]) if data["returns"] else updated_node.returns
            )
            if new_returns and not isinstance(new_returns, cst.Annotation):
                new_returns = cst.Annotation(annotation=new_returns)

            new_params: list[cst.Param] = []
            for param in updated_node.params.params:
                new_param: cst.Param = param
                if param.name.value in data["params"]:
                    p_type: cst.BaseExpression | None = self._simplify_type(data["params"][param.name.value])
                    if p_type is not None:
                        new_param = param.with_changes(annotation=cst.Annotation(annotation=p_type))
                new_params.append(new_param)
            updated_node = updated_node.with_changes(
                returns=new_returns,
                params=updated_node.params.with_changes(params=new_params),
            )

        # Fill missing/weak parameter annotations with local flow-derived types.
        filled_params: list[cst.Param] = []
        for param in updated_node.params.params:
            new_param = param
            current_ann: cst.BaseExpression | None = param.annotation.annotation if param.annotation else None
            current_ann_str: str = node_to_str(current_ann) if current_ann else ""
            if current_ann is None or current_ann_str in {"Any", "Incomplete"}:
                flow_ann: cst.BaseExpression | None = self._get_best_ann(param.name.value)
                if flow_ann and node_to_str(flow_ann) != "Any":
                    new_param = param.with_changes(annotation=cst.Annotation(annotation=flow_ann))
            filled_params.append(new_param)
        updated_node = updated_node.with_changes(
            params=updated_node.params.with_changes(params=filled_params),
        )

        # Then insert any missing loop-index declarations needed by the Lean pipeline.
        new_body_list: list[cst.BaseStatement] = self._add_loop_declarations(list(updated_node.body.body))
        updated_node = updated_node.with_changes(body=updated_node.body.with_changes(body=new_body_list))
        self.current_function = self.function_stack.pop() if self.function_stack else None
        return updated_node

    def _simplify_type(self, node: TypingAny) -> cst.BaseExpression | None:
        if not node:
            return None
        if isinstance(node, cst.Name) and node.value in {"Incomplete", "Unknown"}:
            return cst.Name("Any")
        if isinstance(node, cst.Name) and node.value == "Self":
            return cst.Name(self.current_class) if self.current_class else cst.Name("Any")
        if isinstance(node, cst.Integer):
            return cst.Name("int")
        if isinstance(node, cst.SimpleString):
            return cst.Name("str")
        if isinstance(node, cst.Float):
            return cst.Name("float")
        if isinstance(node, cst.Subscript) and isinstance(node.value, cst.Name):
            name: str = node.value.value
            if name in ["Literal", "Final", "Annotated"]:
                if node.slice and hasattr(node.slice[0].slice, "value"):
                    return self._simplify_type(node.slice[0].slice.value)
            if name == "Optional":
                if node.slice and hasattr(node.slice[0].slice, "value"):
                    inner: cst.BaseExpression | None = self._simplify_type(node.slice[0].slice.value)
                    if inner is None:
                        return cst.Name("Any")
                    return cst.BinaryOperation(left=inner, operator=cst.BitOr(), right=cst.Name("None"))
        return node

    def _get_best_ann(
        self,
        name: str,
        val_node: cst.BaseExpression | None = None,
    ) -> cst.BaseExpression | None:
        """Pick the strongest annotation source: flow info, then stubs, then literals."""
        scope_key: tuple[str | None, str | None, str] = (self.current_class, self.current_function, name)
        flow_type_str: str | None = self.flow_types.get(scope_key)
        if flow_type_str and flow_type_str != "Any":
            try:
                return cst.parse_expression(flow_type_str)
            except Exception:
                pass
        stub_type: cst.BaseExpression | None = self.stub_annotations["globals"].get(name)
        if stub_type:
            return self._simplify_type(stub_type)
        if val_node:
            if isinstance(val_node, cst.Integer):
                return cst.Name("int")
            if isinstance(val_node, cst.SimpleString):
                return cst.Name("str")
            if isinstance(val_node, cst.Float):
                return cst.Name("float")
        return None

    def _ann_decl_stmt(self, name: str, ann: cst.BaseExpression) -> cst.SimpleStatementLine:
        return cst.SimpleStatementLine(
            body=[
                cst.AnnAssign(
                    target=cst.Name(name),
                    annotation=cst.Annotation(annotation=ann),
                )
            ]
        )

    def _extract_match_binder_names(self, pattern: cst.CSTNode) -> list[str]:
        names: list[str] = []
        if isinstance(pattern, cst.MatchAs):
            if isinstance(pattern.name, cst.Name) and pattern.name.value != "_":
                names.append(pattern.name.value)
            if pattern.pattern is not None:
                names.extend(self._extract_match_binder_names(pattern.pattern))
        elif isinstance(pattern, cst.MatchTuple):
            for element in pattern.patterns:
                if isinstance(element, cst.MatchSequenceElement):
                    names.extend(self._extract_match_binder_names(element.value))
        elif isinstance(pattern, cst.MatchOr):
            for element in pattern.patterns:
                names.extend(self._extract_match_binder_names(element.pattern))
        return names

    def _extract_comp_target_names(self, comp_for: cst.CompFor) -> list[str]:
        return extract_comp_target_names(comp_for)

    def _extract_comp_target_names_in_expr(self, expr: cst.BaseExpression | None) -> list[str]:
        names: list[str] = []
        seen: set[str] = set()
        for comp in iter_comprehension_exprs(expr):
            for name in self._extract_comp_target_names(comp.for_in):
                if name in seen:
                    continue
                seen.add(name)
                names.append(name)
        return names

    def _collect_comp_target_decl_lines(
        self,
        expr: cst.BaseExpression | None,
        declared: set[str],
    ) -> list[cst.BaseStatement]:
        decl_lines: list[cst.BaseStatement] = []
        for comp_name in self._extract_comp_target_names_in_expr(expr):
            if comp_name in declared:
                continue
            best_comp_ann: cst.BaseExpression | None = self._get_best_ann(comp_name)
            if best_comp_ann and node_to_str(best_comp_ann) != "Any":
                decl_lines.append(self._ann_decl_stmt(comp_name, best_comp_ann))
                declared.add(comp_name)
        return decl_lines

    def leave_SimpleStatementLine(
        self,
        original_node: cst.SimpleStatementLine,
        updated_node: cst.SimpleStatementLine,
    ) -> cst.SimpleStatementLine | cst.FlattenSentinel[cst.BaseStatement]:
        if len(updated_node.body) != 1:
            return updated_node

        stmt: cst.BaseSmallStatement = updated_node.body[0]
        if isinstance(stmt, cst.Assign) and len(stmt.targets) == 1:
            target: cst.BaseAssignTargetExpression = stmt.targets[0].target
            if isinstance(target, cst.Name):
                best: cst.BaseExpression | None = self._get_best_ann(target.value, stmt.value)
                if best:
                    return updated_node.with_changes(
                        body=[
                            cst.AnnAssign(
                                target=target,
                                annotation=cst.Annotation(annotation=best),
                                value=stmt.value,
                                equal=cst.AssignEqual(
                                    whitespace_before=cst.SimpleWhitespace(" "),
                                    whitespace_after=cst.SimpleWhitespace(" "),
                                ),
                            )
                        ]
                    )
            elif isinstance(target, cst.Attribute) and isinstance(target.value, cst.Name) and target.value.value == "self":
                best_attr: cst.BaseExpression | None = self._get_best_ann(f"self.{target.attr.value}", stmt.value)
                if best_attr:
                    return updated_node.with_changes(
                        body=[
                            cst.AnnAssign(
                                target=target,
                                annotation=cst.Annotation(annotation=best_attr),
                                value=stmt.value,
                                equal=cst.AssignEqual(
                                    whitespace_before=cst.SimpleWhitespace(" "),
                                    whitespace_after=cst.SimpleWhitespace(" "),
                                ),
                            )
                        ]
                    )
            elif isinstance(target, (cst.Tuple, cst.List)):
                if isinstance(stmt.value, (cst.Tuple, cst.List)) and len(target.elements) == len(stmt.value.elements):
                    split_lines: list[cst.BaseStatement] = []
                    for idx, element in enumerate(target.elements):
                        if not isinstance(element.value, cst.Name):
                            continue
                        rhs: cst.BaseExpression = stmt.value.elements[idx].value
                        best: cst.BaseExpression | None = self._get_best_ann(element.value.value, rhs)
                        if best:
                            split_lines.append(
                                cst.SimpleStatementLine(
                                    body=[
                                        cst.AnnAssign(
                                            target=element.value,
                                            annotation=cst.Annotation(annotation=best),
                                            value=rhs,
                                            equal=cst.AssignEqual(
                                                whitespace_before=cst.SimpleWhitespace(" "),
                                                whitespace_after=cst.SimpleWhitespace(" "),
                                            ),
                                        )
                                    ]
                                )
                            )
                        else:
                            split_lines.append(
                                cst.SimpleStatementLine(
                                    body=[
                                        cst.Assign(
                                            targets=[cst.AssignTarget(target=element.value)],
                                            value=rhs,
                                        )
                                    ]
                                )
                            )
                    if split_lines:
                        return cst.FlattenSentinel(split_lines)
                self.unpack_counter += 1
                tmp_name: str = f"__unpack_tmp_{self.unpack_counter}"
                split_lines: list[cst.BaseStatement] = [
                    cst.SimpleStatementLine(
                        body=[
                            cst.Assign(
                                targets=[cst.AssignTarget(target=cst.Name(tmp_name))],
                                value=stmt.value,
                            )
                        ]
                    )
                ]
                for idx, element in enumerate(target.elements):
                    if not isinstance(element.value, cst.Name):
                        continue
                    rhs = cst.Subscript(
                        value=cst.Name(tmp_name),
                        slice=[
                            cst.SubscriptElement(
                                slice=cst.Index(value=cst.Integer(str(idx)))
                            )
                        ],
                    )
                    best_name: cst.BaseExpression | None = self._get_best_ann(element.value.value)
                    if best_name:
                        split_lines.append(
                            cst.SimpleStatementLine(
                                body=[
                                    cst.AnnAssign(
                                        target=element.value,
                                        annotation=cst.Annotation(annotation=best_name),
                                        value=rhs,
                                        equal=cst.AssignEqual(
                                            whitespace_before=cst.SimpleWhitespace(" "),
                                            whitespace_after=cst.SimpleWhitespace(" "),
                                        ),
                                    )
                                ]
                            )
                        )
                    else:
                        split_lines.append(
                            cst.SimpleStatementLine(
                                body=[
                                    cst.Assign(
                                        targets=[cst.AssignTarget(target=element.value)],
                                        value=rhs,
                                    )
                                ]
                            )
                        )
                if split_lines:
                    return cst.FlattenSentinel(split_lines)

        if isinstance(stmt, cst.AnnAssign) and isinstance(stmt.target, cst.Name):
            curr_type: str = node_to_str(stmt.annotation.annotation)
            best_ann: cst.BaseExpression | None = self._get_best_ann(stmt.target.value, stmt.value)
            if best_ann and node_to_str(best_ann) != curr_type:
                return updated_node.with_changes(
                    body=[stmt.with_changes(annotation=cst.Annotation(annotation=best_ann))]
                )

        return updated_node

    def _add_loop_declarations(self, body: list[cst.BaseStatement]) -> list[cst.BaseStatement]:
        new_body: list[cst.BaseStatement] = []
        declared: set[str] = set()
        for stmt in body:
            comp_decl_lines: list[cst.BaseStatement] = []
            if isinstance(stmt, cst.SimpleStatementLine):
                for sub in stmt.body:
                    if isinstance(sub, cst.AnnAssign):
                        comp_decl_lines.extend(self._collect_comp_target_decl_lines(sub.value, declared))
                        if isinstance(sub.target, cst.Name):
                            declared.add(sub.target.value)
                    elif isinstance(sub, cst.Assign) and len(sub.targets) == 1:
                        comp_decl_lines.extend(self._collect_comp_target_decl_lines(sub.value, declared))
                        tgt = sub.targets[0].target
                        if isinstance(tgt, cst.Name):
                            declared.add(tgt.value)
                    elif isinstance(sub, cst.Return):
                        comp_decl_lines.extend(self._collect_comp_target_decl_lines(sub.value, declared))
                    elif isinstance(sub, cst.Expr):
                        comp_decl_lines.extend(self._collect_comp_target_decl_lines(sub.value, declared))
            if comp_decl_lines:
                new_body.extend(comp_decl_lines)
            if isinstance(stmt, cst.For) and isinstance(stmt.target, cst.Name):
                var: str = stmt.target.value
                iter_is_range: bool = (
                    isinstance(stmt.iter, cst.Call)
                    and isinstance(stmt.iter.func, cst.Name)
                    and stmt.iter.func.value == "range"
                )
                if var != "_" and var not in declared and iter_is_range:
                    new_body.append(
                        cst.SimpleStatementLine(
                            body=[cst.AnnAssign(target=stmt.target, annotation=cst.Annotation(cst.Name("int")))]
                        )
                    )
                    declared.add(var)
            if isinstance(stmt, cst.Try):
                new_handlers: list[cst.ExceptHandler] = []
                for handler in stmt.handlers:
                    updated_handler = handler
                    if (
                        isinstance(handler.name, cst.AsName)
                        and isinstance(handler.name.name, cst.Name)
                        and hasattr(handler.body, "body")
                    ):
                        exc_name: str = handler.name.name.value
                        best_exc_ann: cst.BaseExpression | None = self._get_best_ann(exc_name)
                        if best_exc_ann and node_to_str(best_exc_ann) != "Any":
                            handler_body = list(handler.body.body)
                            if not (
                                handler_body
                                and isinstance(handler_body[0], cst.SimpleStatementLine)
                                and len(handler_body[0].body) == 1
                                and isinstance(handler_body[0].body[0], cst.AnnAssign)
                                and isinstance(handler_body[0].body[0].target, cst.Name)
                                and handler_body[0].body[0].target.value == exc_name
                            ):
                                handler_body = [self._ann_decl_stmt(exc_name, best_exc_ann)] + handler_body
                            updated_handler = handler.with_changes(
                                body=handler.body.with_changes(body=handler_body),
                            )
                    new_handlers.append(updated_handler)
                stmt = stmt.with_changes(handlers=tuple(new_handlers))
            if isinstance(stmt, cst.Match):
                new_cases: list[cst.MatchCase] = []
                for case in stmt.cases:
                    if not hasattr(case.body, "body"):
                        new_cases.append(case)
                        continue
                    case_body = list(case.body.body)
                    to_prepend: list[cst.BaseStatement] = []
                    seen: set[str] = set()
                    for binder in self._extract_match_binder_names(case.pattern):
                        if binder in seen:
                            continue
                        seen.add(binder)
                        best_binder_ann: cst.BaseExpression | None = self._get_best_ann(binder)
                        if best_binder_ann and node_to_str(best_binder_ann) != "Any":
                            to_prepend.append(self._ann_decl_stmt(binder, best_binder_ann))
                    if to_prepend:
                        case_body = to_prepend + case_body
                        case = case.with_changes(
                            body=case.body.with_changes(body=case_body),
                        )
                    new_cases.append(case)
                stmt = stmt.with_changes(cases=tuple(new_cases))
            new_body.append(stmt)
        return new_body


class FlowTracker(cst.CSTVisitor):
    """Collect lightweight variable/return type facts across repeated fixed-point passes."""
    def __init__(
        self,
        initial_types: dict[tuple[str | None, str | None, str], set[str]],
        stub_data: dict[str, TypingAny],
    ) -> None:
        self.var_types: dict[tuple[str | None, str | None, str], set[str]] = initial_types
        self.stub_data: dict[str, TypingAny] = stub_data
        self.current_class: str | None = None
        self.current_function: str | None = None
        self.function_stack: list[str] = []
        self.return_types: dict[str, set[str]] = {}

    def visit_ClassDef(self, node: cst.ClassDef) -> bool:
        self.current_class = node.name.value
        return True

    def leave_ClassDef(self, node: cst.ClassDef) -> None:
        self.current_class = None

    def visit_FunctionDef(self, node: cst.FunctionDef) -> bool:
        if self.current_function is not None:
            self.function_stack.append(self.current_function)
        self.current_function = node.name.value
        lookup: str = f"{self.current_class}.{self.current_function}" if self.current_class else self.current_function

        fn_data: dict[str, TypingAny] = self.stub_data["functions"].setdefault(
            lookup,
            {"returns": None, "params": {}},
        )
        params: dict[str, TypingAny] = fn_data.setdefault("params", {})
        for param in node.params.params:
            params.setdefault(param.name.value, cst.Name("Any"))

        # Seed parameter facts from in-source annotations.
        for param in node.params.params:
            if param.annotation is not None:
                param_t: str = node_to_str(param.annotation.annotation).replace("'", "").replace('"', "")
                if param_t not in {"", "Any", "Incomplete", "Unknown"}:
                    self._add_type(param.name.value, param_t)

        # Seed/refresh parameter facts from stub data accumulated across passes.
        if lookup in self.stub_data["functions"]:
            fn_data: dict[str, TypingAny] = self.stub_data["functions"][lookup]
            for p_name, p_ann in fn_data.get("params", {}).items():
                p_t: str = node_to_str(p_ann).replace("'", "").replace('"', "")
                if p_t not in {"", "Any", "Incomplete", "Unknown"}:
                    self._add_type(p_name, p_t)
        return True

    def leave_FunctionDef(self, node: cst.FunctionDef) -> None:
        if self.current_function:
            lookup: str = f"{self.current_class}.{self.current_function}" if self.current_class else self.current_function
            observed: set[str] = self.return_types.get(lookup, set())
            non_any: list[str] = sorted([t for t in observed if t and t != "Any"])
            if non_any:
                if lookup not in self.stub_data["functions"]:
                    self.stub_data["functions"][lookup] = {"returns": None, "params": {}}
                self.stub_data["functions"][lookup]["returns"] = cst.parse_expression(" | ".join(non_any))
        self.current_function = self.function_stack.pop() if self.function_stack else None

    def _get_key(self, name: str) -> tuple[str | None, str | None, str]:
        return (self.current_class, self.current_function, name)

    def _add_type(self, name: str, t: str | None) -> None:
        if not t or t == "Any":
            return
        key: tuple[str | None, str | None, str] = self._get_key(name)
        if key not in self.var_types:
            self.var_types[key] = set()
        for part in split_top_level(t, "|"):
            p: str = part.strip()
            if p:
                self.var_types[key].add(p)
        # Drop weak container variants once a stronger variant is available.
        for prefix in ("list", "set", "generator"):
            any_variant: str = f"{prefix}[Any]"
            if any_variant in self.var_types[key] and any(
                x.startswith(f"{prefix}[") and x != any_variant for x in self.var_types[key]
            ):
                self.var_types[key].remove(any_variant)
        if "dict[Any, Any]" in self.var_types[key] and any(
            x.startswith("dict[") and x != "dict[Any, Any]" for x in self.var_types[key]
        ):
            self.var_types[key].remove("dict[Any, Any]")

    def _record_return_type(self, t: str) -> None:
        if not self.current_function or not t or t == "Any":
            return
        lookup: str = f"{self.current_class}.{self.current_function}" if self.current_class else self.current_function
        if lookup not in self.return_types:
            self.return_types[lookup] = set()
        for part in split_top_level(t, "|"):
            p = part.strip()
            if p:
                self.return_types[lookup].add(p)

    def _iterable_item_type(self, node: cst.CSTNode) -> str:
        if (
            isinstance(node, cst.Call)
            and isinstance(node.func, cst.Name)
            and node.func.value == "range"
        ):
            return "int"
        inferred: str = self._infer_node(node)
        item_types: list[str] = []
        for part in split_top_level(inferred, "|"):
            p = part.strip()
            if not p:
                continue
            if p == "str":
                item_types.append("str")
                continue
            found = False
            for prefix in ("list", "set", "generator"):
                inner: str | None = extract_generic_inner(p, prefix)
                if inner is not None:
                    item_types.append(inner)
                    found = True
                    break
            if found:
                continue
            dict_inner: str | None = extract_generic_inner(p, "dict")
            if dict_inner is not None:
                parts = split_top_level(dict_inner, ",")
                item_types.append(parts[0] if parts else "Any")
                continue
            tup_parts = tuple_type_parts(p)
            if tup_parts is not None:
                item_types.append(normalize_union(" | ".join(tup_parts)))
        if not item_types:
            return "Any"
        return normalize_union(" | ".join(item_types))

    def _bind_target_with_item_type(self, target: cst.CSTNode, item_t: str) -> None:
        if isinstance(target, cst.Name):
            self._add_type(target.value, item_t)
            return
        if isinstance(target, (cst.Tuple, cst.List)):
            tup_parts: list[str] | None = tuple_type_parts(item_t)
            for idx, element in enumerate(target.elements):
                if not isinstance(element.value, cst.Name):
                    continue
                part_t: str = tup_parts[idx] if tup_parts is not None and idx < len(tup_parts) else "Any"
                self._add_type(element.value.value, part_t)

    def _bind_comp_for_targets(self, comp_for: cst.CompFor) -> None:
        item_t: str = self._iterable_item_type(comp_for.iter)
        self._bind_target_with_item_type(comp_for.target, item_t)
        if comp_for.inner_for_in is not None:
            self._bind_comp_for_targets(comp_for.inner_for_in)

    def _bind_comp_targets_in_expr(self, expr: cst.BaseExpression | None) -> None:
        for comp in iter_comprehension_exprs(expr):
            self._bind_comp_for_targets(comp.for_in)

    def _infer_match_pattern_type(self, pattern: cst.CSTNode) -> str:
        if isinstance(pattern, cst.MatchValue):
            return self._infer_node(pattern.value)
        if isinstance(pattern, cst.MatchSingleton):
            if isinstance(pattern.value, cst.Name) and pattern.value.value in {"True", "False"}:
                return "bool"
            if isinstance(pattern.value, cst.Name) and pattern.value.value == "None":
                return "None"
            return "Any"
        if isinstance(pattern, cst.MatchTuple):
            element_types: list[str] = []
            for element in pattern.patterns:
                if isinstance(element, cst.MatchSequenceElement):
                    element_types.append(self._infer_match_pattern_type(element.value))
            return f"tuple[{', '.join(element_types)}]" if element_types else "tuple[Any]"
        if isinstance(pattern, cst.MatchOr):
            pattern_types: list[str] = []
            for element in pattern.patterns:
                pattern_types.append(self._infer_match_pattern_type(element.pattern))
            return normalize_union(" | ".join([p for p in pattern_types if p and p != "Any"]))
        if isinstance(pattern, cst.MatchAs):
            if pattern.pattern is not None:
                return self._infer_match_pattern_type(pattern.pattern)
            return "Any"
        return "Any"

    def _bind_match_pattern_names(self, pattern: cst.CSTNode, subject_t: str) -> None:
        if isinstance(pattern, cst.MatchAs):
            if isinstance(pattern.name, cst.Name) and pattern.name.value != "_":
                self._add_type(pattern.name.value, subject_t)
            if pattern.pattern is not None:
                self._bind_match_pattern_names(pattern.pattern, subject_t)
            return
        if isinstance(pattern, cst.MatchTuple):
            parts: list[str] | None = tuple_type_parts(subject_t)
            for idx, element in enumerate(pattern.patterns):
                if not isinstance(element, cst.MatchSequenceElement):
                    continue
                elem_t: str = parts[idx] if parts is not None and idx < len(parts) else "Any"
                self._bind_match_pattern_names(element.value, elem_t)
            return
        if isinstance(pattern, cst.MatchOr):
            for element in pattern.patterns:
                self._bind_match_pattern_names(element.pattern, subject_t)

    def _infer_except_type(self, node: cst.BaseExpression | None) -> str:
        if node is None:
            return "Exception"
        if isinstance(node, cst.Name):
            return node.value
        if isinstance(node, cst.Tuple):
            parts: list[str] = []
            for element in node.elements:
                if isinstance(element.value, cst.Name):
                    parts.append(element.value.value)
            if parts:
                return normalize_union(" | ".join(parts))
        return "Exception"

    def visit_Return(self, node: cst.Return) -> bool:
        if self.current_function:
            self._bind_comp_targets_in_expr(node.value)
            ret_t: str = self._infer_node(node.value) if node.value else "None"
            self._record_return_type(ret_t)
        return True

    def visit_Assign(self, node: cst.Assign) -> bool:
        if len(node.targets) == 1:
            self._bind_comp_targets_in_expr(node.value)
            target: cst.BaseAssignTargetExpression = node.targets[0].target
            if isinstance(target, cst.Name):
                self._add_type(target.value, self._infer_node(node.value))
            elif isinstance(target, cst.Attribute) and isinstance(target.value, cst.Name) and target.value.value == "self":
                self._add_type(f"self.{target.attr.value}", self._infer_node(node.value))
            elif isinstance(target, (cst.Tuple, cst.List)):
                val_t: str = self._infer_node(node.value)
                if val_t.startswith("tuple["):
                    content: str = val_t[6:-1]
                    parts: list[str] = []
                    bracket_level: int = 0
                    current: str = ""
                    for char in content:
                        if char == "[":
                            bracket_level += 1
                        elif char == "]":
                            bracket_level -= 1
                        if char == "," and bracket_level == 0:
                            parts.append(current.strip())
                            current = ""
                        else:
                            current += char
                    parts.append(current.strip())

                    for i, e in enumerate(target.elements):
                        if i < len(parts) and isinstance(e.value, cst.Name):
                            self._add_type(e.value.value, parts[i])
        return True

    def visit_AnnAssign(self, node: cst.AnnAssign) -> bool:
        self._bind_comp_targets_in_expr(node.value)
        return True

    def visit_Expr(self, node: cst.Expr) -> bool:
        self._bind_comp_targets_in_expr(node.value)
        return True

    def visit_For(self, node: cst.For) -> bool:
        self._bind_target_with_item_type(node.target, self._iterable_item_type(node.iter))
        return True

    def visit_ExceptHandler(self, node: cst.ExceptHandler) -> bool:
        if isinstance(node.name, cst.AsName) and isinstance(node.name.name, cst.Name):
            self._add_type(node.name.name.value, self._infer_except_type(node.type))
        return True

    def visit_Match(self, node: cst.Match) -> bool:
        tuple_element_hints: dict[int, set[str]] = {}
        for case in node.cases:
            if isinstance(case.pattern, cst.MatchTuple):
                for idx, element in enumerate(case.pattern.patterns):
                    if not isinstance(element, cst.MatchSequenceElement):
                        continue
                    elem_t = self._infer_match_pattern_type(element.value)
                    valid = [p for p in split_top_level(elem_t, "|") if p and p != "Any"]
                    if not valid:
                        continue
                    if idx not in tuple_element_hints:
                        tuple_element_hints[idx] = set()
                    tuple_element_hints[idx].update(valid)

        subject_t_candidates: list[str] = []
        for case in node.cases:
            t = self._infer_match_pattern_type(case.pattern)
            if isinstance(case.pattern, cst.MatchTuple):
                parts = tuple_type_parts(t) or []
                if parts:
                    refined_parts: list[str] = []
                    for idx, part in enumerate(parts):
                        if part == "Any" and idx in tuple_element_hints and tuple_element_hints[idx]:
                            refined_parts.append(normalize_union(" | ".join(sorted(tuple_element_hints[idx]))))
                        else:
                            refined_parts.append(part)
                    t = f"tuple[{', '.join(refined_parts)}]"
            if t and t != "Any":
                subject_t_candidates.append(t)
        subject_t: str = normalize_union(" | ".join(subject_t_candidates)) if subject_t_candidates else "Any"
        if isinstance(node.subject, cst.Name):
            self._add_type(node.subject.value, subject_t)
        for case in node.cases:
            self._bind_match_pattern_names(case.pattern, subject_t)
        return True

    def visit_Call(self, node: cst.Call) -> bool:
        if isinstance(node.func, cst.Attribute) and isinstance(node.func.value, cst.Name):
            var_name: str = node.func.value.value
            method: str = node.func.attr.value
            target: str = f"self.{node.func.attr.value}" if var_name == "self" else var_name
            if method in ["append", "add"] and node.args:
                self._add_type(f"{target}!!content", self._infer_node(node.args[0].value))
            if method == "extend" and node.args:
                arg_t: str = self._infer_node(node.args[0].value)
                if arg_t.startswith("list[") and arg_t.endswith("]"):
                    inner_t: str = arg_t[5:-1]
                    for p in [part.strip() for part in inner_t.split("|")]:
                        self._add_type(f"{target}!!content", p)
        elif isinstance(node.func, cst.Name):
            func_name: str = node.func.value
            fn_data: dict[str, TypingAny] | None = self.stub_data["functions"].get(func_name)
            if fn_data is not None:
                params: dict[str, TypingAny] = fn_data.setdefault("params", {})
                param_order: list[str] = list(params.keys())
                for idx, arg in enumerate(node.args):
                    arg_t: str = self._infer_node(arg.value)
                    if arg_t == "Any":
                        continue
                    param_name: str | None = None
                    if arg.keyword is not None and isinstance(arg.keyword, cst.Name):
                        param_name = arg.keyword.value
                    elif idx < len(param_order):
                        param_name = param_order[idx]
                    if not param_name:
                        continue
                    curr_t: str = ""
                    if param_name in params:
                        curr_t = node_to_str(params[param_name]).replace("'", "").replace('"', "")
                    candidates: list[str] = [arg_t]
                    if curr_t and curr_t not in {"Any", "Incomplete", "Unknown"}:
                        candidates.append(curr_t)
                    merged_t: str = normalize_union(" | ".join(candidates))
                    if merged_t != "Any":
                        params[param_name] = cst.parse_expression(merged_t)
        return True

    def _infer_node(self, node: cst.CSTNode) -> str:
        """Infer a best-effort string type for the small Python subset we currently handle."""
        if isinstance(node, cst.Integer):
            return "int"
        if isinstance(node, cst.SimpleString):
            return "str"
        if isinstance(node, cst.Float):
            return "float"
        if isinstance(node, cst.FormattedString):
            return "str"
        if isinstance(node, cst.BooleanOperation):
            return "bool"
        if isinstance(node, cst.Comparison):
            return "bool"
        if isinstance(node, cst.IfExp):
            b_t: str = self._infer_node(node.body)
            o_t: str = self._infer_node(node.orelse)
            if b_t == o_t:
                return b_t
            return normalize_union(f"{b_t} | {o_t}")
        if isinstance(node, cst.UnaryOperation):
            return self._infer_node(node.expression)
        if isinstance(node, cst.BinaryOperation):
            l_t: str = self._infer_node(node.left)
            r_t: str = self._infer_node(node.right)
            if isinstance(node.operator, cst.Add):
                if l_t == "str" or r_t == "str":
                    return "str"
                if l_t == "float" or r_t == "float":
                    return "float"
                if l_t == "int" and r_t == "int":
                    return "int"
            if isinstance(node.operator, (cst.Subtract, cst.Multiply, cst.Modulo)):
                if l_t == "float" or r_t == "float":
                    return "float"
                if l_t == "int" and r_t == "int":
                    return "int"
            if isinstance(node.operator, cst.Divide):
                return "float"
        if isinstance(node, cst.Name):
            if node.value in ["True", "False"]:
                return "bool"
            if node.value == "cls" and self.current_class:
                return self.current_class
            key: tuple[str | None, str | None, str] = self._get_key(node.value)
            if key in self.var_types:
                ts: list[str] = sorted([t for t in self.var_types[key] if t != "Any"])
                if ts:
                    return " | ".join(ts)
        if isinstance(node, cst.Attribute) and isinstance(node.value, cst.Name) and node.value.value == "self":
            key = self._get_key(f"self.{node.attr.value}")
            if key in self.var_types:
                ts = sorted([t for t in self.var_types[key] if t != "Any"])
                if ts:
                    return " | ".join(ts)
        if isinstance(node, cst.List):
            inner: str = self._infer_node(node.elements[0].value) if node.elements else "Any"
            return f"list[{inner}]"
        if isinstance(node, cst.Set):
            inner = self._infer_node(node.elements[0].value) if node.elements else "Any"
            return f"set[{inner}]"
        if isinstance(node, cst.Dict):
            if node.elements:
                key_types: set[str] = set()
                val_types: set[str] = set()
                for element in node.elements:
                    if element and element.key and element.value:
                        key_types.add(self._infer_node(element.key))
                        val_types.add(self._infer_node(element.value))
                if key_types and val_types:
                    key_union: str = " | ".join(sorted(key_types))
                    val_union: str = " | ".join(sorted(val_types))
                    return f"dict[{key_union}, {val_union}]"
            return "dict[Any, Any]"
        if isinstance(node, cst.Tuple):
            return f"tuple[{', '.join([self._infer_node(e.value) for e in node.elements])}]"
        if isinstance(node, cst.ListComp):
            self._bind_comp_for_targets(node.for_in)
            return f"list[{self._infer_node(node.elt)}]"
        if isinstance(node, cst.SetComp):
            self._bind_comp_for_targets(node.for_in)
            return f"set[{self._infer_node(node.elt)}]"
        if isinstance(node, cst.GeneratorExp):
            self._bind_comp_for_targets(node.for_in)
            return f"generator[{self._infer_node(node.elt)}]"
        if isinstance(node, cst.Call):
            name: str | None = None
            if isinstance(node.func, cst.Name):
                if node.func.value == "cls" and self.current_class:
                    return self.current_class
                name = node.func.value
            elif isinstance(node.func, cst.Attribute) and isinstance(node.func.value, cst.Name):
                if node.func.attr.value == "get" and len(node.args) > 1:
                    return self._infer_node(node.args[1].value)
                if node.func.value.value and node.func.value.value[0].isupper():
                    name = f"{node.func.value.value}.{node.func.attr.value}"
                if node.func.attr.value == "upper":
                    return "str"
            if name and name in self.stub_data["functions"]:
                ret = self.stub_data["functions"][name]["returns"]
                if ret:
                    res: str = node_to_str(ret).replace("'", "").replace('"', "")
                    if res == "Self":
                        if "." in name:
                            return name.split(".")[0]
                        if self.current_class:
                            return self.current_class
                    return res
        return "Any"

    def get_results(self) -> dict[tuple[str | None, str | None, str], str]:
        res: dict[tuple[str | None, str | None, str], str] = {}
        for key, types in self.var_types.items():
            cls, func, name = key
            valid: list[str] = sorted([t for t in types if t != "Any"])
            if not valid:
                continue
            if name.endswith("!!content"):
                res[(cls, func, name[:-9])] = f"list[{' | '.join(valid)}]"
            else:
                res[key] = " | ".join(valid)
        return res


def annotate_file(file_path: str, write_back: bool = True) -> str:
    """Prepare a Python file for Lean translation.

    High-level pipeline:
    1. Read the original source.
    2. Ask `pyrefly stubgen` for external type hints when available.
    3. Run repeated `FlowTracker` passes to stabilize local variable types.
    4. Rewrite the CST with `Lean4Annotator`.
    5. Normalize imports / typing spellings and optionally write the result back.
    """
    path: Path = Path(file_path).resolve()
    with open(path, "r") as f:
        original_src: str = f.read()
    if not HAS_LIBCST:
        return original_src
    temp_dir: Path = Path("temp_stubs")
    try:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        python_bin: Path = Path(sys.executable).parent
        pyrefly: str = str(python_bin / "pyrefly") if (python_bin / "pyrefly").exists() else "pyrefly"
        pyrefly_ok: bool = False
        try:
            stubgen_proc = subprocess.run(
                [pyrefly, "stubgen", str(path), "-o", str(temp_dir)],
                capture_output=True,
                text=True,
            )
            pyrefly_ok = stubgen_proc.returncode == 0
        except (FileNotFoundError, OSError):
            pyrefly_ok = False

        stub_path: Path | None = next(temp_dir.rglob("*.pyi"), None) if pyrefly_ok else None
        src: str = original_src
        tree: cst.Module = cst.parse_module(src)
        stub_data: dict[str, dict[str, TypingAny]] = {"globals": {}, "functions": {}}

        if stub_path:
            with open(stub_path, "r") as f:
                stub_src: str = f.read()

            class Extractor(cst.CSTVisitor):
                def __init__(self) -> None:
                    self.data: dict[str, dict[str, TypingAny]] = {"globals": {}, "functions": {}}
                    self.curr_cls: str | None = None

                def visit_ClassDef(self, node: cst.ClassDef) -> bool:
                    self.curr_cls = node.name.value
                    return True

                def leave_ClassDef(self, node: cst.ClassDef) -> None:
                    self.curr_cls = None

                def visit_AnnAssign(self, node: cst.AnnAssign) -> bool:
                    if isinstance(node.target, cst.Name) and self.curr_cls is None:
                        self.data["globals"][node.target.value] = node.annotation.annotation
                    return False

                def visit_FunctionDef(self, node: cst.FunctionDef) -> bool:
                    lkp: str = f"{self.curr_cls}.{node.name.value}" if self.curr_cls else node.name.value
                    self.data["functions"][lkp] = {
                        "returns": node.returns.annotation if node.returns else None,
                        "params": {
                            p.name.value: p.annotation.annotation
                            for p in node.params.params
                            if p.annotation
                        },
                    }
                    return True

            ext: Extractor = Extractor()
            cst.parse_module(stub_src).visit(ext)
            stub_data = ext.data

        types: dict[tuple[str | None, str | None, str], set[str]] = {}
        prev_stub_fp = stub_fingerprint(stub_data)
        # Re-run local flow tracking until the discovered type map stops changing.
        for _ in range(MAX_FLOW_PASSES):
            tracker: FlowTracker = FlowTracker(types, stub_data)
            tree.visit(tracker)
            new_res: dict[tuple[str | None, str | None, str], str] = tracker.get_results()
            new_types = {
                k: (
                    set(split_top_level(v, "|"))
                    if split_top_level(v, "|")
                    else {v}
                )
                for k, v in new_res.items()
            }
            curr_stub_fp = stub_fingerprint(stub_data)
            if new_types == types and curr_stub_fp == prev_stub_fp:
                break
            types = new_types
            prev_stub_fp = curr_stub_fp

        # Prefer observed function return types over conservative stubgen placeholders.
        for lookup, rtypes in tracker.return_types.items():
            valid: list[str] = sorted([t for t in rtypes if t and t != "Any"])
            if not valid:
                continue
            if lookup not in stub_data["functions"]:
                stub_data["functions"][lookup] = {"returns": None, "params": {}}
            stub_data["functions"][lookup]["returns"] = cst.parse_expression(" | ".join(valid))

        final_flow: dict[tuple[str | None, str | None, str], str] = {
            k: list(v)[0] if len(v) == 1 else " | ".join(sorted(list(v)))
            for k, v in types.items()
        }
        # Apply the final rewrite once we have a stable view of inferred types.
        final_tree: cst.Module = tree.visit(Lean4Annotator(stub_data, final_flow))
        code: str = (
            final_tree.code
            .replace("Incomplete", "Any")
            .replace("List[", "list[")
            .replace("Dict[", "dict[")
            .replace("Tuple[", "tuple[")
        )
        # if not code.startswith("from __future__ import annotations"):
        #     code = f"from __future__ import annotations\n\n{code}"
        needs: list[str] = []
        if "Any" in code:
            needs.append("Any")
        # if needs and "from typing import" not in code:
        #     code = f"from typing import {', '.join(needs)}\n\n{code}"
        if write_back:
            with open(path, "w") as f:
                f.write(code)
        return code
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError, cst.ParserSyntaxError):
        return original_src
    finally:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--file")
    parser.add_argument("--no-write", action="store_true")
    args = parser.parse_args()
    res: str = annotate_file(args.file, write_back=not args.no_write)
    if args.no_write and res:
        print(res)
    elif res:
        print(f"Annotated {args.file} for Lean 4")
