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
        self.unpack_counter: int = 0

    def visit_ClassDef(self, node: cst.ClassDef) -> bool:
        self.current_class = node.name.value
        return True

    def leave_ClassDef(self, original_node: cst.ClassDef, updated_node: cst.ClassDef) -> cst.ClassDef:
        self.current_class = None
        return updated_node

    def visit_FunctionDef(self, node: cst.FunctionDef) -> bool:
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

        # Then insert any missing loop-index declarations needed by the Lean pipeline.
        new_body_list: list[cst.BaseStatement] = self._add_loop_declarations(list(updated_node.body.body))
        updated_node = updated_node.with_changes(body=updated_node.body.with_changes(body=new_body_list))
        self.current_function = None
        return updated_node

    def _simplify_type(self, node: TypingAny) -> cst.BaseExpression | None:
        if not node:
            return None
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
            if isinstance(stmt, cst.SimpleStatementLine):
                for sub in stmt.body:
                    if isinstance(sub, cst.AnnAssign):
                        if isinstance(sub.target, cst.Name):
                            declared.add(sub.target.value)
                    elif isinstance(sub, cst.Assign) and len(sub.targets) == 1:
                        tgt = sub.targets[0].target
                        if isinstance(tgt, cst.Name):
                            declared.add(tgt.value)
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

    def visit_ClassDef(self, node: cst.ClassDef) -> bool:
        self.current_class = node.name.value
        return True

    def leave_ClassDef(self, node: cst.ClassDef) -> None:
        self.current_class = None

    def visit_FunctionDef(self, node: cst.FunctionDef) -> bool:
        self.current_function = node.name.value
        return True

    def leave_FunctionDef(self, node: cst.FunctionDef) -> None:
        self.current_function = None

    def _get_key(self, name: str) -> tuple[str | None, str | None, str]:
        return (self.current_class, self.current_function, name)

    def _add_type(self, name: str, t: str | None) -> None:
        if not t or t == "Any":
            return
        key: tuple[str | None, str | None, str] = self._get_key(name)
        if key not in self.var_types:
            self.var_types[key] = set()
        for part in t.split("|"):
            p: str = part.strip()
            if p:
                self.var_types[key].add(p)

    def visit_Return(self, node: cst.Return) -> bool:
        if self.current_function and node.value:
            lookup: str = f"{self.current_class}.{self.current_function}" if self.current_class else self.current_function
            ret_t: str = self._infer_node(node.value)
            if ret_t != "Any":
                if lookup not in self.stub_data["functions"]:
                    self.stub_data["functions"][lookup] = {"returns": None, "params": {}}
                curr = self.stub_data["functions"][lookup]["returns"]
                curr_str: str = node_to_str(curr) if curr else ""
                should_override: bool = (not curr) or (curr_str == "Any")
                if self.current_class and ret_t == self.current_class and curr_str in {"str", "Self", ""}:
                    should_override = True
                if should_override:
                    self.stub_data["functions"][lookup]["returns"] = cst.parse_expression(ret_t)
        return True

    def visit_Assign(self, node: cst.Assign) -> bool:
        if len(node.targets) == 1:
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
        return True

    def _infer_node(self, node: cst.CSTNode) -> str:
        """Infer a best-effort string type for the small Python subset we currently handle."""
        if isinstance(node, cst.Integer):
            return "int"
        if isinstance(node, cst.SimpleString):
            return "str"
        if isinstance(node, cst.Float):
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
                    return False

            ext: Extractor = Extractor()
            cst.parse_module(stub_src).visit(ext)
            stub_data = ext.data

        types: dict[tuple[str | None, str | None, str], set[str]] = {}
        # Re-run local flow tracking until the discovered type map stops changing.
        for _ in range(MAX_FLOW_PASSES):
            tracker: FlowTracker = FlowTracker(types, stub_data)
            tree.visit(tracker)
            new_res: dict[tuple[str | None, str | None, str], str] = tracker.get_results()
            new_types = {
                k: (
                    set(v.split(" | "))
                    if "list[" not in v and "dict[" not in v and "tuple[" not in v
                    else {v}
                )
                for k, v in new_res.items()
            }
            if new_types == types:
                break
            types = new_types

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
