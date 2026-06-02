import argparse
import sys
import os
import json
import ast
import atexit
import select
import re
from pathlib import Path
import subprocess
import logging
import threading
from collections import deque
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

HOMEDIR = Path.absolute(Path(__name__).parent.parent)
SRC_DIR = HOMEDIR / "src"
PY_EXEC = HOMEDIR / ".venv" / "bin" / "python"
logger = logging.getLogger(__name__)

def get_supported_libraries():
    # Read directory names from the Libraries folder to determine supported libraries
    libraries_path = Path(__file__).parent.parent / "Libraries"
    if not libraries_path.exists() or not libraries_path.is_dir():
        logger.warning("Libraries directory not found at %s; no libraries will be supported.", libraries_path)
        return set()
    return {f.name for f in libraries_path.iterdir() if f.is_dir()}

SUPPORTED_LIBRARY_IMPORTS = get_supported_libraries()

COMMENT_PLACEHOLDER_RE = re.compile(
    r"^(?P<indent>\s*)(?:let|def)\s+__pyastlean_comment_(?P<id>\d+)\b.*$"
)

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
def configure_logging(verbose: bool) -> None:
    """Configure CLI logging, keeping normal runs quiet unless verbose is enabled."""
    level = logging.DEBUG if verbose else logging.WARNING
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")


def _node_type(node):
    return node.get("node_type") if isinstance(node, dict) else None


def _walk_json_nodes(node, *, skip_nested_function_bodies=False):
    if isinstance(node, dict):
        yield node
        node_type = node.get("node_type")
        for key, value in node.items():
            if skip_nested_function_bodies and node_type == "FunctionDef" and key == "body":
                continue
            yield from _walk_json_nodes(value, skip_nested_function_bodies=skip_nested_function_bodies)
    elif isinstance(node, list):
        for item in node:
            yield from _walk_json_nodes(item, skip_nested_function_bodies=skip_nested_function_bodies)


def _comment_node_map(node):
    comments = {}
    for subnode in _walk_json_nodes(node):
        node_type = _node_type(subnode)
        if node_type not in {"Comment", "DocString"}:
            continue
        comment_id = subnode.get("comment_id")
        if comment_id is not None:
            comments[str(comment_id)] = subnode
    return comments


def _lean_comment_lines(comment_node, indent):
    text = str(comment_node.get("text", ""))
    if _node_type(comment_node) == "DocString":
        safe_lines = [line.replace("-/", "- /") for line in text.splitlines()] or [""]
        return [f"{indent}/-", *[f"{indent}{line}" for line in safe_lines], f"{indent}-/"]
    body = text.replace("\n", " ").replace("\r", " ").strip()
    return [f"{indent}-- {body}" if body else f"{indent}--"]


def _inject_comments_into_lean(ast_json, lean_code):
    comment_map = _comment_node_map(ast_json)
    if not comment_map:
        return lean_code
    output_lines = []
    for line in lean_code.splitlines():
        match = COMMENT_PLACEHOLDER_RE.match(line)
        if match is None:
            output_lines.append(line)
            continue
        comment_node = comment_map.get(match.group("id"))
        if comment_node is None:
            output_lines.append(line)
            continue
        output_lines.extend(_lean_comment_lines(comment_node, match.group("indent")))
    return "\n".join(output_lines)


def _direct_comment_code(ast_json):
    return "\n".join(_lean_comment_lines(ast_json, ""))


def _body_has_direct_exception_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) in {"Try", "Raise"}:
                return True
    return False


def _body_has_direct_io_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
                and func.get("id") in {"print", "input"}
            ):
                return True
    return False


def _body_calls_known_functions(body, known_names):
    called = set()
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name":
                func_name = func.get("id")
                if func_name in known_names:
                    called.add(func_name)
    return called


def _annotate_calls(node, effectful_names):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node["effect_mode"] = "except"
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls(value, effectful_names)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls(item, effectful_names)


def _annotate_calls_with_mode(node, effectful_names, effect_mode):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node.setdefault("effect_mode", effect_mode)
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls_with_mode(value, effectful_names, effect_mode)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls_with_mode(item, effectful_names, effect_mode)


def _annotate_direct_io_calls(node):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
                and func.get("id") in {"print", "input"}
            ):
                node.setdefault("effect_mode", "io")
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_direct_io_calls(value)
    elif isinstance(node, list):
        for item in node:
            _annotate_direct_io_calls(item)


def annotate_exception_effects(module_json):
    """Mark function defs and direct calls that require translated `Except` handling."""
    def annotate_scope(body):
        local_functions = {
            stmt["name"]: stmt
            for stmt in body
            if isinstance(stmt, dict) and stmt.get("node_type") == "FunctionDef"
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        effectful = {
            name: _body_has_direct_exception_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if effectful[name]:
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(effectful.get(callee, False) for callee in called):
                    effectful[name] = True
                    changed = True

        effectful_names = {name for name, is_effectful in effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if effectful[name]:
                fn["effect_mode"] = "except"
            _annotate_calls(fn.get("body", []), effectful_names)

        _annotate_calls(body, effectful_names)

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def annotate_io_effects(module_json):
    """Mark input/print-bearing function defs and direct calls that require translated `IO` handling."""
    def annotate_scope(body):
        local_functions = {
            stmt["name"]: stmt
            for stmt in body
            if isinstance(stmt, dict) and stmt.get("node_type") == "FunctionDef"
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        io_effectful = {
            name: _body_has_direct_io_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
            if fn.get("effect_mode") != "except"
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if fn.get("effect_mode") == "except":
                    continue
                if io_effectful.get(name, False):
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(io_effectful.get(callee, False) for callee in called):
                    io_effectful[name] = True
                    changed = True

        io_effectful_names = {name for name, is_effectful in io_effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if fn.get("effect_mode") == "except":
                continue
            if io_effectful.get(name, False):
                fn["effect_mode"] = "io"
            _annotate_direct_io_calls(fn.get("body", []))
            _annotate_calls_with_mode(fn.get("body", []), io_effectful_names, "io")

        _annotate_direct_io_calls(body)
        _annotate_calls_with_mode(body, io_effectful_names, "io")

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def _imported_alias_name(alias_node):
    asname = alias_node.get("asname")
    if isinstance(asname, str) and asname:
        return asname
    name = alias_node.get("name")
    if not isinstance(name, str) or not name:
        return None
    return name.split(".")[0]


def _stmt_bound_names(node):
    bound = set()
    if not isinstance(node, dict):
        return bound
    node_type = node.get("node_type")
    if node_type == "Name":
        ident = node.get("id")
        if isinstance(ident, str):
            bound.add(ident)
    elif node_type in {"Tuple", "List"}:
        for elt in node.get("elts", []):
            bound.update(_stmt_bound_names(elt))
    elif node_type == "arg":
        ident = node.get("arg")
        if isinstance(ident, str):
            bound.add(ident)
    elif node_type == "Assign":
        for target in node.get("targets", []):
            bound.update(_stmt_bound_names(target))
    elif node_type == "AnnAssign":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type == "AugAssign":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type == "For":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type == "FunctionDef":
        name = node.get("name")
        if isinstance(name, str):
            bound.add(name)
    return bound


def _function_arg_names(fn_node):
    args = fn_node.get("args", {})
    names = set()
    if not isinstance(args, dict):
        return names
    for key in ("posonlyargs", "args", "kwonlyargs"):
        for arg in args.get(key, []):
            names.update(_stmt_bound_names(arg))
    names.update(_stmt_bound_names(args.get("vararg")))
    names.update(_stmt_bound_names(args.get("kwarg")))
    return names


def _annotate_library_refs_in_expr(node, import_env):
    if isinstance(node, list):
        for item in node:
            _annotate_library_refs_in_expr(item, import_env)
        return
    if not isinstance(node, dict):
        return

    node_type = node.get("node_type")
    if node_type == "Name":
        binding = import_env.get(node.get("id"))
        if binding and binding.get("kind") == "member":
            node["library_module"] = binding["module"]
            node["library_member"] = binding["member"]
    elif node_type == "Attribute":
        value = node.get("value")
        if isinstance(value, dict) and value.get("node_type") == "Name":
            binding = import_env.get(value.get("id"))
            if binding and binding.get("kind") == "module":
                node["library_module"] = binding["module"]
                node["library_member"] = node.get("attr")

    for key, value in node.items():
        if node_type == "FunctionDef" and key == "body":
            continue
        _annotate_library_refs_in_expr(value, import_env)


def _annotate_library_imports_in_scope(body, inherited_env=None):
    env = dict(inherited_env or {})
    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        node_type = stmt.get("node_type")
        if node_type == "Import":
            for alias_node in stmt.get("names", []):
                if not isinstance(alias_node, dict):
                    continue
                module_name = alias_node.get("name")
                local_name = _imported_alias_name(alias_node)
                if (
                    isinstance(module_name, str)
                    and isinstance(local_name, str)
                    and module_name in SUPPORTED_LIBRARY_IMPORTS
                ):
                    env[local_name] = {"kind": "module", "module": module_name}
            continue
        if node_type == "ImportFrom":
            module_name = stmt.get("module")
            if isinstance(module_name, str) and module_name in SUPPORTED_LIBRARY_IMPORTS:
                for alias_node in stmt.get("names", []):
                    if not isinstance(alias_node, dict):
                        continue
                    member_name = alias_node.get("name")
                    local_name = _imported_alias_name(alias_node)
                    if isinstance(member_name, str) and isinstance(local_name, str):
                        env[local_name] = {
                            "kind": "member",
                            "module": module_name,
                            "member": member_name,
                        }
            continue

        _annotate_library_refs_in_expr(stmt, env)

        if node_type == "FunctionDef":
            child_env = dict(env)
            for arg_name in _function_arg_names(stmt):
                child_env.pop(arg_name, None)
            _annotate_library_imports_in_scope(stmt.get("body", []), child_env)
        else:
            for body_key in ("body", "orelse", "finalbody"):
                nested = stmt.get(body_key)
                if isinstance(nested, list):
                    _annotate_library_imports_in_scope(nested, dict(env))
            for handler in stmt.get("handlers", []):
                if isinstance(handler, dict):
                    _annotate_library_imports_in_scope(handler.get("body", []), dict(env))
            for case in stmt.get("cases", []):
                if isinstance(case, dict):
                    _annotate_library_imports_in_scope(case.get("body", []), dict(env))

        for bound_name in _stmt_bound_names(stmt):
            env.pop(bound_name, None)


def annotate_library_imports(module_json):
    """Annotate names/attributes that come from imported libraries such as `math`."""
    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        _annotate_library_imports_in_scope(module_json.get("body", []))


# ---------------------------------------------------------------------------
# Top-level state threading
#
# Lean has no top-level statement execution: a bare `if`/`for`/`while`/`match`
# at module scope cannot mutate a module global the way Python does. We instead
# treat each such top-level block as a *state transformer* over the names it
# mutates. This pass computes, for every top-level executable block, the set of
# names it assigns ("mutated_names"), so the Lean backend can lower the block to
# a value that returns the updated names and re-export each as a fresh `def`.
#
# We only ANNOTATE here (Python is good at write-set analysis); the Lean backend
# decides how to emit the fold / tuple-if / re-export syntax.
# ---------------------------------------------------------------------------

ASSIGNMENT_NODE_TYPES = {"Assign", "AnnAssign", "AugAssign"}
EXECUTABLE_BLOCK_NODE_TYPES = {"If", "For", "While", "Match", "Try"}
TOP_LEVEL_DECL_NODE_TYPES = {"FunctionDef", "Import", "ImportFrom", "Comment", "DocString"}


def _target_assigned_names(target):
    """Collect the Name ids written by an assignment/loop target (handles tuple unpacking)."""
    names = set()
    if not isinstance(target, dict):
        return names
    node_type = target.get("node_type")
    if node_type == "Name":
        ident = target.get("id")
        if isinstance(ident, str):
            names.add(ident)
    elif node_type in {"Tuple", "List"}:
        for elt in target.get("elts", []):
            names.update(_target_assigned_names(elt))
    # Subscript / Attribute targets (e.g. xs[0] = ...) do not bind a fresh name.
    return names


def _block_mutated_names(body):
    """Compute the set of plain names assigned anywhere within a statement list.

    Recurses into nested executable blocks so an outer block reports every name
    its sub-statements mutate. Does not descend into nested FunctionDef/Lambda
    bodies: those introduce their own scope and do not mutate module globals via
    plain assignment.
    """
    mutated = set()
    if not isinstance(body, list):
        return mutated
    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        node_type = stmt.get("node_type")
        if node_type in {"Assign", "AnnAssign"}:
            mutated.update(_target_assigned_names(stmt.get("target")))
        elif node_type == "AugAssign":
            mutated.update(_target_assigned_names(stmt.get("target")))
        elif node_type == "For":
            # The loop variable is local to the loop, not a re-exported global,
            # but names mutated inside the body are.
            mutated.update(_block_mutated_names(stmt.get("body", [])))
            mutated.update(_block_mutated_names(stmt.get("orelse", [])))
        elif node_type == "While":
            mutated.update(_block_mutated_names(stmt.get("body", [])))
            mutated.update(_block_mutated_names(stmt.get("orelse", [])))
        elif node_type == "If":
            mutated.update(_block_mutated_names(stmt.get("body", [])))
            mutated.update(_block_mutated_names(stmt.get("orelse", [])))
        elif node_type == "Match":
            for case in stmt.get("cases", []):
                if isinstance(case, dict):
                    mutated.update(_block_mutated_names(case.get("body", [])))
        elif node_type == "Try":
            mutated.update(_block_mutated_names(stmt.get("body", [])))
            mutated.update(_block_mutated_names(stmt.get("orelse", [])))
            mutated.update(_block_mutated_names(stmt.get("finalbody", [])))
            for handler in stmt.get("handlers", []):
                if isinstance(handler, dict):
                    mutated.update(_block_mutated_names(handler.get("body", [])))
    return mutated


def _plain_assign_name(stmt):
    """Return the single Name id a top-level `x = ...` binds, or None for other shapes."""
    if not (isinstance(stmt, dict) and stmt.get("node_type") == "Assign"):
        return None
    target = stmt.get("target")
    if isinstance(target, dict) and target.get("node_type") == "Name":
        return target.get("id")
    return None


class ToplevelStateError(Exception):
    """Raised when top-level state threading hits a case the block-local model rejects."""


def annotate_toplevel_state(module_json):
    """Annotate top-level executable blocks for state threading (block-local model).

    For each top-level `if`/`for`/`while`/`match`/`try` that mutates module names,
    we record `mutated_names` and a `state_init` map: the identifier the Lean
    backend should read for each name's pre-block value. When a mutated name was
    bound by an earlier top-level `x = ...`, that assignment is versioned (its
    target becomes `x<U+2080>`) so the clean name `x` can be re-exported with the
    block's result, avoiding Lean's immutable-`def` redefinition error.

    Scope (block-local): a name may be mutated by at most one top-level block, and
    a pre-block initializer may be assigned at most once. Anything outside this is
    rejected with a clear error rather than miscompiled.
    """
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return
    body = module_json.get("body", [])

    # Map each plain top-level assignment name -> the (single) Assign node, and
    # track how many times it has been (re)assigned at top level.
    init_assign = {}
    assign_count = {}
    for stmt in body:
        name = _plain_assign_name(stmt)
        if name is not None:
            init_assign[name] = stmt
            assign_count[name] = assign_count.get(name, 0) + 1

    already_mutated = set()
    for stmt in body:
        if not (isinstance(stmt, dict) and stmt.get("node_type") in EXECUTABLE_BLOCK_NODE_TYPES):
            continue
        all_mutated = _block_mutated_names([stmt])
        # Only names with a module-scope initializer are threaded globals. Names
        # assigned solely inside the block (e.g. tuple-unpack temporaries the
        # annotator introduced) are block-local and stay inside the lowering.
        mutated = sorted(name for name in all_mutated if name in init_assign)
        if not mutated:
            continue
        stmt["mutated_names"] = mutated

        state_init = {}
        for name in mutated:
            if name in already_mutated:
                raise ToplevelStateError(
                    f"top-level name '{name}' is mutated by more than one block; "
                    f"this is not supported yet (block-local state threading only)."
                )
            if assign_count.get(name, 0) > 1:
                raise ToplevelStateError(
                    f"top-level name '{name}' is assigned more than once before a "
                    f"mutating block; this is not supported yet."
                )
            # Version the initializer so the clean name is free for re-export.
            init_stmt = init_assign[name]
            versioned = f"{name}₀"  # name + subscript zero
            init_stmt["target"]["id"] = versioned
            state_init[name] = versioned
        stmt["state_init"] = state_init
        already_mutated.update(mutated)


def _is_main_guard_test(test):
    """Recognize the JSON for `__name__ == "__main__"`."""
    if not (isinstance(test, dict) and test.get("node_type") == "Compare"):
        return False
    if test.get("op") != "eq":
        return False
    left, right = test.get("left"), test.get("right")
    if not (isinstance(left, dict) and isinstance(right, dict)):
        return False
    left_is_name = left.get("node_type") == "Name" and left.get("id") == "__name__"
    right_is_main = (
        right.get("node_type") == "Constant" and right.get("value") == "__main__"
    )
    return left_is_name and right_is_main


def _rename_name_refs(node, old, new):
    """Rewrite every `Name` with id `old` to `new` throughout a JSON subtree."""
    if isinstance(node, dict):
        if node.get("node_type") == "Name" and node.get("id") == old:
            node["id"] = new
        for value in node.values():
            _rename_name_refs(value, old, new)
    elif isinstance(node, list):
        for item in node:
            _rename_name_refs(item, old, new)


def annotate_main_entrypoint(module_json):
    """Resolve the Python/Lean `main` naming collision and mark the `__main__` guard.

    - A top-level `def main()` with NO guard keeps the name `main` (importable).
    - A `__main__` guard with NO `def main` becomes Lean's `main` (the guard body).
    - When BOTH exist, the Python `def main` is renamed to `_main` (plus all
      references) so the guard can own Lean's entry-point name `main`.
    The guard node is tagged `is_main_guard` so the backend lowers it to `main`.
    """
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return
    body = module_json.get("body", [])

    has_main_def = any(
        isinstance(s, dict) and s.get("node_type") == "FunctionDef" and s.get("name") == "main"
        for s in body
    )
    guard = next(
        (
            s for s in body
            if isinstance(s, dict) and s.get("node_type") == "If"
            and _is_main_guard_test(s.get("test"))
        ),
        None,
    )

    if guard is not None:
        guard["is_main_guard"] = True
        if has_main_def:
            # Collision: the Python `main` function yields the name to the guard.
            # Rewrite every reference (call sites) `main` -> `_main` ...
            _rename_name_refs(module_json, "main", "_main")
            # ... and the FunctionDef's own name, which is a plain field, not a Name node.
            for s in body:
                if isinstance(s, dict) and s.get("node_type") == "FunctionDef" and s.get("name") == "main":
                    s["name"] = "_main"

def translate_to_json(source_code, filepath=None):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.
    """
    if filepath is not None:
        logger.debug("Annotating Python source from %s before AST translation.", filepath)
        logger.debug("Original source:\n%s", source_code)
        annotated_code = subprocess.run(
            [str(PY_EXEC), str(SRC_DIR / "annotate_python.py"), "--no-write", "--file", str(filepath)],
            text=True,
            capture_output=True,
        )
        if annotated_code.returncode != 0:
            logger.warning("Annotation failed: %s", annotated_code.stderr.strip())
            logger.warning("Falling back to unannotated source code for translation.")
        source_code = annotated_code.stdout if annotated_code.returncode == 0 else source_code

    logger.debug("Source passed to Python AST parser:\n%s", source_code)
    ast_tree = ast.parse(source_code)
    logger.debug("Parsed Python AST:\n%s", ast.dump(ast_tree, indent=4))
    translator = ASTToJsonLeanVisitor(source_code)
    data = translator.visit(ast_tree)
    annotate_library_imports(data)
    annotate_exception_effects(data)
    annotate_io_effects(data)
    annotate_main_entrypoint(data)
    annotate_toplevel_state(data)
    logger.debug("Generated JSON IR: %s", json.dumps(data))
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

class LeanBackendClient:
    """Persistent line-oriented client for the Lean backend server mode."""

    def __init__(self, cwd: Path):
        self.cwd = cwd
        self.proc = None
        self._stderr_lines = deque(maxlen=200)
        self._stderr_thread = None

    @property
    def binary_path(self):
        return self.cwd / ".lake" / "build" / "bin" / "py2lean"

    def _tracked_backend_sources(self):
        """Yield Lean source files whose freshness determines whether `py2lean` must be rebuilt."""
        explicit_files = [
            self.cwd / "py2lean.lean",
            self.cwd / "lakefile.lean",
            self.cwd / "lakefile.toml",
            self.cwd / "lean-toolchain",
        ]
        for path in explicit_files:
            if path.exists():
                yield path

        pyastlean_dir = self.cwd / "PyAstLean"
        if pyastlean_dir.exists():
            yield from pyastlean_dir.rglob("*.lean")
        libraries_dir = self.cwd / "Libraries"
        if libraries_dir.exists():
            yield from libraries_dir.rglob("*.lean")

    def _binary_needs_rebuild(self):
        """Return true when the backend binary is missing or older than tracked Lean sources."""
        binary = self.binary_path
        if not binary.exists():
            logger.debug("py2lean backend binary is missing; rebuild required.")
            return True

        binary_mtime = binary.stat().st_mtime
        latest_source_mtime = max(
            (path.stat().st_mtime for path in self._tracked_backend_sources()),
            default=0.0,
        )
        if latest_source_mtime > binary_mtime:
            logger.debug(
                "A tracked Lean source is newer than the py2lean backend binary; rebuild required."
            )
            return True
        return False

    def _ensure_binary(self):
        if not self._binary_needs_rebuild():
            logger.debug("Reusing existing py2lean backend binary; no rebuild needed.")
            return

        logger.debug("Building py2lean backend binary before starting server.")
        build = subprocess.run(
            ["lake", "build", "py2lean"],
            cwd=self.cwd,
            text=True,
            capture_output=True,
        )
        if build.returncode != 0:
            raise RuntimeError(build.stderr.strip() or build.stdout.strip() or "lake build py2lean failed")

    def _command(self):
        return ["lake", "env", str(self.binary_path), "--server"]

    def _drain_stderr(self):
        assert self.proc is not None and self.proc.stderr is not None
        for line in self.proc.stderr:
            line = line.rstrip()
            if not line:
                continue
            self._stderr_lines.append(line)
            logger.debug("Lean backend stderr: %s", line)

    def _recent_stderr(self):
        return "\n".join(self._stderr_lines)

    def _one_shot_request(self, ast_json, target, check=True):
        """Fallback backend path that avoids the persistent server when it misbehaves."""
        json_task = json.dumps(
            {"task": "translate", "ast": ast_json, "target": target, "check": check},
            separators=(",", ":"),
        )
        cmd = ["lake", "exe", "py2lean", json_task, target]
        logger.debug("Falling back to one-shot Lean backend: %s", cmd)
        proc = subprocess.run(
            cmd,
            cwd=self.cwd,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            return {
                "result": False,
                "error": proc.stderr.strip() or proc.stdout.strip() or "Lean backend failed",
            }
        output = proc.stdout.strip()
        try:
            return json.loads(output)
        except json.JSONDecodeError as err:
            return {
                "result": False,
                "error": f"Invalid JSON response from one-shot Lean backend: {err}\n{output}",
            }

    def start(self):
        if self.proc is not None and self.proc.poll() is None:
            return
        self._ensure_binary()
        cmd = self._command()
        logger.debug("Starting persistent Lean backend: %s", cmd)
        self.proc = subprocess.Popen(
            cmd,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self._stderr_lines.clear()
        self._stderr_thread = threading.Thread(target=self._drain_stderr, daemon=True)
        self._stderr_thread.start()

    def close(self):
        if self.proc is None:
            return
        try:
            if self.proc.stdin is not None:
                self.proc.stdin.close()
        except BrokenPipeError:
            pass
        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=2)
        finally:
            if self.proc.stdout is not None:
                self.proc.stdout.close()
            if self.proc.stderr is not None:
                self.proc.stderr.close()
        self.proc = None
        self._stderr_thread = None

    def request(self, ast_json, target, check=True):
        """Send one translation request to the persistent Lean backend."""
        self.start()
        assert self.proc is not None
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        json_task = json.dumps(
            {"task": "translate", "ast": ast_json, "target": target, "check": check},
            separators=(",", ":"),
        )
        logger.debug("Sending request to Lean backend: target=%s check=%s", target, check)
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return self._one_shot_request(ast_json, target, check)

        assert self.proc.stdout is not None
        ready, _, _ = select.select([self.proc.stdout], [], [], 5.0)
        if not ready:
            logger.debug("Persistent Lean backend timed out waiting for a response; retrying once-shot.")
            self.close()
            return self._one_shot_request(ast_json, target, check)

        response_line = self.proc.stdout.readline()
        if not response_line:
            self.close()
            return self._one_shot_request(ast_json, target, check)
        response_line = response_line.strip()
        logger.debug("Lean backend response: %s", response_line)
        try:
            return json.loads(response_line)
        except json.JSONDecodeError as err:
            logger.debug(f"Persistent Lean backend returned invalid JSON; retrying one-shot: {err}")
            self.close()
            return self._one_shot_request(ast_json, target, check)

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


_LEAN_BACKEND = LeanBackendClient(parent_dir)
atexit.register(_LEAN_BACKEND.close)


def invoke_lean_backend(ast_json, target, check=True, client=None):
    """Send one JSON AST node to the Lean backend and return the parsed JSON response."""
    backend = client or _LEAN_BACKEND
    try:
        return backend.request(ast_json, target, check)
    except Exception as err:
        return {"result": False, "error": str(err)}

def translate_to_lean(source_code, target="term", filepath = None, imports_add = True):
    """Translate Python source to Lean via JSON IR and the Lean backend executable."""
    json_ir = translate_to_json(source_code, filepath)
    ast_json = json.loads(json_ir)
    client = _LEAN_BACKEND

    if ast_json.get("node_type") == "Module":
        body = ast_json.get("body", [])
        if target == "command":
            code_parts = []
            for stmt in body:
                # A top-level Python `pass` is a true no-op, so there is no Lean command to emit.
                if stmt.get("node_type") in {"Pass", "Import", "ImportFrom"}:
                    continue
                if stmt.get("node_type") in {"Comment", "DocString"}:
                    code_parts.append(_direct_comment_code(stmt))
                    continue
                result = invoke_lean_backend(stmt, target, check=False, client=client)
                if result.get("result") is False:
                    return result
                code_key = f"lean_{target}"
                if code_key not in result:
                    return {"result": False, "error": f"Missing '{code_key}' in backend response."}
                code_parts.append(_inject_comments_into_lean(stmt, result[code_key]))
            # All imports needed
            preamble = [
                "import PyAstLean",
                "import Libraries",
                "",
                "open PyAstLean",
                "open Libraries",
                "",
            ]
            full_code = "\n".join(preamble) + "\n\n".join(code_parts) if imports_add else "\n\n".join(code_parts)
            return {"result": True, f"lean_{target}": full_code}

        if len(body) == 1:
            result = invoke_lean_backend(body[0], target, client=client)
            if result.get("result") is False:
                return result
            code_key = f"lean_{target}"
            if code_key in result:
                result[code_key] = _inject_comments_into_lean(body[0], result[code_key])
            return result
        return {
            "result": False,
            "error": f"Target '{target}' only supports a single top-level statement; use --target command for full modules.",
        }

    if target == "command" and ast_json.get("node_type") in {"Comment", "DocString"}:
        return {"result": True, f"lean_{target}": _direct_comment_code(ast_json)}

    result = invoke_lean_backend(ast_json, target, client=client)
    if result.get("result") is False:
        return result
    code_key = f"lean_{target}"
    if code_key in result:
        result[code_key] = _inject_comments_into_lean(ast_json, result[code_key])
    return result

def egProgram():
    return """def f(n):
    x = n + 1
    y = x * 2
    x = y - 1
    return x + y
"""


def main(argv=None):
    """CLI entry point that reads a file and forwards its contents to the translator."""
    parser = argparse.ArgumentParser(description="Translate a Python file to Lean.")
    parser.add_argument("file", nargs="?", help="Python source file to translate")
    parser.add_argument("--file", dest="file_option", help=argparse.SUPPRESS)
    parser.add_argument(
        "--target",
        nargs="?",
        default="term",
        help="Lean target string to pass to the translator (default: term)",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output for debugging")
    args = parser.parse_args(argv)
    configure_logging(args.verbose)

    file_path = args.file_option or args.file
    if not file_path:
        parser.error("the following arguments are required: file")

    source_code = Path(file_path).read_text(encoding="utf-8")
    result = translate_to_lean(source_code, args.target, file_path)

    if isinstance(result, dict):
        if result.get("result") is False:
            print(result.get("error", "Translation failed."), file=sys.stderr)
            return 1

        code_key = f"lean_{args.target}"
        if code_key in result:
            logger.info("Successfully translated to Lean target '%s'.", args.target)
            print(result[code_key])
            return 0
    print("Unexpected translation result format.", file=sys.stderr)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
