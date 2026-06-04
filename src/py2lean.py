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
from toplevel_state import (
    annotate_main_entrypoint,
    annotate_toplevel_state,
    annotate_if_assigned_names,
)

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


def _join_command_parts(parts):
    """Join generated top-level parts, attaching leading comments to the next part.

    `parts` is a list of `(is_comment, text)`. A comment is followed by a single newline
    so it sits directly above the next declaration; declarations are separated by a blank
    line. This avoids a stray blank line after every comment.
    """
    out = ""
    for is_comment, text in parts:
        if not text:
            continue
        if not out:
            out = text
        elif out.endswith("\n"):
            # Previous part was a comment: glue this part directly beneath it.
            out += text
        else:
            out += "\n\n" + text
        if is_comment:
            out += "\n"
    return out


def _lean_module_path(python_module):
    """Map a dotted Python module path to a Lean module path.

    Lean requires each component of a module path to start uppercase (this is how Lean
    resolves `import` to a file and is enforced by Mathlib's linter). We capitalize the
    first letter of every dotted segment and leave the rest — including underscores —
    intact, so the mapping is deterministic and reversible:
        `mymodule`         -> `Mymodule`
        `pkg.sub_pkg.mod`  -> `Pkg.Sub_pkg.Mod`
    Both the importing and the defining file compute this identically, which matters
    because we translate one file at a time and never see the other.
    """
    segments = [seg for seg in python_module.split(".") if seg]
    capitalized = [seg[:1].upper() + seg[1:] for seg in segments]
    return ".".join(capitalized)


def _crossfile_import_lines(body):
    """Build the Lean `import` lines for non-library cross-file imports.

    Library imports (`math`, `numpy`, ...) are handled by symbol mapping and skipped here.
    Both `import a.b` and `from a.b import f, g` become `import A.B`: a translated module
    emits its definitions at the top level (not inside a per-file namespace), and Lean
    makes a module's top-level definitions globally available after `import` — so no `open`
    is needed and the imported names are already unqualified, matching Python's
    `from ... import`. Private (`_`-prefixed) definitions stay non-importable.

    Imports must appear at the very top of a Lean file, so these lines are assembled into
    the preamble rather than emitted per-statement by the backend.
    """
    import_lines = []
    seen_imports = set()

    def add_import(lean_path):
        if lean_path and lean_path not in seen_imports:
            seen_imports.add(lean_path)
            import_lines.append(f"import {lean_path}")

    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        node_type = stmt.get("node_type")
        if node_type == "Import":
            for alias_node in stmt.get("names", []):
                if not isinstance(alias_node, dict):
                    continue
                module_name = alias_node.get("name")
                if not isinstance(module_name, str):
                    continue
                # `import math` etc. is library-mapped, not a cross-file Lean import.
                if module_name.split(".")[0] in SUPPORTED_LIBRARY_IMPORTS:
                    continue
                add_import(_lean_module_path(module_name))
        elif node_type == "ImportFrom":
            module_name = stmt.get("module")
            if not isinstance(module_name, str) or not module_name:
                continue
            if module_name in SUPPORTED_LIBRARY_IMPORTS:
                continue
            add_import(_lean_module_path(module_name))

    return import_lines


def _collect_scope_function_defs(body):
    """Collect the `FunctionDef` nodes that live in a single Python scope.

    A `def` nested inside an `if`/`for`/`while`/`try`/`with` block is still in the *same*
    scope (those compound statements do not introduce a scope in Python), so effect analysis
    must see it — e.g. the harness wraps bare top-level code under `if __name__ == "__main__":`,
    which nests the program's functions one level deep. We descend through compound statements
    but stop at scope boundaries (`FunctionDef`/`AsyncFunctionDef`/`ClassDef`/`Lambda`), whose
    own bodies form separate scopes handled by recursion.
    """
    found = []

    def walk(node):
        if isinstance(node, dict):
            node_type = node.get("node_type")
            if node_type == "FunctionDef":
                found.append(node)
                return  # separate scope: do not descend into its body
            if node_type in {"AsyncFunctionDef", "ClassDef", "Lambda"}:
                return  # separate scopes, not handled by this collector
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    for stmt in body:
        walk(stmt)
    return found


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
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
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
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
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


def _sanitize_hole_identifiers(ast_tree):
    """Rename Python variables whose name is a single underscore when they are *read*.

    Python allows `_` as an ordinary identifier (e.g. `for _ in xs: a = int(_)`), but Lean
    treats a bare `_` as a placeholder/hole, so a read of it elaborates to a metavariable
    rather than the bound value. When `_` is only ever a throwaway binder (`for _ in range(n)`,
    `fun _ => ...`) emitting `_` is correct and idiomatic, so we leave those alone and only
    rewrite when `_` actually appears in a load position somewhere in the module.
    """
    reads_underscore = any(
        isinstance(n, ast.Name) and n.id == "_" and isinstance(n.ctx, ast.Load)
        for n in ast.walk(ast_tree)
    )
    if not reads_underscore:
        return
    safe = "__py_us"
    for n in ast.walk(ast_tree):
        if isinstance(n, ast.Name) and n.id == "_":
            n.id = safe
        elif isinstance(n, ast.arg) and n.arg == "_":
            n.arg = safe


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
    _sanitize_hole_identifiers(ast_tree)
    logger.debug("Parsed Python AST:\n%s", ast.dump(ast_tree, indent=4))
    translator = ASTToJsonLeanVisitor(source_code)
    data = translator.visit(ast_tree)
    annotate_library_imports(data)
    annotate_exception_effects(data)
    annotate_io_effects(data)
    annotate_main_entrypoint(data)
    annotate_toplevel_state(data)
    annotate_if_assigned_names(data)
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
            # Each part is (is_comment, text). Standalone comments attach to the next
            # part with a single newline so they read as leading comments, while real
            # declarations are separated by a blank line.
            code_parts = []
            for stmt in body:
                # A top-level Python `pass` is a true no-op, so there is no Lean command to emit.
                if stmt.get("node_type") in {"Pass", "Import", "ImportFrom"}:
                    continue
                if stmt.get("node_type") in {"Comment", "DocString"}:
                    code_parts.append((True, _direct_comment_code(stmt)))
                    continue
                result = invoke_lean_backend(stmt, target, check=False, client=client)
                if result.get("result") is False:
                    return result
                code_key = f"lean_{target}"
                if code_key not in result:
                    return {"result": False, "error": f"Missing '{code_key}' in backend response."}
                code_parts.append((False, _inject_comments_into_lean(stmt, result[code_key])))

            body_code = _join_command_parts(code_parts)
            if imports_add:
                # Every `import` must precede the first command in a Lean file. We list the
                # runtime imports, then the user's cross-file modules, then the `open`s.
                crossfile_imports = _crossfile_import_lines(body)
                preamble_lines = [
                    "import PyAstLean",
                    "import Libraries",
                    *crossfile_imports,
                    "",
                    "open PyAstLean",
                    "open Libraries",
                    "",
                ]
                full_code = "\n".join(preamble_lines) + body_code
            else:
                full_code = body_code
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
