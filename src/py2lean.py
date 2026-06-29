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
from contract_passta import CONTRACT_FUNCS as PASSTA_STAR_MEMBERS

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

# Backwards-compatible Python module names for the PASSTA contract shim. The Lean library lives
# under `Libraries/passta`, while Python examples may import `contracts` or `contract_passta`.
LIBRARY_IMPORT_ALIASES = {
    "contracts": "passta",
    "contract_passta": "passta",
}

# Type-only / compile-time modules: they contribute nothing at runtime (their names live in
# annotations, which `annotate_python.py` normalises to builtin generics). They are neither
# library-mapped nor real cross-file Lean modules, so they must be dropped entirely.
TYPE_ONLY_IMPORTS = {"typing", "typing_extensions", "__future__"}

# Numeric lowering mode sent to the Lean backend: "exact" → Python float becomes Lean ℚ
# (provable + computable); "approx" → Float (fast, runnable). Set per backend send.
_NUMERIC_MODE = "exact"
# Run-twin suffix (`--mode both`): "'rn" while emitting the runnable twin of a declaration, "" for
# the single-version modes. `_USER_NAMES` lists the user functions/classes whose references the
# backend suffixes in a twin (so `foo'rn` calls `bar'rn`, builds `CNN'rn`).
_RUN_SUFFIX = ""
_USER_NAMES = []

# Submodules of a supported library that act as nested namespaces (e.g. `scipy.special`). Their
# members all flatten into the top-level library's registry, so importing the submodule (e.g.
# `from scipy import special`) binds a *module*-kind name that resolves `special.factorial`.
LIBRARY_SUBMODULES = {
    "scipy": {"special", "constants", "stats", "linalg"},
}


def _supported_library_root(module_name):
    """Top-level package of `module_name` if it (or its root) is a supported library, else None.
    e.g. `scipy.special` -> `scipy`, `numpy` -> `numpy`, `os.path` -> None."""
    if not isinstance(module_name, str) or not module_name:
        return None
    root = module_name.split(".")[0]
    root = LIBRARY_IMPORT_ALIASES.get(root, root)
    return root if root in SUPPORTED_LIBRARY_IMPORTS else None

COMMENT_PLACEHOLDER_RE = re.compile(
    r"^(?P<indent>\s*)(?:let|def)\s+__PastaLean_comment_(?P<id>\d+)\b.*$"
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
                top = module_name.split(".")[0]
                if top in SUPPORTED_LIBRARY_IMPORTS or top in TYPE_ONLY_IMPORTS:
                    continue
                add_import(_lean_module_path(module_name))
        elif node_type == "ImportFrom":
            module_name = stmt.get("module")
            if not isinstance(module_name, str) or not module_name:
                continue
            if (
                _supported_library_root(module_name) is not None
                or module_name.split(".")[0] in TYPE_ONLY_IMPORTS
            ):
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


# Library members whose result is a real (irrational) number — they lower to noncomputable `ℝ`
# in exact mode (mirrors `pythonLibraryMapReal?` on the Lean side). A function that (transitively)
# produces one of these can't stay in `ℚ`, so its floats lower to `ℝ` instead.
REAL_TRANSCENDENTAL_MEMBERS = {
    "math": {"sqrt", "exp", "log", "sin", "cos", "tan", "pi", "e"},
    "numpy": {"exp", "log", "log10", "log2", "sqrt", "std"},
    "scipy": {"pi", "gamma", "gmean", "norm"},
}


def _node_uses_transcendental(node):
    module = node.get("library_module")
    member = node.get("library_member")
    return (
        isinstance(module, str)
        and module in REAL_TRANSCENDENTAL_MEMBERS
        and member in REAL_TRANSCENDENTAL_MEMBERS[module]
    )


def _body_uses_transcendental(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if isinstance(node, dict) and _node_uses_transcendental(node):
                return True
    return False


def _iter_function_defs(module_json):
    """Every `FunctionDef` node anywhere in the module (including class methods and nested defs)."""
    return [
        node
        for node in _walk_json_nodes(module_json)
        if isinstance(node, dict) and node.get("node_type") == "FunctionDef"
    ]


def _func_own_body_nodes(fn):
    """All IR nodes in `fn`'s OWN body — does not descend into nested function bodies."""
    for stmt in fn.get("body", []):
        yield from _walk_json_nodes(stmt, skip_nested_function_bodies=True)


def _callee_name(func):
    """The function/method name a `Call.func` refers to: a plain `Name` id, or an `Attribute`'s
    `attr` (so `self.sigmoid(x)` / `obj.m(x)` resolve to method `sigmoid`/`m` by name)."""
    if isinstance(func, dict):
        if func.get("node_type") == "Name":
            return func.get("id"), 0
        if func.get("node_type") == "Attribute":
            return func.get("attr"), 1  # method: args line up after the implicit `self`
    return None, 0


def _self_field_name(target):
    """If `target` writes to `self.<field>` (possibly through subscripts, e.g. `self.w[i] = …`),
    the field name; else `None`. Mutating an element makes the whole field hold the element type."""
    t = target
    while isinstance(t, dict) and t.get("node_type") == "Subscript":
        t = t.get("value")
    if isinstance(t, dict) and t.get("node_type") == "Attribute":
        owner = t.get("value")
        if isinstance(owner, dict) and owner.get("node_type") == "Name" and owner.get("id") == "self":
            return t.get("attr")
    return None


def _assign_base_name(node):
    """The root variable name an Assign/AnnAssign/AugAssign writes to, plus the `Name` target node
    when the target is a plain `Name`. Follows `Subscript`/`Attribute` chains to the root (so
    `w[0] = …` and `w[0][1] = …` both attribute to `w`), since mutating an element makes the whole
    container hold the element's type."""
    target = node.get("target")
    name_node = target if isinstance(target, dict) and target.get("node_type") == "Name" else None
    while isinstance(target, dict) and target.get("node_type") in ("Subscript", "Attribute"):
        target = target.get("value")
    if isinstance(target, dict) and target.get("node_type") == "Name":
        return target.get("id"), name_node
    return None, None


def annotate_real_flow(module_json):
    """Per-VARIABLE real-number dataflow. Marks (in exact mode) exactly the variables/parameters
    that hold an irrational `ℝ` value, so the Lean backend ascribes `ℝ` only to those slots and
    leaves everything else `ℚ`/`Int` (which stays computable + provable). Lean's `ℚ ↪ ℝ` scalar
    coercion bridges a `ℚ` value flowing into an `ℝ` scalar position (call args, `q + sqrt x`).

    Forward monotone fixpoint over a per-`(function, name)` lattice:
      - a variable assigned an expression that is real → real;
      - a call argument that is real → the callee's matching parameter is real (arg→param);
      - a function whose `return` value is real → "returns real", which makes `y = f(…)` real.
    An expression is real if it contains a transcendental member, references a real var/param, or
    calls a function that returns real.

    Stamps: `_real` on real parameter (`arg`) nodes and real assignment targets; `_real_fn` on any
    function/guard that produces or *handles* an `ℝ` (drives `noncomputable`, decoupled from which
    individual floats are `ℝ`)."""
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return

    functions = {}
    for fn in _iter_function_defs(module_json):
        name = fn.get("name")
        if isinstance(name, str):
            functions[name] = fn  # last def wins on a (rare) name collision

    param_names = {
        name: [
            a.get("arg")
            for a in fn.get("args", {}).get("args", [])
            if isinstance(a, dict)
        ]
        for name, fn in functions.items()
    }
    real_names = {name: set() for name in functions}  # real var/param names, per function
    returns_real = {name: False for name in functions}
    real_fields = set()  # instance fields `self.X` that hold an ℝ value (class-global)

    def expr_is_real(expr, scope):
        for node in _walk_json_nodes(expr, skip_nested_function_bodies=True):
            if not isinstance(node, dict):
                continue
            if _node_uses_transcendental(node):
                return True
            node_type = node.get("node_type")
            if node_type == "Name" and node.get("id") in real_names[scope]:
                return True
            if node_type == "Attribute":
                owner = node.get("value")
                if (
                    isinstance(owner, dict)
                    and owner.get("node_type") == "Name"
                    and owner.get("id") == "self"
                    and node.get("attr") in real_fields
                ):
                    return True
            if node_type == "Call":
                callee, _ = _callee_name(node.get("func"))
                if returns_real.get(callee, False):
                    return True
        return False

    changed = True
    while changed:
        changed = False
        for name, fn in functions.items():
            for node in _func_own_body_nodes(fn):
                node_type = node.get("node_type")
                if node_type in ("Assign", "AnnAssign", "AugAssign"):
                    base_name, _ = _assign_base_name(node)
                    value = node.get("value")
                    if (
                        base_name
                        and value is not None
                        and base_name not in real_names[name]
                        and expr_is_real(value, name)
                    ):
                        real_names[name].add(base_name)
                        changed = True
                    field = _self_field_name(node.get("target"))
                    if (
                        field
                        and field not in real_fields
                        and value is not None
                        and expr_is_real(value, name)
                    ):
                        real_fields.add(field)
                        changed = True
                elif node_type == "Call":
                    callee, self_offset = _callee_name(node.get("func"))
                    if callee in functions:
                        for i, arg in enumerate(node.get("args", [])):
                            pi = i + self_offset  # skip the implicit `self` for method calls
                            if pi >= len(param_names[callee]):
                                break
                            pname = param_names[callee][pi]
                            if (
                                pname
                                and pname not in real_names[callee]
                                and expr_is_real(arg, name)
                            ):
                                real_names[callee].add(pname)
                                changed = True
                    # A list-mutating method `xs.append(v)` / `.extend(v)` / `.insert(i, v)` makes
                    # the receiver hold `v`'s type — so a list built by appending real values is real.
                    func = node.get("func")
                    if (
                        isinstance(func, dict)
                        and func.get("node_type") == "Attribute"
                        and func.get("attr") in ("append", "extend", "insert")
                    ):
                        args = node.get("args", [])
                        if args and expr_is_real(args[-1], name):
                            recv = func.get("value")
                            if isinstance(recv, dict) and recv.get("node_type") == "Name":
                                rn = recv.get("id")
                                if rn and rn not in real_names[name]:
                                    real_names[name].add(rn)
                                    changed = True
                            else:
                                fld = _self_field_name(recv)
                                if fld and fld not in real_fields:
                                    real_fields.add(fld)
                                    changed = True
                elif node_type == "Return":
                    value = node.get("value")
                    if (
                        value is not None
                        and not returns_real[name]
                        and expr_is_real(value, name)
                    ):
                        returns_real[name] = True
                        changed = True

    # Stamp the IR with the converged marks.
    for name, fn in functions.items():
        reals = real_names[name]
        for a in fn.get("args", {}).get("args", []):
            if isinstance(a, dict) and a.get("arg") in reals:
                a["_real"] = True
        for node in _func_own_body_nodes(fn):
            node_type = node.get("node_type")
            if node_type in ("Assign", "AnnAssign", "AugAssign"):
                base_name, target_node = _assign_base_name(node)
                # Stamp EVERY assignment whose root var is real (even a `x = 0.0` whose own RHS
                # isn't real but `x` is real elsewhere), so the RHS is lowered in real-context
                # (literals → `ℝ`, list literals → `List ℝ`); the mutable then infers `ℝ`.
                if base_name in reals or _self_field_name(node.get("target")) in real_fields:
                    node["_real"] = True
                    if target_node is not None:
                        target_node["_real"] = True
            elif node_type == "Return" and returns_real[name]:
                # The function's return type is `ℝ`; lower every `return` value in real-context so a
                # literal-only branch (e.g. `return -1.0, []`) matches an `ℝ`-valued branch.
                node["_real"] = True

    # `_real_fn` (→ `noncomputable`) — a function is noncomputable if it produces or *handles* an ℝ
    # value, OR calls a `_real_fn` function (cascade through void calls too, e.g. `main` → `train`).
    real_fn = {
        name
        for name, fn in functions.items()
        if real_names[name]
        or returns_real[name]
        or any(expr_is_real(stmt, name) for stmt in fn.get("body", []))
    }
    changed = True
    while changed:
        changed = False
        for name, fn in functions.items():
            if name in real_fn:
                continue
            for node in _func_own_body_nodes(fn):
                if node.get("node_type") == "Call":
                    callee, _ = _callee_name(node.get("func"))
                    if callee in real_fn:
                        real_fn.add(name)
                        changed = True
                        break
    for name in real_fn:
        functions[name]["_real_fn"] = True

    # Stamp `_real` on the structure-field declarations of real instance fields (so the Lean
    # `structure` types them `ℝ`), matching the real-context values written into them.
    for node in _walk_json_nodes(module_json):
        if isinstance(node, dict) and node.get("node_type") == "ClassDef":
            for fld in node.get("fields", []):
                if isinstance(fld, dict) and fld.get("name") in real_fields:
                    fld["_real"] = True

    # The `__main__` guard becomes Lean's `def main`; if it calls a noncomputable (`_real_fn`)
    # function, that wrapper must be `noncomputable` too.
    real_fn_names = {name for name, fn in functions.items() if fn.get("_real_fn")}
    for stmt in module_json.get("body", []):
        if isinstance(stmt, dict) and stmt.get("node_type") == "If":
            guard_body = stmt.get("body", [])
            if _body_uses_transcendental(guard_body) or _body_calls_known_functions(
                guard_body, real_fn_names
            ):
                stmt["_real_fn"] = True


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
                root = _supported_library_root(module_name)
                # `import scipy.special as sp` / `import numpy as np`: bind the local name to the
                # top-level library so `sp.factorial` / `np.array` resolve through its registry.
                if root is not None and isinstance(local_name, str):
                    env[local_name] = {"kind": "module", "module": root}
            continue
        if node_type == "ImportFrom":
            module_name = stmt.get("module")
            root = _supported_library_root(module_name)
            if root is not None:
                is_submodule_path = isinstance(module_name, str) and "." in module_name
                for alias_node in stmt.get("names", []):
                    if not isinstance(alias_node, dict):
                        continue
                    member_name = alias_node.get("name")
                    local_name = _imported_alias_name(alias_node)
                    if root == "passta" and member_name == "*":
                        for contract_member in PASSTA_STAR_MEMBERS:
                            env[contract_member] = {
                                "kind": "member",
                                "module": root,
                                "member": contract_member,
                            }
                        continue
                    if isinstance(member_name, str) and isinstance(local_name, str):
                        # `from scipy import special` binds a submodule namespace; `from
                        # scipy.special import factorial` (and `from math import exp`) bind members.
                        if not is_submodule_path and member_name in LIBRARY_SUBMODULES.get(root, set()):
                            env[local_name] = {"kind": "module", "module": root}
                            continue
                        env[local_name] = {
                            "kind": "member",
                            "module": root,
                            "member": member_name,
                        }
            continue

        _annotate_library_refs_in_expr(stmt, env)

        if node_type == "ClassDef":
            # Class methods are FunctionDefs under "methods"; annotate library refs in each body.
            for method in stmt.get("methods", []):
                if not isinstance(method, dict):
                    continue
                child_env = dict(env)
                for arg_name in _function_arg_names(method):
                    child_env.pop(arg_name, None)
                _annotate_library_imports_in_scope(method.get("body", []), child_env)
        elif node_type == "FunctionDef":
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


def _is_name(node, name=None):
    return (isinstance(node, dict) and node.get("node_type") == "Name"
            and (name is None or node.get("id") == name))


def _name_referenced(nodes, name):
    """Does `name` appear as a `Name` load anywhere within `nodes`?"""
    stack = list(nodes)
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("node_type") == "Name" and n.get("id") == name:
                return True
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return False


def _is_const_one(node):
    return isinstance(node, dict) and node.get("node_type") == "Constant" and node.get("value") == 1


def _is_incr_by_one(stmt, var):
    """True if `stmt` increments `var` by 1, as `var += 1` or `var = var + 1`."""
    if not isinstance(stmt, dict):
        return False
    if stmt.get("node_type") == "AugAssign":
        return (_is_name(stmt.get("target"), var) and stmt.get("op") == "add"
                and _is_const_one(stmt.get("value")))
    if stmt.get("node_type") == "Assign" and _is_name(stmt.get("target"), var):
        v = stmt.get("value")
        if isinstance(v, dict) and v.get("node_type") == "BinOp" and v.get("op") == "add":
            l, r = v.get("left"), v.get("right")
            return (_is_name(l, var) and _is_const_one(r)) or (_is_const_one(l) and _is_name(r, var))
    return False


def _counting_while_match(stmt):
    """`(loop_var, stop_node)` for a canonical `while i < bound: …; i += 1` (or `i <= bound`, or
    `i = i + 1`), else `None`. For `<=`, the `range` stop is `bound + 1`."""
    if not (isinstance(stmt, dict) and stmt.get("node_type") == "While"):
        return None
    test = stmt.get("test")
    if not (isinstance(test, dict) and test.get("node_type") == "Compare" and test.get("op") in ("lt", "le")):
        return None
    if not _is_name(test.get("left")):
        return None
    loop_var = test["left"]["id"]
    body = stmt.get("body", [])
    if not body or not _is_incr_by_one(body[-1], loop_var):
        return None
    bound = test["right"]
    if test["op"] == "le":
        bound = {"node_type": "BinOp", "op": "add", "left": bound,
                 "right": {"node_type": "Constant", "value": 1}}
    return loop_var, bound


def _normalize_counting_loops_in_block(body):
    """Rewrite a canonical counting `while i < bound: …; i += 1` (with a preceding `i = 0` in the
    same block, and `i` unused after the loop) into `for i in range(bound): …`, so the verification
    path handles it via the well-supported `for`/`forIn` machinery rather than mvcgen's fragile
    `while`. Recurses into nested blocks first. Semantics-preserving only under those guards (a `for`
    leaves `i = bound-1`, a `while` leaves `i = bound`), so we bail if any guard fails."""
    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        for key in ("body", "orelse", "finalbody"):
            if isinstance(stmt.get(key), list):
                _normalize_counting_loops_in_block(stmt[key])
        for handler in stmt.get("handlers", []) or []:
            if isinstance(handler, dict):
                _normalize_counting_loops_in_block(handler.get("body", []))
        for method in stmt.get("methods", []) or []:
            if isinstance(method, dict):
                _normalize_counting_loops_in_block(method.get("body", []))
    i = 0
    while i < len(body):
        match = _counting_while_match(body[i])
        if match:
            loop_var, bound = match
            init_idx, start_node = None, None
            for j in range(i - 1, -1, -1):
                s = body[j]
                if not isinstance(s, dict):
                    continue
                if (s.get("node_type") == "Assign" and _is_name(s.get("target"), loop_var)
                        and isinstance(s.get("value"), dict) and s["value"].get("node_type") == "Constant"
                        and isinstance(s["value"].get("value"), int)):
                    init_idx, start_node = j, s["value"]
                    break
                if s.get("node_type") in ("Assign", "AugAssign") and _is_name(s.get("target"), loop_var):
                    break  # `i` re-bound to something else first → not the canonical pattern
            if init_idx is not None and not _name_referenced(body[i + 1:], loop_var):
                stmt = body[i]
                new_body = stmt["body"][:-1]  # drop the `i += 1`
                # `range(stop)` when the counter starts at 0, else `range(start, stop)`.
                args = [bound] if start_node.get("value") == 0 else [start_node, bound]
                stmt.clear()
                stmt.update({
                    "node_type": "For",
                    "target": {"node_type": "Name", "id": loop_var},
                    "iter": {"node_type": "Range", "func": {"node_type": "Name", "id": "range"},
                             "args": args, "keywords": {}},
                    "body": new_body,
                    "orelse": [],
                })
                del body[init_idx]
                i -= 1
        i += 1


def normalize_counting_loops(module_json):
    if isinstance(module_json, dict) and isinstance(module_json.get("body"), list):
        _normalize_counting_loops_in_block(module_json["body"])


def translate_to_json(source_code, filepath=None, best_effort=False):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.

    When `best_effort` is set, unsupported statements (foreign libraries, unhandled syntax) are
    replaced by `pyUnsupported(...)` placeholders instead of aborting; dropped lines are logged
    to stderr.
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
    module_dir = str(Path(filepath).resolve().parent) if filepath else None
    translator = ASTToJsonLeanVisitor(
        source_code,
        best_effort=best_effort,
        supported_modules=set(SUPPORTED_LIBRARY_IMPORTS) | set(LIBRARY_IMPORT_ALIASES),
        type_only_modules=TYPE_ONLY_IMPORTS,
        module_dir=module_dir,
    )
    data = translator.visit(ast_tree)
    if best_effort and translator.unsupported_log:
        logger.warning(
            "best-effort: replaced %d unsupported statement(s) with pyUnsupported placeholders:",
            len(translator.unsupported_log),
        )
        for src in translator.unsupported_log:
            logger.warning("  unsupported: %s", src)
    normalize_counting_loops(data)
    annotate_library_imports(data)
    annotate_exception_effects(data)
    annotate_io_effects(data)
    annotate_real_flow(data)
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

        PastaLean_dir = self.cwd / "PastaLean"
        if PastaLean_dir.exists():
            yield from PastaLean_dir.rglob("*.lean")
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
            {"task": "translate", "ast": ast_json, "target": target, "check": check,
             "numericMode": _NUMERIC_MODE, "runSuffix": _RUN_SUFFIX,
             "userNames": _USER_NAMES},
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
            {"task": "translate", "ast": ast_json, "target": target, "check": check,
             "numericMode": _NUMERIC_MODE, "runSuffix": _RUN_SUFFIX,
             "userNames": _USER_NAMES},
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

    def prove_file(self, code, timeout=600.0):
        """Elaborate an assembled generated file in the WARM backend so `taste?` searches each
        assert; return the parsed JSON carrying the ordered list of winning tactic strings
        (`winners`). Uses a long timeout because this elaborates the whole program — unlike
        `request`'s 5s budget, which a `nlinarith`/`grind` search would blow past."""
        self.start()
        assert self.proc is not None and self.proc.stdin is not None and self.proc.stdout is not None
        json_task = json.dumps({"task": "proveFile", "code": code}, separators=(",", ":"))
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return None
        ready, _, _ = select.select([self.proc.stdout], [], [], timeout)
        if not ready:
            logger.debug("proveFile timed out after %ss; leaving taste? in place.", timeout)
            return None
        line = self.proc.stdout.readline()
        if not line:
            self.close()
            return None
        try:
            return json.loads(line.strip())
        except json.JSONDecodeError as err:
            logger.debug("proveFile returned invalid JSON: %s", err)
            return None

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


def _splice_taste_winners(code, winners):
    """Replace each `taste?` proof obligation in `code` with its winning tactic, matched by *byte
    offset*: `winners` is a list of ``{"pos": <byte offset into code>, "proof": <tactic>}``. Matching
    by position (not append order) is essential — a `mvcgen … with taste?` whose VCs `mvcgen` itself
    discharged records NO winner, so order-based zipping would shift every later token onto the wrong
    proof. A token with a matching winner gets it (prettified); a `with taste?` with no winner is a
    self-closed `mvcgen` → drop the dead `with` clause; any other unmatched `taste?` → `sorry`.

    Comment/string aware: `taste?` ALSO shows up inside docstrings/comments (e.g. ``:= by taste?`` in
    prose), which aren't elaborated and have no winner. Those never match a `pos`, so they're left
    untouched — we only substitute `taste?` in actual code (outside `--` line comments, nestable
    `/- -/` block comments, and `"..."` string literals)."""
    by_pos = {w["pos"]: w["proof"] for w in winners if isinstance(w, dict) and "pos" in w}
    out = []
    i, n = 0, len(code)
    in_line_comment = False
    block_depth = 0
    in_string = False
    while i < n:
        two = code[i:i + 2]
        c = code[i]
        if in_line_comment:
            out.append(c); i += 1
            if c == "\n":
                in_line_comment = False
            continue
        if block_depth > 0:
            if two == "/-":
                block_depth += 1; out.append(two); i += 2; continue
            if two == "-/":
                block_depth -= 1; out.append(two); i += 2; continue
            out.append(c); i += 1; continue
        if in_string:
            if c == "\\" and i + 1 < n:
                out.append(code[i:i + 2]); i += 2; continue
            if c == '"':
                in_string = False
            out.append(c); i += 1; continue
        # normal code context
        if two == "--":
            in_line_comment = True; out.append(two); i += 2; continue
        if two == "/-":
            block_depth = 1; out.append(two); i += 2; continue
        if c == '"':
            in_string = True; out.append(c); i += 1; continue
        if code.startswith("taste?", i):
            # Byte offset of this token into `code` (the winners' `pos` is byte-based, UTF-8).
            off = len(code[:i].encode("utf-8"))
            if off in by_pos:
                proof = by_pos[off]
                if proof.strip():
                    # The recorded `c₁; c₂; …` sequence — drop it in verbatim (no `first`, no merge).
                    out.append(proof)
                else:
                    # Empty proof: `mvcgen` discharged every VC, so the trailing `taste?` ran on no
                    # goals. Prune the dangling `taste?` line for a clean `mvcgen [...]`.
                    while out and out[-1].strip() == "":
                        out.pop()
            else:
                # Unmatched `taste?` (e.g. inside prose, or no recorded proof) → keep it compiling.
                out.append("sorry")
            i += len("taste?")
            continue
        out.append(c); i += 1
    return "".join(out)

def _newline_before_mvcgen_with(code):
    """Put a contract spec's `mvcgen … invariants` closer on its own line: the pretty-printer glues
    `with <closer>` straight onto the last `⌜…⌝` invariant bullet (rendering `…⌝with taste?`), which
    reads poorly. Break before `with` and align it under `mvcgen` (two spaces). Only the spec
    theorems emit `⌝` immediately followed by `with`, so this can't touch anything else."""
    return re.sub(r"⌝[^\S\n]*with\b", "⌝\n  with", code)


def _references_name(node, target):
    """Recursively check whether a JSON subtree references a `Name` with id `target`."""
    if isinstance(node, dict):
        if node.get("node_type") == "Name" and node.get("id") == target:
            return True
        return any(_references_name(v, target) for v in node.values())
    if isinstance(node, list):
        return any(_references_name(x, target) for x in node)
    return False


def _mutual_recursion_groups(body):
    """Map each top-level function name to its mutual-recursion group (a strongly-connected
    component of the call graph). Singletons are self- or non-recursive; groups of size >= 2 are
    mutually recursive and must be emitted together inside a Lean `mutual … end` block.

    The backend translates one top-level statement at a time, so it never sees two functions
    together; this whole-module analysis lives here and drives sending a group as one `Module`."""
    funcs = [
        (s.get("name"), s)
        for s in body
        if isinstance(s, dict) and s.get("node_type") == "FunctionDef" and isinstance(s.get("name"), str)
    ]
    names = [n for n, _ in funcs]
    reach = {n: {m for m in names if _references_name(b, m)} for n, b in funcs}
    # Transitive closure of "references".
    changed = True
    while changed:
        changed = False
        for n in names:
            for r in list(reach[n]):
                extra = reach.get(r, set()) - reach[n]
                if extra:
                    reach[n] |= extra
                    changed = True
    # SCC of n = every m that n reaches and that reaches n back.
    return {
        n: frozenset([n] + [m for m in reach[n] if m != n and n in reach.get(m, set())])
        for n in names
    }


def _collect_class_table(body):
    """Build {class_name: {methods, mutators, fields, bases}} from the module's ClassDefs, folding
    a single base class's members into each subclass (so inherited methods dispatch correctly)."""
    table = {}
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            table[s["name"]] = {
                "methods": set(m.get("name") for m in s.get("methods", [])),
                "mutators": set(s.get("mutators", [])),
                "fields": set(f.get("name") for f in s.get("fields", [])),
                "statics": set(s.get("staticmethods", [])) | set(s.get("classmethods", [])),
                "bases": [b.get("id") for b in s.get("bases", []) if isinstance(b, dict)],
            }
    for info in table.values():
        for base in info["bases"]:
            if base in table:
                info["methods"] |= table[base]["methods"]
                info["mutators"] |= table[base]["mutators"]
                info["fields"] |= table[base]["fields"]
    return table


def _prune_inherited_fields(body):
    """Drop a subclass ClassDef's fields that are already declared by its base, so the emitted Lean
    `structure Sub extends Base` does not redeclare an inherited field (which Lean rejects)."""
    own = {}
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            own[s["name"]] = {f.get("name") for f in s.get("fields", [])}
            own[s["name"]] |= set()  # ensure a set even with no fields
    # Transitive base-field set per class (single inheritance).
    bases = {
        s["name"]: [b.get("id") for b in s.get("bases", []) if isinstance(b, dict)]
        for s in body
        if isinstance(s, dict) and s.get("node_type") == "ClassDef"
    }
    def base_fields(name, seen=None):
        seen = seen or set()
        acc = set()
        for base in bases.get(name, []):
            if base in own and base not in seen:
                seen.add(base)
                acc |= own[base] | base_fields(base, seen)
        return acc
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            inherited = base_fields(s["name"])
            if inherited:
                s["fields"] = [f for f in s.get("fields", []) if f.get("name") not in inherited]


def _method_owner_index(table):
    """Map a method name to its class when exactly one class declares it (ambiguous names omitted).
    Used to resolve a method-call receiver's class when its variable type is otherwise unknown."""
    owners = {}
    for cname, info in table.items():
        for m in info["methods"]:
            owners.setdefault(m, set()).add(cname)
    return {m: next(iter(cs)) for m, cs in owners.items() if len(cs) == 1}


def _stamp_class_dispatch(ast_json):
    """Annotate Call nodes with class-dispatch hints so the Lean backend (which sees one statement
    at a time, with no shared state) can lower them deterministically:
      * instantiation `C(..)`  -> `_class_ctor: "C"`
      * method call `obj.m(..)` -> `_receiver_class: "C"`, `_is_mutator: bool`
    Receiver class is resolved from `self` (the enclosing class), tracked `x = C(..)` bindings,
    typed parameters, or a method name unique to one class."""
    if ast_json.get("node_type") != "Module":
        return ast_json
    body = ast_json.get("body", [])
    table = _collect_class_table(body)
    if not table:
        return ast_json
    _prune_inherited_fields(body)
    owners = _method_owner_index(table)

    def ctor_class_of(func, current_class):
        if isinstance(func, dict) and func.get("node_type") == "Name":
            fid = func.get("id")
            if fid in table:
                return fid
            if fid == "cls" and current_class:
                return current_class
        return None

    def receiver_class_of(recv, scope, current_class, method):
        if isinstance(recv, dict) and recv.get("node_type") == "Name":
            rid = recv.get("id")
            if rid == "self" and current_class:
                return current_class
            if rid in scope:
                return scope[rid]
        if method in owners:
            return owners[method]
        return None

    def walk_expr(node, scope, current_class):
        """Stamp Calls anywhere inside an expression (scope is read-only here)."""
        if isinstance(node, list):
            for x in node:
                walk_expr(x, scope, current_class)
            return
        if not isinstance(node, dict):
            return
        if node.get("node_type") == "Call":
            func = node.get("func")
            cls = ctor_class_of(func, current_class)
            if cls is not None:
                node["_class_ctor"] = cls
            elif isinstance(func, dict) and func.get("node_type") == "Attribute":
                method = func.get("attr")
                recv = func.get("value")
                # `ClassName.method(...)` (static, classmethod, or an unbound call passing an
                # explicit instance) calls `C.method` directly without prepending a receiver.
                if (isinstance(recv, dict) and recv.get("node_type") == "Name"
                        and recv.get("id") in table
                        and method in table[recv["id"]]["methods"]):
                    node["_static_class"] = recv["id"]
                else:
                    rcls = receiver_class_of(recv, scope, current_class, method)
                    if rcls is not None and method in table.get(rcls, {}).get("methods", set()):
                        node["_receiver_class"] = rcls
                        node["_is_mutator"] = method in table[rcls]["mutators"]
        for v in node.values():
            walk_expr(v, scope, current_class)

    def param_scope(funcdef):
        """Seed a function scope with parameters whose annotation names a known class."""
        sc = {}
        args = (funcdef.get("args") or {}).get("args", [])
        for a in args:
            ann = a.get("annotation")
            if isinstance(ann, dict) and ann.get("node_type") == "Name" and ann.get("id") in table:
                sc[a.get("arg")] = ann["id"]
        return sc

    def walk_stmts(stmts, scope, current_class):
        for stmt in stmts:
            if not isinstance(stmt, dict):
                continue
            nt = stmt.get("node_type")
            if nt == "ClassDef":
                cname = stmt.get("name")
                for m in stmt.get("methods", []):
                    msc = param_scope(m)
                    walk_stmts(m.get("body", []), msc, cname)
                continue
            if nt in ("FunctionDef", "AsyncFunctionDef"):
                walk_stmts(stmt.get("body", []), param_scope(stmt), current_class)
                continue
            # Stamp every expression in the statement, then learn `x = C(..)` bindings.
            walk_expr(stmt, scope, current_class)
            if nt == "Assign":
                target = stmt.get("target")
                value = stmt.get("value")
                if (isinstance(target, dict) and target.get("node_type") == "Name"
                        and isinstance(value, dict) and value.get("node_type") == "Call"):
                    cls = ctor_class_of(value.get("func"), current_class)
                    if cls is not None:
                        scope[target["id"]] = cls
            # Recurse into compound-statement blocks (their bodies share this scope).
            for block_attr in ("body", "orelse", "finalbody"):
                blk = stmt.get(block_attr)
                if isinstance(blk, list):
                    walk_stmts(blk, scope, current_class)
            for handler in stmt.get("handlers", []) or []:
                if isinstance(handler, dict):
                    walk_stmts(handler.get("body", []), scope, current_class)

    walk_stmts(body, {}, None)
    return ast_json


def _lean_ident(name):
    """A safe Lean identifier from a Python name, or None if unusable."""
    return name if isinstance(name, str) and name.isidentifier() else None


def _backend_placeholder_command(stmt, idx):
    """Best-effort placeholder for a top-level statement the *Lean backend* could not translate
    (e.g. a `with` statement, which `node_visitor` emits IR for but the backend has no generator
    for, so it slips past the node-level fallback). Keeps the declaration's name where possible so
    references still resolve; the linter flags the `pyUnsupported` use."""
    node_type = stmt.get("node_type", "statement") if isinstance(stmt, dict) else "statement"
    name = stmt.get("name") if isinstance(stmt, dict) else None
    msg = f"unsupported {node_type} (backend could not translate)"
    # The main entry-point body (`main'`) is awaited by the `main` wrapper, so it must stay a
    # runnable `IO Unit` — a `pyUnsupported` *value* there would dangle the wrapper's reference.
    if name in ("main", "main'"):
        return f'def {name} : IO Unit := do\n  let _ := pyUnsupported "{msg}"\n  pure ()'
    ident = _lean_ident(name) or f"__py_unsup_backend_{idx}"
    return f'def {ident} := pyUnsupported "{msg}"'


def _collect_user_names(body):
    """The user's module-scope function/class names — references to these get the `'rn` suffix in a
    run-twin (so `foo'rn` calls `bar'rn`, builds `CNN'rn`). NESTED functions (`def` inside `def`) are
    emitted as local `let` bindings regenerated in each twin, so their names must NOT be suffixed."""
    names = set()

    def walk(node):
        if isinstance(node, dict):
            nt = node.get("node_type")
            if nt in ("FunctionDef", "ClassDef"):
                n = node.get("name")
                if isinstance(n, str):
                    names.add(n)
                return  # a def/class boundary: its own body is a separate scope (nested = local)
            if nt in ("AsyncFunctionDef", "Lambda"):
                return
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for it in node:
                walk(it)

    for stmt in body:
        walk(stmt)
    return sorted(names)


def translate_to_lean(source_code, target="term", filepath = None, imports_add = True, best_effort=False, mode="both", prove_asserts=True):
    """Translate Python source to Lean via JSON IR and the Lean backend executable.

    `mode` selects the numeric semantics: "prove" (exact ℚ/ℝ, provable), "run" (Float, runnable), or
    "both" (default) — emit the provable version AND a runnable twin whose top-level defs/classes and
    the entry point are suffixed `'rn`, adjacently."""
    global _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES
    _NUMERIC_MODE = "approx" if mode == "run" else "exact"
    _RUN_SUFFIX, _USER_NAMES = "", []
    json_ir = translate_to_json(source_code, filepath, best_effort=best_effort)
    ast_json = json.loads(json_ir)
    _stamp_class_dispatch(ast_json)
    client = _LEAN_BACKEND

    if ast_json.get("node_type") == "Module":
        body = ast_json.get("body", [])
        user_names = _collect_user_names(body)
        code_key = f"lean_{target}"
        single = "approx" if mode == "run" else "exact"

        def node_passes(node):
            """Emission passes for one top-level node: (numericMode, runSuffix, userNames). In `both`
            mode only definitions/classes and the `__main__` guard get a runnable `'rn` twin (their
            names are suffixed); top-level constants/`del`/statements emit once (an unsuffixed twin
            would just redeclare the same global)."""
            nt = node.get("node_type")
            twinnable = nt in ("FunctionDef", "ClassDef", "Module") or (nt == "If" and node.get("is_main_guard"))
            if mode == "both" and twinnable:
                return [("exact", "", []), ("approx", "'rn", user_names)]
            return [(single, "", [])]

        def send_node(node):
            """Send `node` once per pass; return the list of code strings, or None on failure."""
            global _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES
            codes = []
            for nmode, suffix, unames in node_passes(node):
                _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES = nmode, suffix, unames
                r = invoke_lean_backend(node, target, check=False, client=client)
                if r.get("result") is False or code_key not in r:
                    return None
                codes.append(r[code_key])
            return codes

        if target == "command":
            # Each part is (is_comment, text). Standalone comments attach to the next
            # part with a single newline so they read as leading comments, while real
            # declarations are separated by a blank line.
            code_parts = []
            mutual_groups = _mutual_recursion_groups(body)
            emitted_funcs = set()
            backend_unsup = 0
            for stmt in body:
                # A top-level Python `pass` is a true no-op, so there is no Lean command to emit.
                if stmt.get("node_type") in {"Pass", "Import", "ImportFrom"}:
                    continue
                if stmt.get("node_type") in {"Comment", "DocString"}:
                    code_parts.append((True, _direct_comment_code(stmt)))
                    continue
                # Mutually-recursive functions can't be separate `def`s — send the whole group as a
                # single `Module` so the backend emits one `mutual … end` block.
                if stmt.get("node_type") == "FunctionDef":
                    name = stmt.get("name")
                    if name in emitted_funcs:
                        continue
                    group = mutual_groups.get(name, frozenset([name]))
                    if len(group) >= 2:
                        members = [
                            s for s in body
                            if isinstance(s, dict) and s.get("node_type") == "FunctionDef"
                            and s.get("name") in group
                        ]
                        module_node = {"node_type": "Module", "body": members}
                        codes = send_node(module_node)
                        if codes is None:
                            if best_effort:
                                logger.warning("best-effort: backend could not translate %s; replaced with pyUnsupported placeholder", name)
                                code_parts.append((False, _backend_placeholder_command(stmt, backend_unsup)))
                                backend_unsup += 1
                                emitted_funcs.update(group)
                                continue
                            return {"result": False, "error": f"backend could not translate {name}"}
                        for c in codes:
                            code_parts.append((False, c))
                        emitted_funcs.update(group)
                        continue
                codes = send_node(stmt)
                if codes is None:
                    if best_effort:
                        logger.warning("best-effort: backend could not translate a %s; replaced with pyUnsupported placeholder", stmt.get("node_type"))
                        code_parts.append((False, _backend_placeholder_command(stmt, backend_unsup)))
                        backend_unsup += 1
                        continue
                    return {"result": False, "error": f"backend could not translate {stmt.get('node_type')}"}
                # Inline comment placeholders live inside each emitted version, so inject into the
                # prove version AND every `'rn` twin.
                for c in codes:
                    code_parts.append((False, _inject_comments_into_lean(stmt, c)))

            body_code = _join_command_parts(code_parts)
            if imports_add:
                # Every `import` must precede the first command in a Lean file. We list the
                # runtime imports, then the user's cross-file modules, then the `open`s.
                crossfile_imports = _crossfile_import_lines(body)
                preamble_lines = [
                    "import PastaLean",
                    "import Libraries",
                    "import Std.Tactic.Do",
                    *crossfile_imports,
                    "",
                    "open PastaLean",
                    "open Libraries",
                    "open Std.Do",
                    "",
                    "set_option linter.all false", # shut up warnings which annoyingly popup in output
                    "set_option mvcgen.warning false",
                    "\n"
                    "set_option maxHeartbeats 800000",
                    "\n",
                ]
                full_code = "\n".join(preamble_lines) + body_code
            else:
                full_code = body_code
            # Lay an `mvcgen … invariants` spec's `with` closer on its own line (cosmetic), for both
            # the spliced and the `--leave-taste` forms.
            full_code = _newline_before_mvcgen_with(full_code)
            # Prove-and-replace pass: elaborate the assembled file in the warm backend so `taste?`
            # searches each assert, then splice the concrete winning tactic (or `sorry`) over each
            # `taste?`. Non-destructive — on any failure we leave the `taste?` obligations in place.
            if prove_asserts and "taste?" in full_code:
                resp = client.prove_file(full_code)
                if resp and resp.get("result") and isinstance(resp.get("winners"), list):
                    full_code = _splice_taste_winners(full_code, resp["winners"])
                    if resp.get("hasErrors"):
                        logger.warning("proveFile reported elaboration errors; some asserts may be left `sorry`.")
                else:
                    logger.warning("proveFile pass unavailable/failed; leaving `taste?` obligations in place.")
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
        default="command",
        help="Lean target string to pass to the translator (default: target)",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output for debugging")
    parser.add_argument(
        "--strict",
        dest="strict",
        action="store_true",
        help="Disable the best-effort fallback (which is ON by default): fail hard on "
             "unsupported constructs (foreign libraries, unhandled syntax) instead of emitting "
             "pyUnsupported(...) placeholders.",
    )
    parser.add_argument(
        "--mode",
        dest="mode",
        choices=["prove", "run", "both"],
        default="both",
        help="Which numeric semantics to emit. 'prove': exact ℚ/ℝ (provable; transcendentals "
             "noncomputable). 'run': Float (fast, runnable). 'both' (default): emit BOTH in one file "
             "— the provable version under its name and a runnable twin suffixed 'rn "
             "(e.g. `main'rn`, `sigmoid'rn`).",
    )
    parser.add_argument(
        "--prove-asserts",
        dest="prove_asserts",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Run the prove-and-replace pass on each assert: elaborate in the warm backend and "
             "splice the concrete winning tactic — or `sorry` — over each `:= by taste?`. Default: "
             "on. Use --no-prove-asserts to leave the obligations as `:= by taste?`.",
    )
    args = parser.parse_args(argv)
    configure_logging(args.verbose)

    file_path = args.file_option or args.file
    if not file_path:
        parser.error("the following arguments are required: file")

    source_code = Path(file_path).read_text(encoding="utf-8")
    result = translate_to_lean(source_code, args.target, file_path, best_effort=not args.strict,
                               mode=args.mode, prove_asserts=args.prove_asserts)

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
