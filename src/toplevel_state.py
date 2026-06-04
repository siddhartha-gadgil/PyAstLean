"""Top-level state threading and the `main`/`main'` entry-point rename.

Lean has no top-level statement execution: a bare `if`/`for`/`while`/`match` at module
scope cannot mutate a module global the way Python does. We instead treat each such
top-level block as a *state transformer* over the names it mutates — this module performs
the source-level analysis (write-sets, SSA-style versioning of re-initialized names, and
the `main`/`main'` collision rename) and annotates the JSON IR. The Lean backend reads
these annotations (`mutated_names`, `state_init`, `reexport_names`, `block_id`,
`is_main_guard`) and decides how to emit the fold / tuple-if / re-export syntax.

Python is good at this kind of whole-module name analysis, so it lives here rather than in
the Lean codegen. The two public entry points, applied to a `Module` JSON node, are:

- `annotate_main_entrypoint(module_json)` — resolve the `main`/`main'` collision.
- `annotate_toplevel_state(module_json)` — thread state through top-level blocks.
"""

import hashlib

ASSIGNMENT_NODE_TYPES = {"Assign", "AnnAssign", "AugAssign"}
EXECUTABLE_BLOCK_NODE_TYPES = {"If", "For", "While", "Match", "Try"}
TOP_LEVEL_DECL_NODE_TYPES = {"FunctionDef", "Import", "ImportFrom", "Comment", "DocString"}


# ---------------------------------------------------------------------------
# Write-set analysis
# ---------------------------------------------------------------------------

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


def _names_referenced(node):
    """All Name ids referenced anywhere in `node`, not descending into nested function/class
    bodies (those open their own scope)."""
    found = set()

    def walk(n):
        if isinstance(n, dict):
            node_type = n.get("node_type")
            if node_type == "Name":
                ident = n.get("id")
                if isinstance(ident, str):
                    found.add(ident)
                return
            if node_type in {"FunctionDef", "AsyncFunctionDef", "Lambda", "ClassDef"}:
                return
            for value in n.values():
                walk(value)
        elif isinstance(n, list):
            for item in n:
                walk(item)

    walk(node)
    return found


def _annotate_ifs_in_block(stmts):
    """For each statement list, annotate each `If` with `if_assigned_names`: the names it
    assigns in either branch that are *also referenced later in the same block* — i.e. that
    escape the `if`. Branch-local names (used only inside the branch) are deliberately left
    out so they keep their natural per-branch scope and type inference.

    Then recurse into every sub-block (including function bodies, which form their own block).
    """
    if not isinstance(stmts, list):
        return
    n = len(stmts)
    for i, stmt in enumerate(stmts):
        if not isinstance(stmt, dict):
            continue
        if stmt.get("node_type") == "If":
            assigned = _block_mutated_names(stmt.get("body", []))
            assigned |= _block_mutated_names(stmt.get("orelse", []))
            later = set()
            for later_stmt in stmts[i + 1:]:
                later |= _names_referenced(later_stmt)
            stmt["if_assigned_names"] = sorted(assigned & later)
        for key in ("body", "orelse", "finalbody"):
            _annotate_ifs_in_block(stmt.get(key, []))
        for handler in stmt.get("handlers", []) or []:
            if isinstance(handler, dict):
                _annotate_ifs_in_block(handler.get("body", []))
        for case in stmt.get("cases", []) or []:
            if isinstance(case, dict):
                _annotate_ifs_in_block(case.get("body", []))


def annotate_if_assigned_names(module_json):
    """Annotate `If` nodes with the names that escape them (see `_annotate_ifs_in_block`).

    The Lean `doElem` lowering hoists each escaping name (not already bound in the enclosing
    scope) as `let mut name := default` *before* the `if`, so a variable first bound in one
    branch stays in scope for the other branch and for uses after the `if` — matching Python,
    which binds across branches in the enclosing scope rather than per-branch.
    """
    if isinstance(module_json, dict):
        _annotate_ifs_in_block(module_json.get("body", []))


def _plain_assign_name(stmt):
    """Return the single Name id a top-level `x = ...` binds, or None for other shapes."""
    if not (isinstance(stmt, dict) and stmt.get("node_type") == "Assign"):
        return None
    target = stmt.get("target")
    if isinstance(target, dict) and target.get("node_type") == "Name":
        return target.get("id")
    return None


def _block_id(index):
    """A short, stable, name-independent id for a top-level block, unique by position.

    Used to name the generated result `def` (`__py_block_<id>`) so distinct top-level
    blocks never collide, even two textually identical ones.
    """
    # 6 hex chars of a hash over the statement's position is plenty to avoid collisions
    # while staying readable; position guarantees uniqueness within a module.
    return hashlib.sha1(f"toplevel_block_{index}".encode()).hexdigest()[:6]


# ---------------------------------------------------------------------------
# Top-level state threading (streaming SSA over module globals)
# ---------------------------------------------------------------------------

def annotate_toplevel_state(module_json):
    """Annotate top-level executable blocks for state threading (streaming model).

    Walk the module body in source order, tracking the *current* initializer for each
    name. When a top-level `if`/`for`/`while`/`match`/`try` mutates names that have a
    current initializer, record `mutated_names`, a `state_init` map (the identifier to
    read for each name's pre-block value), and a `block_id` (for the result def name).

    Because the analysis is sequential, re-initializing a name between blocks is fine:
    each block consumes whichever initializer is current at that point. Each consumed
    initializer is versioned (its target id gets a unique `₀` suffix) so the clean
    name stays free to be re-exported with the block's result, avoiding Lean's immutable
    `def` redefinition error. After a block, its re-exported names become current again.
    """
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return
    body = module_json.get("body", [])

    # Index of the last top-level plain `name = ...` assignment per name. A block that
    # mutates `name` may keep the clean re-export name `name` only if it is the final
    # definition; if a later plain assignment re-initializes `name`, this block's
    # re-export is dead (shadowed) and must be versioned to avoid a Lean `def` collision.
    last_plain_assign_index = {}
    for idx, stmt in enumerate(body):
        name = _plain_assign_name(stmt)
        if name is not None:
            last_plain_assign_index[name] = idx

    # current_init[name] -> the Assign node currently providing `name`'s value, or
    # None once `name` has been (re-)exported by a block (so it is a clean global def).
    current_init = {}
    # Count how many times each name has been versioned, so repeated re-initialization
    # across blocks produces distinct versioned ids (both for inits and dead re-exports).
    version_count = {}

    def next_version(name):
        n = version_count.get(name, 0) + 1
        version_count[name] = n
        return f"{name}₀" if n == 1 else f"{name}₀{n}"

    for index, stmt in enumerate(body):
        if not isinstance(stmt, dict):
            continue

        # Track plain `name = ...` initializers as we pass them.
        plain_name = _plain_assign_name(stmt)
        if plain_name is not None:
            current_init[plain_name] = stmt
            continue

        if stmt.get("node_type") not in EXECUTABLE_BLOCK_NODE_TYPES:
            continue

        all_mutated = _block_mutated_names([stmt])
        # Only names with a current module-scope initializer are threaded globals.
        # Names assigned solely inside the block (e.g. tuple-unpack temporaries the
        # annotator introduced) are block-local and stay inside the lowering.
        mutated = sorted(name for name in all_mutated if current_init.get(name) is not None)
        if not mutated:
            continue
        stmt["mutated_names"] = mutated
        stmt["block_id"] = _block_id(index)

        state_init = {}
        reexport_names = {}
        for name in mutated:
            init_stmt = current_init[name]
            # Version the initializer so the clean name is free for re-export.
            versioned_init = next_version(name)
            init_stmt["target"]["id"] = versioned_init
            state_init[name] = versioned_init

            # Decide the re-export name. If a later plain assignment re-initializes
            # `name`, this block's result is shadowed: give it a versioned (dead) name so
            # the eventual final definition can own the clean `name`. Otherwise this is
            # the final definition and re-exports the clean `name`.
            if index < last_plain_assign_index.get(name, -1):
                reexport_names[name] = next_version(name)
                # `name` is re-initialized later, so it is not yet a clean global.
                current_init[name] = None
            else:
                reexport_names[name] = name
                # After this block re-exports `name`, it is a clean global def again.
                current_init[name] = None
        stmt["state_init"] = state_init
        stmt["reexport_names"] = reexport_names


# ---------------------------------------------------------------------------
# `main` / `_main` entry-point rename
# ---------------------------------------------------------------------------

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


# Lean's entry point is `main`, but Python's `main()` is an ordinary function. When both a
# `def main()` and a `__main__` guard exist, the Python function must yield the Lean name
# `main` to the guard. We rename it to `main'` rather than `_main`: a Python identifier
# cannot contain `'`, so `main'` can never collide with a user-defined helper (whereas a
# user `_main` helper is perfectly legal and would collide). `main'` is a valid Lean name.
MAIN_RENAME_TARGET = "main'"


def annotate_main_entrypoint(module_json):
    """Resolve the Python/Lean `main` naming collision and mark the `__main__` guard.

    - A top-level `def main()` with NO guard keeps the name `main` (importable).
    - A `__main__` guard with NO `def main` becomes Lean's `main` (the guard body).
    - When BOTH exist, the Python `def main` is renamed to `main'` (plus all references)
      so the guard can own Lean's entry-point name `main`. `'` is unusable in a Python
      identifier, so `main'` cannot clash with any user-defined name (e.g. a `_main` helper).
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
            # Rewrite every reference (call sites) `main` -> `main'` ...
            _rename_name_refs(module_json, "main", MAIN_RENAME_TARGET)
            # ... and the FunctionDef's own name, which is a plain field, not a Name node.
            for s in body:
                if isinstance(s, dict) and s.get("node_type") == "FunctionDef" and s.get("name") == "main":
                    s["name"] = MAIN_RENAME_TARGET
