"""Rewrite canonical counting `while` loops into `for i in range(...)` on the JSON IR.

`normalize_counting_loops(module_json)` is the only public entry point; import that.

It converts `while i < bound: body; i += 1` (or `<=`, or `i = i + 1`) into `for i in range(start, bound)`
so the verification path handles it via the well-supported `for`/`forIn` machinery. The rewrite fires
ONLY under guards that make it semantics-preserving; anything else is left as a `while` (still verifiable
directly via `pyWhile`). A false negative (leaving a convertible loop) is harmless; a false positive
(converting an inconvertible loop) is the only danger, so the guards are deliberately conservative:

  * the test is `i < bound` / `i <= bound` with `i` a bare name on the left;
  * the increment is exactly `i += 1` and is the loop's LAST statement;
  * `i` has a constant-int init in the same block;
  * `i` is unused after the loop (a `for` leaves `i = bound-1`, a `while` leaves `i = bound`);
  * `i` is not reassigned mid-body (a `for` would clobber it);
  * no loop-bound variable is mutated in the body — by rebind, by in-place mutation (`x.pop()`,
    `del x`, `x[i] = …`), so the snapshotted `range` bound can't drift from the re-read `while` test;
  * no `continue` (it would skip the increment).

See `src/test_normalize_loops.py` for the differential regression tests (original `while` vs `for`
equivalent over random inputs, plus guard-violation cases that must NOT convert).
"""
from __future__ import annotations


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


def _expr_name_ids(node):
    """Every identifier referenced anywhere in `node` (over-approximation: any `Name` id)."""
    ids, stack = set(), [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("node_type") == "Name" and isinstance(n.get("id"), str):
                ids.add(n["id"])
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return ids


def _assign_targets(target):
    """Yield the `Name` ids a target binds (handling nested `Tuple`/`List` unpack targets)."""
    if isinstance(target, dict):
        nt = target.get("node_type")
        if nt == "Name" and isinstance(target.get("id"), str):
            yield target["id"]
        elif nt in ("Tuple", "List"):
            for elt in target.get("elts", []):
                yield from _assign_targets(elt)


def _name_assigned(nodes, name):
    """True if `name` is bound by an `Assign`/`AugAssign`/`AnnAssign`/`For` anywhere in `nodes`
    (recursing into nested blocks). Guards the `while`→`for` rewrite against the two unsound cases:
    the loop counter reassigned mid-body, or a loop-bound variable mutated inside the loop."""
    stack = list(nodes)
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("node_type") in ("Assign", "AugAssign", "AnnAssign", "For"):
                if name in _assign_targets(n.get("target")):
                    return True
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return False


def _target_root(target):
    """Root `Name` id of an assignment/del/attribute target, following `Subscript`/`Attribute` chains
    (`x[i]`, `x.f`, `x[i].g` → `x`); `None` for tuple/other roots."""
    t = target
    while isinstance(t, dict) and t.get("node_type") in ("Subscript", "Attribute"):
        t = t.get("value")
    return t.get("id") if isinstance(t, dict) and t.get("node_type") == "Name" else None


def _name_mutated(nodes, name):
    """True if `name`'s object is mutated IN PLACE anywhere in `nodes`: a subscript/attribute-target
    assignment (`x[i] = …`, `x.f = …`), a `del` rooted at it, or a method call on it (`x.pop()`,
    `x.append(…)`, …). Conservative — any method call on `name` counts. This closes the bound-invariance
    hole that `_name_assigned` (rebind-only) misses: `while i < len(xs): xs.pop(); … ; i += 1` changes
    the bound without ever *reassigning* `xs`."""
    stack = list(nodes)
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            nt = n.get("node_type")
            if nt in ("Assign", "AugAssign", "AnnAssign") and _target_root(n.get("target")) == name:
                return True
            if nt == "Delete" and any(_target_root(t) == name for t in n.get("targets", [])):
                return True
            if nt == "Call":
                func = n.get("func")
                if isinstance(func, dict) and func.get("node_type") == "Attribute" \
                        and _target_root(func) == name:
                    return True
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return False


def _contains_continue(nodes):
    """True if a `continue` occurs at this loop's own level (not inside a nested loop). A `continue`
    jumps over the trailing `i += 1`, so the `while` and a `for` would iterate differently."""
    for n in nodes:
        if not isinstance(n, dict):
            continue
        nt = n.get("node_type")
        if nt == "Continue":
            return True
        if nt in ("For", "While"):
            continue  # a nested loop owns its own `continue`
        for key in ("body", "orelse", "finalbody"):
            if isinstance(n.get(key), list) and _contains_continue(n[key]):
                return True
        for h in n.get("handlers", []) or []:
            if isinstance(h, dict) and _contains_continue(h.get("body", [])):
                return True
    return False


def _normalize_counting_loops_in_block(body):
    """Rewrite each canonical counting `while` in `body` into a `for` (see module docstring for the
    guards). Recurses into nested blocks first."""
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
            # Soundness guards (beyond init + `i`-unused-after): the counter must be touched ONLY by the
            # trailing `i += 1` (a mid-body reassignment would be clobbered by `for`'s rebind), the loop
            # bound must be loop-invariant (a `for` range snapshots it, a `while` re-reads it each
            # iteration), and no `continue` (it would skip the increment). Any violation → leave the
            # `while` as-is (it is still verifiable directly via `pyWhile`).
            loop_body = body[i].get("body", [])
            bound_names = _expr_name_ids(bound)
            sound = (
                not _name_assigned(loop_body[:-1], loop_var)
                and not any(_name_assigned(loop_body, nm) or _name_mutated(loop_body, nm)
                            for nm in bound_names)
                and not _contains_continue(loop_body)
            )
            if init_idx is not None and sound and not _name_referenced(body[i + 1:], loop_var):
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
    """Public entry point: rewrite counting `while` loops in a module IR to `for` loops, in place."""
    if isinstance(module_json, dict) and isinstance(module_json.get("body"), list):
        _normalize_counting_loops_in_block(module_json["body"])
