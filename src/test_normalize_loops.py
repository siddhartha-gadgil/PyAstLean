"""Differential test for the `while → for` normalization (`normalize_counting_loops`).

How do we know the rewrite is correct? Two checks per case, using the REAL pass:

1. **Semantic equivalence** — execute the original `while` function and a hand-written `for`
   equivalent on many inputs; their results must agree. This validates the equivalence the pass
   relies on (`while i<n: B; i+=1`  ≡  `for i in range(start,n): B`).
2. **The pass behaves** — run the real `translate_to_json` (which invokes
   `normalize_counting_loops`) on the original source and assert the loop became a `For` (or, for a
   guard-violating case, stayed a `While`).

Together: the pass fires exactly when the conversion is semantics-preserving, and its target is
provably equivalent on the tested inputs. Run: `python src/test_normalize_loops.py`.
"""
import ast
import json
import random
import sys
import os

sys.path.append(os.path.dirname(__file__))
from py2lean import translate_to_json


def _run(src: str, fn: str, *args):
    ns: dict = {}
    exec(compile(src, "<diff>", "exec"), ns)
    return ns[fn](*args)


def _loop_node_types(src: str, fn: str):
    """The loop node_types inside `fn`'s body in the REAL post-normalization IR."""
    ir = json.loads(translate_to_json(src))
    for stmt in ir["body"]:
        if stmt.get("node_type") == "FunctionDef" and stmt.get("name") == fn:
            return [s["node_type"] for s in stmt["body"] if s.get("node_type") in ("For", "While")]
    return []


# (name, while-source, for-equivalent | None if the pass must REFUSE, fn, arg-generator)
CASES = [
    (
        "sum_upto",
        "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n",
        "def f(n):\n    s = 0\n    for i in range(0, n):\n        s = s + i\n    return s\n",
        "f", lambda: (random.randint(0, 40),),
    ),
    (
        "factorial",
        "def f(n):\n    r = 1\n    i = 1\n    while i <= n:\n        r = r * i\n        i = i + 1\n    return r\n",
        "def f(n):\n    r = 1\n    for i in range(1, n + 1):\n        r = r * i\n    return r\n",
        "f", lambda: (random.randint(0, 12),),
    ),
    (
        # GUARD VIOLATION: `i` is read after the loop, so a `for` (leaving i=n-1) would differ from the
        # `while` (leaving i=n). The pass MUST refuse — for-equivalent is None.
        "uses_i_after",
        "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
        None,
        "f", lambda: (random.randint(0, 30),),
    ),
    (
        # GUARD VIOLATION: the bound `n` is mutated in the body. A `for range(0,n)` snapshots `n`; the
        # `while` re-reads it each iteration → different iteration count. The pass MUST refuse.
        "bound_mutated",
        "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        n = n - 1\n        s = s + i\n        i = i + 1\n    return s\n",
        None,
        "f", lambda: (random.randint(0, 30),),
    ),
    (
        # GUARD VIOLATION: the counter `i` is reassigned mid-body; a `for` would clobber that rebind
        # each iteration. The pass MUST refuse.
        "loopvar_mutated",
        "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 3\n        s = s + i\n        i = i + 1\n    return s\n",
        None,
        "f", lambda: (random.randint(0, 30),),
    ),
    (
        # GUARD VIOLATION (in-place mutation): the bound `len(xs)` shrinks via `xs.pop()` — a method
        # call, not a reassignment — so a `for range(0,len(xs))` (bound snapshotted) diverges from the
        # `while` (bound re-read). The pass MUST refuse.
        "collection_bound_mutated",
        "def f(xs):\n    t = 0\n    i = 0\n    while i < len(xs):\n        xs.pop()\n        t = t + i\n        i = i + 1\n    return t\n",
        None,
        "f", lambda: ([1, 2, 3],),
    ),
]


def main() -> int:
    rng = random.Random(0)
    random.seed(0)
    ok = True
    for name, while_src, for_src, fn, gen in CASES:
        loops = _loop_node_types(while_src, fn)
        if for_src is None:
            # Guard violation: the pass must leave it a `While`.
            converted = loops == ["While"]
            print(f"[{name}] pass refused to convert (stayed While): {converted}")
            ok &= converted
            continue
        # The pass must have converted While → For.
        converted = loops == ["For"]
        # Semantic equivalence over many random inputs.
        equal = all(_run(while_src, fn, *args) == _run(for_src, fn, *args)
                    for args in (gen() for _ in range(2000)))
        print(f"[{name}] converted While→For: {converted} | while≡for on 2000 inputs: {equal}")
        ok &= converted and equal
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
