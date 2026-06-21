# Syntax & codegen gaps — TODO

Found by a "kitchen sink" stress test (a huge Python file mixing everything). Two kinds of gap.

## A. Accepted-but-miscompiled (the dangerous ones)

The transpiler **accepts** these and emits Lean, but the Lean **fails to compile** — so they are
NOT caught by the best-effort fallback (which only degrades node-level / backend-level *transpile*
failures, not compile failures). These should either be supported or made to degrade.

- [ ] **Tuple-unpack in a comprehension over `zip`** — `sum(a*b for a,b in zip(xs,ys))` types the
      unpacked elements as `ℚ × ℚ` instead of `Float × Float` → `failed to synthesize PyIterable
      (List (Float × Float)) (ℚ × ℚ)`. (Index form `xs[i]*ys[i]` works.)
- [ ] **Top-level name collisions with Mathlib** — a `def normalize` (also likely `det`-style
      common names) → `'normalize' has already been declared`. Generated top-level defs share the
      namespace with everything `open`ed (Mathlib). Need namespacing or a collision-safe prefix.
- [ ] **Dunder operator with a non-self return type** — `def __add__(self, other) -> float` is
      forced into `HAdd C C C` (result = the class), so a `Float`-returning body → type mismatch.
      Honour the dunder's actual return type / arg types.
- [ ] **`try`/`except` whose body `return`s a value** — `try: return int(s) except: return -1` →
      `pure a✝ : PUnit` vs `ℤ`. The exception-monad lowering mishandles a `return` inside the
      `try`. (Plain `raise` works; `try`/`except` without a return-in-body presumably works.)
- [ ] **`*args` / `**kwargs` (variadic params)** — `def f(*nums, **opts)` then `sum(nums)` →
      `Unknown identifier nums`. Variadic parameters are parsed but never bound.
- [ ] **Complex numbers** — `complex(x, y)`, `.real`, `.imag` → `Unknown identifier complex`.

## B. Detected-unsupported (already degrade cleanly to `pyUnsupported` placeholders)

Best-effort already contains these — they become no-op placeholders and don't break the file.
Listed here as eventual real-support targets.

- [ ] generators / `yield`
- [ ] `async def` / `await`
- [ ] `with` statements (context managers)  *(now degrades — see Done below)*
- [ ] walrus `:=` (`NamedExpr`)
- [ ] `global` / `nonlocal`
- [ ] foreign stdlib libs: `logging`, `random`, `os`, `sys`, `json`, `datetime`, `collections`
      (`Counter`/`deque`/`defaultdict`), `itertools`, `re`, `hashlib`, `threading`, `csv`,
      `asyncio` — these are foreign by design; support case-by-case if needed.

(`match` statements already work — not a gap.)

## Done
- [x] **`scipy.integrate.odeint`** — implemented as a fixed-step RK4 integrator
      (`Libraries/scipy/ScipyDef.lean` `pyScipyOdeint`); `np.linspace` made polymorphic so
      integer bounds (`np.linspace(0, 100, n)`) work. A full ODE simulation now transpiles,
      compiles, and runs (matching real SciPy to display precision).
- [x] **f-string format specs `:.Nf`** — `f"{x:.2f}"` now lowers to `pyFormatSpec`/`pyFixedFloat`
      (`PyAstLean/PyAPI/PyPrint.lean`); `node_visitor` captures a constant `format_spec`,
      `joinedInterpTerm` (CallExpr.lean) wraps the value. Other specs fall back to default render.
- [x] **Auto-avoid Mathlib name clashes** — a runnable program (has `main`) is wrapped in
      `namespace «_PyProgram»` with a root `main` forwarder (`src/py2lean.py`), so top-level defs
      like `e`/`f`/`normalize` no longer collide ("ambiguous term"). Libraries (no `main`) stay
      un-namespaced so cross-file imports still resolve.
- [x] **numpy 2-D indexing** — `a[i,j]` / `a[:,j]` (column) / `a[i,:]` (row) on `List (List _)`
      (`PyAstLean/PyGens/Core/Subscript.lean`, Tuple-slice branch).
- [x] **Best-effort now degrades *backend* failures too.** Previously a `with` statement (which
      `node_visitor` emits IR for but the Lean backend has no generator for) crashed the whole
      transpile even in best-effort. `src/py2lean.py` now catches a per-top-level-statement backend
      failure in best-effort mode and emits a `pyUnsupported` placeholder
      (`_backend_placeholder_command`) instead of aborting.
