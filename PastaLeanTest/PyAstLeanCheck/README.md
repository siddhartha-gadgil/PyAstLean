# PastaLeanCheck

`PastaLeanCheck` is a FileCheck-style test harness for Python → Lean translation.

It runs as part of `lake test` and checks generated Lean output by **shape**, not exact formatting.

## Where tests live

- Cases: `PastaLeanTest/PastaLeanCheck/Cases/*.py`
- Harness: `PastaLeanTest/PastaLeanCheck.lean`
- Regex engine: [`lean-regex`](https://github.com/pandaman64/lean-regex)

## Test file format

Put one check block inside each `.py` case file:

```python
# PastaLeanCHECK START
# TARGET: command
# CHECK: def
# CHECK: := fun
# CHECK: while . <= .
# PastaLeanCHECK END

def sum_to_n(n):
    total = 0
    i = 1
    while i <= n:
        total = total + i
        i = i + 1
    return total
```

`PastaLeanCHECK START` and `PastaLeanCHECK END` are required.

## Directives

- `TARGET: term|command|...` target passed to `src/py2lean.py` (default: `term`)
- `EXIT: <code>` expected process exit code (default: `0`)
- `CHECK: <pattern>` ordered match in stdout
- `CHECK-NOT: <pattern>` must not appear in stdout
- `CHECK-ERR: <pattern>` ordered match in stderr
- `CHECK-ERR-NOT: <pattern>` must not appear in stderr
- `CHECK-EXACT: <text>` exact stdout (trimmed)
- `CHECK-ERR-EXACT: <text>` exact stderr (trimmed)

## Pattern features

### 1. Ordered matching

`CHECK` lines are matched in order, like FileCheck.

### 2. Captures and reuse (lean-regex)

- Capture: `[[NAME:regex]]`
- Reuse later: `[[NAME]]`

Example:

```text
CHECK: let mut [[IDX:[A-Za-z_][A-Za-z0-9_]*]] :=
CHECK: [[IDX]] := [[IDX]] +ₚ
```

### 3. Wildcard dot

In plain pattern text, `.` means “match any fragment”.

Example:

```text
CHECK: while . <= .
```

Use `\.` for a literal dot.

### 4. `<=`, `\<=`, and `≤` equivalence

PastaLeanCheck treats all of these as equivalent in checks:

- `<=`
- `\<=`
- `≤`

So `CHECK: while . <= .` will match output containing `while i ≤ n`.

### 5. Whitespace-tolerant non-exact checks

For `CHECK`, `CHECK-NOT`, `CHECK-ERR`, and `CHECK-ERR-NOT`, whitespace in the
literal parts of the pattern is flexible: a space can match spaces, newlines,
or indentation in pretty-printed Lean output.

Example:

```text
CHECK: def GLOBAL_VAR := (42 : Int)
```

will match:

```lean
def GLOBAL_VAR :=
  (42 : Int)
```

This flexibility only applies to literal pattern text. Capture regexes like
`[[NAME:...]]` are left unchanged, and `CHECK-EXACT` / `CHECK-ERR-EXACT` remain strict.

## Adding a new case

1. Add `PastaLeanTest/PastaLeanCheck/Cases/<name>.py`
2. Add one `PastaLeanCHECK` block at top (or anywhere in comments)
3. Prefer shape checks over exact text
4. Run the whole suite:

```bash
lake test
```

## Running one file

For faster iteration, use the dedicated executable:

```bash
lake exe PastaLeancheck conditionals
```

You can also pass a full path:

```bash
lake exe PastaLeancheck PastaLeanTest/PastaLeanCheck/Cases/conditionals.py
```

Or run a few specific cases together:

```bash
lake exe PastaLeancheck conditionals loops functions_and_calls
```

With no arguments, it runs the full `PastaLeanCheck` suite:

```bash
lake exe PastaLeancheck
```

<details>
<summary><strong>Feature showcase (copy-paste examples)</strong></summary>

### A. Basic success case (`TARGET`, `CHECK`, `CHECK-NOT`)

```python
# PastaLeanCHECK START
# TARGET: command
# CHECK: def
# CHECK: := fun
# CHECK: while . <= .
# CHECK-NOT: panic
# PastaLeanCHECK END
```

### B. Failure case (`EXIT`, `CHECK-ERR`, `CHECK-ERR-NOT`)

```python
# PastaLeanCHECK START
# TARGET: term
# EXIT: 1
# CHECK-ERR: Error
# CHECK-ERR-NOT: Successfully generated code
# PastaLeanCHECK END
```

### C. Captures and reuse (`[[NAME:regex]]`, `[[NAME]]`)

```text
CHECK: let mut [[IDX:[A-Za-z_][A-Za-z0-9_]*]] :=
CHECK: while [[IDX]] <= .
CHECK: [[IDX]] := [[IDX]] +ₚ .
```

### D. Wildcard dot and literal dot

```text
CHECK: while . <= .
CHECK: module\.
```

### E. `<=`, `\<=`, and `≤` equivalence

All of the following are treated as equivalent in checks:

```text
CHECK: while . <= .
CHECK: while . \<= .
CHECK: while . ≤ .
```

### F. Exact checks (`CHECK-EXACT`, `CHECK-ERR-EXACT`)

```text
CHECK-EXACT: def exp := fun n ↦ n ^ₚ (4 : Int)
CHECK-ERR-EXACT: Error generating code: ...
```

### G. “Any error message is okay” (recommended resilient style)

When exact error wording may change, assert failure by exit code and only broad error presence:

```python
# PastaLeanCHECK START
# TARGET: term
# EXIT: 1
# CHECK-ERR: .
# CHECK-ERR-NOT: Successfully generated code
# PastaLeanCHECK END
```

This means:
- translation **must fail** (`EXIT: 1`)
- stderr must be **non-empty** (`CHECK-ERR: .`)
- and must not look like success (`CHECK-ERR-NOT: Successfully generated code`)

</details>
