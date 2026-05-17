# PyAstLean Lean Layout

This directory contains the Lean side of the Python-to-Lean pipeline.

There are two main layers:

1. `PyAPI/`
   This is the runtime layer.
   Put Lean implementations of Python-like behavior here.
   Examples:
   - `pyRange`
   - `pyAppend`
   - `pyItems`
   - `pySplit`
   - `PyException`
   - `PyExcept`
   - operator/typeclass APIs like `+ₚ`, `%ₚ`, `PyIterable`, `PyContains`

and more.

2. `PyGens/`
   This is the code generation layer.
   Put JSON-AST-to-Lean-syntax translation here.
   Examples:
   - `FunctionDef`
   - `Lambda`
   - `ListComp`
   - `If`
   - `Try`
   - `Assign`

and more.

The rough rule is:

- If you are implementing a Python operation in Lean, it belongs in `PyAPI/`.
- If you are deciding how a Python AST node should emit Lean syntax, it belongs in `PyGens/`.

## What Goes Where

### `PyAPI/`

Use `PyAPI/` when the same Lean function may be called from many generated nodes.

Good examples:
- string operations
- list/dict helpers
- exception values
- iteration helpers
- operator overloading / typeclass-based generic behavior

Suggested split:
- `Core.lean`: shared runtime types like `PyException`, `PyExcept`, `pyPrint`, and small cross-cutting helpers like `pyRange`
- `Operators.lean`: `+ₚ`, `-ₚ`, `*ₚ`, `/ₚ`, `%ₚ`, `^ₚ`
- `Strings.lean`: `pySplit`, `pyJoin`, `pyReplace`, ...
- `Lists.lean`: list-specific helpers like `pyAppend`
- `Dicts.lean`: dict-specific helpers like `pyItems`
- `CommonProtocols/`: intentionally extensible protocols like `pyLen`, `pyContains`, `pyIter`

### `PyGens/`

Use `PyGens/` when the work is about syntax lowering.

Examples:
- `Basic.lean`: core expression nodes like `Constant`, `BinOp`, `Call`
- `FuncDef.lean`: `Module`, `FunctionDef`, `Head_*` function-body threading
- `LambdaExpr.lean`: lambda lowering
- `ListComp.lean`: comprehensions and generator expressions
- `ControlFlow.lean`: `If`, `For`, `While`, `AugAssign`
- `Exceptions.lean`: `Try`, `Raise`

### `PyGens/Attributes.lean`

`Attributes.lean` is only dispatch glue.

Its job is:
- map Python method names like `"split"` or `"append"`
- to Lean runtime functions like `pySplit` or `pyAppend`

It should not hold the implementation of those functions.

Example:

- Python:
  `xs.append(x)`
- Codegen sees attribute name `"append"`
- `Attributes.lean` maps it to `pyAppend`
- actual implementation of `pyAppend` lives in `PyAPI/Lists.lean`

So:
- implementation lives in `PyAPI/*`
- method-name dispatch lives in `Attributes.lean`

### `PyAPI/CommonProtocols/`

Use `CommonProtocols/` only for operations that are deliberately meant to be
extensible across runtime types.

Good examples:
- `pyLen` for `List`, `String`, `Std.HashMap`, ...
- `pyContains` for membership tests across containers
- `pyIter` for iterable normalization

These are usually typeclass-based APIs:
- codegen emits one stable name
- Lean chooses the implementation from the argument type

This is the right home when you want one stable public runtime name and expect new
types to extend that operation later by adding instances.

This is not the right home for every helper that merely feels reusable.
Concrete APIs like `pyUpper`, `pySplit`, `pyItems`, or a list-specific `pyAppend`
should stay in their type-specific files unless you intentionally promote them into
a shared protocol.

## Builtins vs Methods

This distinction matters:

- Python builtin:
  `len(xs)`
- Python method:
  `xs.append(x)`

Builtins are not handled by `Attributes.lean`.
They usually go through function-name mapping such as `#map_names`, and then call a
runtime function in `PyAPI/CommonProtocols/` or another `PyAPI/*` file.

Methods go through `Attributes.lean`.

## When To Use A Typeclass

Use a typeclass when:
- Python has one operation name
- but Lean should support multiple unrelated container/value types
- and codegen should emit one stable function name

Good candidates:
- `len`
- containment / membership
- truthiness
- indexing

Do not use a typeclass when:
- the operation is naturally specific to one family
- or the API is just a direct helper for one type

Examples:
- `pySplit : String -> ...` does not need a typeclass
- `pyAppend : List α -> α -> List α` usually does not need a typeclass unless you want one generic append protocol

## Example 1: `len`

This is a good typeclass candidate because Python uses one surface name for many types.

```lean
class PyLen (α : Type) where
  pyLen : α → Int

def pyLen {α : Type} [PyLen α] (x : α) : Int :=
  PyLen.pyLen x

instance : PyLen (List α) where
  pyLen xs := xs.length

instance : PyLen String where
  pyLen s := s.length

instance [BEq α] [Hashable α] : PyLen (Std.HashMap α β) where
  pyLen m := m.size
```

Then codegen can always emit:

```lean
pyLen x
```

and Lean will choose the right implementation from the type of `x`.

Where this should go:
- runtime API: `PyAPI/CommonProtocols/Length.lean`

How Python reaches it:
- map builtin `len` to `pyLen`
- not through `Attributes.lean`

## Example 2: method dispatch without a typeclass

For a string method like `split`, a plain runtime function is enough:

```lean
def pySplit : String → String → List String
```

and in `Attributes.lean`:

```lean
def pythonMethodMap (attr : String) : Option Lean.Name :=
  match attr with
  | "split" => some ``pySplit
  | _ => none
```

This is not a typeclass case because the operation is already clearly tied to strings.

## Practical Rule

When adding a new Python feature, ask:

1. Is this a runtime behavior or a syntax-lowering rule?
   - runtime -> `PyAPI/`
   - syntax lowering -> `PyGens/`

2. Is this a builtin/function name or a method name?
   - builtin -> builtin mapping / `#map_names` and often `PyAPI/CommonProtocols/`
   - method -> `Attributes.lean`

3. Does one Python operation need multiple Lean implementations based on type?
   - yes -> use a typeclass
   - no -> plain function is enough

## Stable Surface Rule

Try to keep one stable public Lean name per Python operation.

Examples:
- `len(x)` lowers to `pyLen`
- `x in y` lowers to `pyContains`
- `xs.append(v)` lowers to `pyAppend`
- `s.upper()` lowers to `pyUpper`

Then choose the implementation strategy underneath:
- if the operation is intentionally extensible, put the public name in `CommonProtocols/`
- if it is concrete today, keep it as a plain function in a type-specific file

This lets codegen stay stable. If a concrete operation later needs to become
extensible, you can promote its implementation to a protocol without changing the
generated surface syntax.
