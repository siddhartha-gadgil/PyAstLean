import Mathlib

namespace PastaLean

/-- Minimal runtime value for translated Python exceptions. -/
structure PyException where
  kind : String
  msg : String
  deriving Inhabited, Repr, BEq

namespace PyException

/-- Smart constructor used by codegen so generated Lean does not need to expose `.mk`. -/
def Raise (kind : String) (msg : String := "") : PyException :=
  .mk kind msg

/-- Accessor used by generated code when matching caught exceptions by kind. -/
def OfKind (exc : PyException) : String :=
  exc.kind

end PyException

/-- Concrete exception monad used for translated Python code that can raise. -/
abbrev PyExcept (α : Type) := ExceptT PyException IO α

instance : ToString PyException where
  toString exc :=
    if exc.msg.isEmpty then
      exc.kind
    else
      s!"{exc.kind}: {exc.msg}"

/-- Run `body`, converting any underlying `IO` error into a `PyException` raise (leaving an
already-raised `PyException` untouched). A bare Python `except:` catches *everything*, including
the `EOFError`/`OSError` that `input()` raises at end of input — but those surface as `IO` errors
below the `ExceptT` layer, invisible to a `try … catch` over `PyExcept` (which only sees
`PyException`). Wrapping the `try` body in this turns such errors into `PyException`s, so the
translated `catch` (which keeps a real `try … catch`, so `break`/`continue` in the handler still
work) catches them — matching Python. -/
def PyExcept.captureIOErrors {α : Type} (body : PyExcept α) : PyExcept α :=
  ExceptT.mk
    (try body.run
     catch e : IO.Error => pure (Except.error (PyException.Raise "Exception" (toString e))))

/-- Python-style `range` supporting positive and negative steps. -/
def pyRange (stop : Int) (start : Int := 0) (step : Int := 1) : List Int := do
  if step > 0 then
    List.map (fun i => start + i) (List.range' 0 ((stop - start) / step + (stop - start) % step).toNat step.toNat)
  else if step < 0 then
    List.map (fun i => start - i) (List.range' 0 ((start - stop) / (-step) + (start - stop) % (-step)).toNat (-step).toNat)
  else
    []

/-- Python-style list indexing with negative indices and runtime failure on out-of-bounds access. -/
def pyListGetItem {α : Type} [Inhabited α] (xs : List α) (idx : Int) : α :=
  let len := xs.length
  if len == 0 then
    panic! "IndexError: list index out of range"
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      panic! "IndexError: list index out of range"
    else
      match xs[trueIdx.toNat]? with
      | some value => value
      | none => panic! "IndexError: list index out of range"

/-- Python-style slicing for lists. -/
def pyListSlice {α : Type} (xs : List α) (start : Option Int) (stop : Option Int) : List α :=
  let len := xs.length
  let start : Nat := match start with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => 0
  let stop : Nat := match stop with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => len
  xs.take stop |> List.drop start

/-- Full Python list slicing `xs[start:stop:step]`, including a negative `step` (e.g. `xs[::-1]`
reverses; `xs[::2]` takes every other element). Implements CPython's index clamping: with a
positive step the bounds clamp into `[0, len]`, with a negative step into `[-1, len-1]`, then it
walks `start, start+step, …` while still on the correct side of `stop`. A `step` of `0` (a Python
`ValueError`) yields `[]`. -/
def pyListSliceStep {α : Type} (xs : List α) (start stop step : Option Int) : List α :=
  let len : Int := xs.length
  let s : Int := step.getD 1
  if s == 0 then []
  else
    let arr := xs.toArray
    let clampPos (i : Int) : Int := if i < 0 then max 0 (len + i) else min i len
    let clampNeg (i : Int) : Int := if i < 0 then max (-1) (len + i) else min i (len - 1)
    let lo : Int := if s > 0 then (match start with | none => 0 | some i => clampPos i)
                    else (match start with | none => len - 1 | some i => clampNeg i)
    let hi : Int := if s > 0 then (match stop with | none => len | some i => clampPos i)
                    else (match stop with | none => -1 | some i => clampNeg i)
    let rec go (idx : Int) (fuel : Nat) (acc : List α) : List α :=
      match fuel with
      | 0 => acc.reverse
      | fuel + 1 =>
        let onSide := if s > 0 then idx < hi else idx > hi
        if onSide && idx ≥ 0 && idx < len then
          match arr[idx.toNat]? with
          | some x => go (idx + s) fuel (x :: acc)
          | none => acc.reverse
        else acc.reverse
    go lo (xs.length + 1) []

/-- Python-style indexing/slicing for strings. -/
def pyStringGetItem (s : String) (idx : Int) : Option Char :=
  let lst := s.toList
  let len := lst.length
  if len == 0 then
    none
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      none
    else
      lst[trueIdx.toNat]?

/-- Python-style string indexing, returning a one-character string. Python has no separate
character type — `s[i]` is a length-1 `str` — so string element access yields `String`, keeping
it interoperable with string literals (`s[i] == 'x'`), `ord`, and string methods. An
out-of-range index yields the empty string. -/
def pyStringGetItemStr (s : String) (idx : Int) : String :=
  match pyStringGetItem s idx with
  | some c => c.toString
  | none => ""

/-- Python-style slicing for strings. -/
def pyStringSlice (s : String) (start : Option Int) (stop : Option Int) : String :=
  let lst := s.toList
  let sliced := pyListSlice lst start stop
  String.ofList sliced

/-- Full Python string slicing `s[start:stop:step]` (negative step reverses, etc.). -/
def pyStringSliceStep (s : String) (start stop step : Option Int) : String :=
  String.ofList (pyListSliceStep s.toList start stop step)

/-- Python slicing `c[lo:hi:step]` over the types that support it. Both lists and strings slice,
and codegen cannot tell which a value is (e.g. `a[1:]` where `a` is a parameter), so it targets
the single name `pySlice` and the instance is chosen by the value's type — a `String` slices to a
`String`, a `List` to a `List`. The `step` is carried so `a[::-1]`/`a[::2]` work. -/
class PySlice (α : Type) where
  slice : α → Option Int → Option Int → Option Int → α

/-- Dispatch Python slicing `c[lo:hi:step]` through the `PySlice` typeclass. -/
def pySlice {α : Type} [PySlice α] (c : α) (lo hi step : Option Int) : α :=
  PySlice.slice c lo hi step

instance {β : Type} : PySlice (List β) where
  slice xs lo hi step := pyListSliceStep xs lo hi step

instance : PySlice String where
  slice s lo hi step := pyStringSliceStep s lo hi step

/--
Concrete carrier for a Python construct the transpiler does not support (foreign libraries like
`logging`/`requests`, unhandled syntax, ...). It carries the original source and prints as its
`Repr`.
-/
structure PyUnsupportedValue where
  source : String
  deriving Inhabited, Repr, BEq

/--
Best-effort fallback sink. Codegen emits `pyUnsupported "<original source>"` in
every position a dropped statement appears — bare statement (`let _ := …`), assignment
(`let x := …`), or top-level (`def … := …`). Because it returns a concrete type, the binding
always elaborates and keeps the variable **declared** (no unconstrained `Inhabited ?m`); the
[`PastaLean.Linter`] flags each use with a yellow "not supported" warning.
-/
@[inline] def pyUnsupported (source : String) : PyUnsupportedValue := ⟨source⟩

end PastaLean
