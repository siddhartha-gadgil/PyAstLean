import Mathlib

namespace PastaLean

/-- Concrete list implementation for Python-style `append`. -/
def pyListAppend : List α → α → List α
  | lst, elem => lst ++ [elem]

/--
Public runtime surface for Python `append`.

Keep codegen targeting `pyAppend`; if another runtime type later needs append-like
behavior, this public name can be promoted to a protocol without changing the
generated Lean surface.
-/
def pyAppend : List α → α → List α :=
  pyListAppend

/--
Concrete list implementation for Python-style `pop(index)`.

If the index is out of bounds, return the provided default and leave the list unchanged.
-/
def pyListPop (xs : List α) (idx : Int) (default : Option α := none) : (Option α × List α) :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if hUpper : natIdx < xs.length then
      let value := xs.get ⟨natIdx, hUpper⟩
      (some value, xs.eraseIdx natIdx)
    else
      (default, xs)
  else
    (default, xs)

/--
API for `list.extend()` which concatenates two lists.
-/
def pyListExtend (xs : List α) (ys : List α) : List α :=
  xs ++ ys

/-- Public runtime surface for Python `extend()`. -/
def pyExtend : List α → List α → List α :=
  pyListExtend

/--
API for `list.index()` which returns the index of the first occurrence of the given
element in the list, or raises at runtime when the element is missing.
-/
def pyListIndex [DecidableEq α] (xs : List α) (elem : α) : Int :=
  match xs.findIdx? (fun x => x = elem) with
  | some idx => idx
  | none => panic! s!"ValueError: Element is not in list"

def pyListFind [DecidableEq α] (xs : List α) (elem : α) : Int :=
  match xs.findIdx? (fun x => x = elem) with
  | some idx => idx
  | none => -1

/--
API for `list.count(elem)` which returns the number of occurrences of the given element in the list.
-/
def PyListCount [DecidableEq α] (xs : List α) (elem : α) : Nat :=
  xs.count elem

/-- Public runtime surface for Python `count()`. -/
def pyListCount [DecidableEq α] : List α → α → Int :=
  fun xs elem => ((PyListCount xs elem) : Int)

def pyListReverse (xs : List α) : List α :=
  xs.reverse

/-- Public runtime surface for Python `reverse()`. -/
def pyReverse : List α → List α :=
  pyListReverse

/-- Public runtime surface for Python `clear()`. -/
def pyListClear (_ : List α) : List α :=
  []

/-- API runtime surface for Python `insert()`. -/
def pyListInsert (xs : List α) (idx : Int) (elem : α) : List α :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if natIdx <= xs.length then
      xs.take natIdx ++ [elem] ++ xs.drop natIdx
    else
      xs ++ [elem]
  else
    -- Python prepends when given a negative index
    [elem] ++ xs

/-- Public runtime surface for Python `insert()`. -/
def pyInsert : List α → Int → α → List α :=
  pyListInsert

/-- Python `.copy()` (lists and dicts). These are immutable values in this runtime, so a
shallow copy is the value itself. -/
def pyCopy {α : Type} (x : α) : α := x

/-- Python slice assignment `xs[start:stop] = repl`: replace the `start:stop` segment with
`repl` (which may differ in length). Bounds follow Python slice semantics (negative indices
count from the end; `none` means the list edge), matching `pyListSlice`. -/
def pySliceSet {α : Type} (xs : List α) (start stop : Option Int) (repl : List α) : List α :=
  let len := xs.length
  let s : Nat := match start with
    | some i => if i < 0 then (max 0 (len + i)).toNat else min len i.toNat
    | none => 0
  let e : Nat := match stop with
    | some i => if i < 0 then (max 0 (len + i)).toNat else min len i.toNat
    | none => len
  let e := max s e
  xs.take s ++ repl ++ xs.drop e


theorem pyListReverse_involution (xs : List α) : pyReverse (pyReverse xs) = xs := by
  unfold pyReverse pyListReverse
  apply List.reverse_reverse

theorem pyAppend_length_increase_one : ∀ (xs : List α) (elem : α), (pyAppend xs elem).length = xs.length + 1
  | [], elem => by simp [pyAppend, pyListAppend]
  | x :: xs, elem => by simp [pyAppend, pyListAppend]

theorem pyListExtend_length (xs ys : List α) : (pyListExtend xs ys).length = xs.length + ys.length := by
  unfold pyListExtend
  simp

theorem pyListPop_length_decrease_one (xs : List α) (idx : Int) (h : 0 <= idx) (h' : (idx.toNat) < xs.length) :
  pyListPop xs idx none|>.2.length = xs.length - 1 := by
  unfold pyListPop
  simp [h, h']
  grind

theorem pyListCount_increase_one [DecidableEq α] (xs : List α) (elem : α) :
  pyListCount (pyListAppend xs elem) elem = pyListCount xs elem + 1 := by
    unfold pyListCount
    simp [PyListCount, pyListAppend]

theorem pyListCount_extend [DecidableEq α] (xs ys : List α) (elem : α) :
  pyListCount (pyListExtend xs ys) elem = pyListCount xs elem + pyListCount ys elem := by
    unfold pyListExtend pyListCount
    simp [PyListCount]

theorem pyInsert_length_increase_one (xs : List α) (idx : Int) (elem : α) :
  (pyInsert xs idx elem).length = xs.length + 1 := by
    unfold pyInsert pyListInsert
    grind

theorem pyInsert_eq_append (xs : List α) (idx : Int) (elem : α) (h : idx >= xs.length) :
  pyInsert xs idx elem = pyAppend xs elem := by
    unfold pyInsert pyListInsert
    simp
    by_cases eq1 : idx < 0
    · grind
    · simp_all only [ge_iff_le, not_lt, ↓reduceIte]
      split
      next h_1 => by_cases eq2 : idx = xs.length
                  · simp [eq2, pyAppend, pyListAppend]
                  · grind
      next h_1 =>
        simp_all only [not_le]
        rfl


end PastaLean
