import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.Operators

namespace PastaLean

/-- `Float` does not ship with an `Ord` instance, but Python's `min`/`max` need one. -/
instance : Ord Float where
  compare x y :=
    if x < y then
      Ordering.lt
    else if x > y then
      Ordering.gt
    else
      Ordering.eq

/--
Python-style eager `map`.

Unlike Python's lazy iterator result, the current runtime surface returns a `List`, which
fits the rest of the Lean-facing runtime well and keeps later consumers straightforward.
-/
def pyMap {α β γ : Type} [inst : PyIterable α β] (f : β → γ) (xs : α) : List γ :=
  (pyIter xs).map f

/-- Python-style eager `filter`, returning the kept elements as a `List`. -/
def pyFilter {α β : Type} [inst : PyIterable α β] (p : β → Bool) (xs : α) : List β :=
  (pyIter xs).filter p

/-- Python-style `zip`, truncating to the shorter iterable. -/
def pyZip {α β γ δ : Type} [instA : PyIterable α β] [instB : PyIterable γ δ]
    (xs : α) (ys : γ) : List (β × δ) :=
  (pyIter xs).zip (pyIter ys)

/-- Helper for Python-style `enumerate`, using `Int` indices to match the runtime's numeric story. -/
private def pyEnumerateFrom (start : Int) : List α → List (Int × α)
  | [] => []
  | x :: xs => (start, x) :: pyEnumerateFrom (start + 1) xs

/-- Python-style eager `enumerate`, defaulting to a `0` start index. -/
def pyEnumerate {α β : Type} [inst : PyIterable α β] (xs : α) (start : Int := 0) : List (Int × β) :=
  pyEnumerateFrom start (pyIter xs)

/-- Python-style `sum`, folding with the runtime addition operator and optional start value. -/
def pySum {α β : Type} [inst : PyIterable α β] [OfNat β 0]
    [PyHAdd β β β] (xs : α) (start : β := 0) : β :=
  (pyIter xs).foldl (fun acc x => acc +ₚ x) start


theorem pySum_nil {α β : Type} [inst : PyIterable α β] [OfNat β 0] [PyHAdd β β β] (start : β := 0) (x : α) (h : pyIter x = []) :
  pySum x start = start := by
    grind [pySum]

theorem pySum_Singleton {α β : Type} [inst : PyIterable α β] [OfNat β 0] [PyHAdd β β β] (start : β := 0) (x : α)
    : ∀ y , pyIter x = [y] → pySum x start = start +ₚ y := by
  intro y h
  grind [pySum]


/-- Pick the minimum element of a non-empty list using `Ord`. -/
private def pyMinList [Ord α] [Inhabited α] : List α → α
  | [] => panic! "ValueError: min() arg is an empty sequence"
  | x :: xs =>
      xs.foldl
        (fun best y => if compare y best == Ordering.lt then y else best)
        x

/-- Python-style `min` over one iterable argument. -/
def pyMin {α β : Type} [inst : PyIterable α β] [Ord β] [Inhabited β] (xs : α) : β :=
  pyMinList (pyIter xs)
-- #check List

theorem pyMinList_singleton [Ord α] [Inhabited α] : ∀ x : α, pyMinList [x] = x := by
  intro x
  grind [pyMinList]

theorem pyMin_singleton [inst : PyIterable α β] [Ord β] [Inhabited β] : ∀ (xs : α) (_ : (pyIter xs).length = 1), pyMin xs = (pyIter xs).head! := by
  intro xs h
  unfold pyMin
  match h' : pyIter xs with
  | [x] => simp [pyMinList_singleton x]
  | [] => aesop
  | x :: y :: s =>
    have c : (x :: y :: s).length ≥ 2 := by grind
    grind


/-- Pick the maximum element of a non-empty list using `Ord`. -/
private def pyMaxList [Ord α] [Inhabited α] : List α → α
  | [] => panic! "ValueError: max() arg is an empty sequence"
  | x :: xs =>
      xs.foldl
        (fun best y => if compare y best == Ordering.gt then y else best)
        x

/-- Python-style `max` over one iterable argument. -/
def pyMax {α β : Type} [inst : PyIterable α β] [Ord β] [Inhabited β] (xs : α) : β :=
  pyMaxList (pyIter xs)

/-- Python `min(iterable, key=f)`: the element whose projected key is smallest. Ties keep the
first element (Python's `min` is stable on the leftmost minimum). -/
def pyMinBy {α β κ : Type} [PyIterable α β] [Ord κ] [Inhabited β] (key : β → κ) (xs : α) : β :=
  match pyIter xs with
  | [] => panic! "ValueError: min() arg is an empty sequence"
  | x :: rest =>
      rest.foldl (fun best y => if compare (key y) (key best) == Ordering.lt then y else best) x

/-- Python `max(iterable, key=f)`: the element whose projected key is largest (leftmost on ties,
matching Python). -/
def pyMaxBy {α β κ : Type} [PyIterable α β] [Ord κ] [Inhabited β] (key : β → κ) (xs : α) : β :=
  match pyIter xs with
  | [] => panic! "ValueError: max() arg is an empty sequence"
  | x :: rest =>
      rest.foldl (fun best y => if compare (key y) (key best) == Ordering.gt then y else best) x


theorem pyMaxList_singleton [Ord α] [Inhabited α] : ∀ x : α, pyMaxList [x] = x := by
  intro x
  grind [pyMaxList]

theorem pyMax_singleton [inst : PyIterable α β] [Ord β] [Inhabited β] : ∀ (xs : α) (_ : (pyIter xs).length = 1), pyMax xs = (pyIter xs).head! := by
  intro xs h
  unfold pyMax
  match h' : pyIter xs with
  | [x] => simp [pyMaxList_singleton x]
  | [] => aesop
  | x :: y :: s =>
    have c : (x :: y :: s).length ≥ 2 := by grind
    grind
