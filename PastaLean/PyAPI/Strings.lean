import Mathlib
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/-- Treat the most common Python whitespace characters as separators/strip chars. -/
private def isPyWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Helper used by `strip` to remove matching characters from the left. -/
private def stripLeftBy (p : Char → Bool) : List Char → List Char
  | c :: cs =>
      if p c then
        stripLeftBy p cs
      else
        c :: cs
  | [] => []

/-- Helper used by `strip` to remove matching characters from both ends. -/
private def stripBy (p : Char → Bool) (s : String) : String :=
  let leftTrimmed := stripLeftBy p s.toList
  let rightTrimmedRev := stripLeftBy p leftTrimmed.reverse
  String.ofList rightTrimmedRev.reverse

/--
Python-style `split()` with no explicit separator.

This collapses repeated whitespace and discards empty chunks, which matches the usual
Python behavior more closely than `splitOn " "`.
-/
private def splitOnPyWhitespace (s : String) : List String :=
  let rec go (rest : List Char) (currentRev : List Char) (accRev : List String) : List String :=
    match rest with
    | [] =>
        let accRev :=
          if currentRev.isEmpty then
            accRev
          else
            String.ofList currentRev.reverse :: accRev
        accRev.reverse
    | c :: cs =>
        if isPyWhitespace c then
          let accRev :=
            if currentRev.isEmpty then
              accRev
            else
              String.ofList currentRev.reverse :: accRev
          go cs [] accRev
        else
          go cs (c :: currentRev) accRev
  go s.toList [] []

/--
Elements accepted by Python-style `str.join`.

Python requires the iterable items to behave like strings. We support the two common
runtime cases here:
- `List String`-style inputs join directly
- a `String` input iterates by `Char`, and each character becomes a one-character string
-/
class PyStringJoin (α : Type) where
  toJoinString : α → String

/-- Strings already have the right representation for `str.join`. -/
instance : PyStringJoin String where
  toJoinString := id

/-- Joining over a string should treat each character as a one-character string. -/
instance : PyStringJoin Char where
  toJoinString c := String.singleton c

/--
Concrete string implementation for Python `join`.

Python `str.join` takes any iterable whose items behave like strings. In Lean, that means
the argument is any `α` with a `PyIterable α β` instance, together with a way to convert
each iterated item into the joined string fragment.
-/
def pyStringJoin {α β : Type} [PyIterable α β] [PyStringJoin β] (sep : String) (xs : α) : String :=
  String.intercalate sep <| (pyIter xs).map PyStringJoin.toJoinString

/-- Public runtime surface for Python `join`. -/
def pyJoin {α β : Type} [PyIterable α β] [PyStringJoin β] (sep : String) (xs : α) : String :=
  pyStringJoin sep xs

/-- Concrete string implementation for Python `replace`. -/
def pyStringReplace : String → (old : String) → (new : String) → String
  | s, old, new => s.replace old new

/-- Python `str.format` for the common positional `{}` placeholders: each `{}` is replaced,
left to right, by the next (already-stringified) argument. Splitting on `"{}"` yields the
literal segments between placeholders, which we interleave with the arguments. Surplus
arguments are ignored and surplus placeholders are left as the surrounding literals, which is
close enough for the `"{} {}".format(a, b)` idiom (named/spec placeholders aren't handled). -/
def pyStrFormat (fmt : String) (args : List String) : String :=
  match fmt.splitOn "{}" with
  | [] => ""
  | first :: rest =>
      let rec weave (segments : List String) (args : List String) (acc : String) : String :=
        match segments, args with
        | [], _ => acc
        | seg :: segs, a :: as' => weave segs as' (acc ++ a ++ seg)
        | seg :: segs, [] => weave segs [] (acc ++ seg)
      weave rest args first

/--
Concrete string implementation for Python `strip`.

When `chars` is omitted, Python strips surrounding whitespace. When `chars` is given,
Python treats it as a set of characters to trim from both ends.
-/
def pyStringStrip : String → (chars : String := " ") → String
  | s, chars =>
      if chars = " " then
        stripBy isPyWhitespace s
      else
        let stripCharSet := chars.toList
        stripBy (fun c => stripCharSet.contains c) s

/--
Concrete string implementation for Python `find`.

Returns `-1` when the substring is missing, matching Python's `str.find`.
-/
def pyStringFind : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => -1

/--
Concrete string implementation for Python `index`.

Raises at runtime when the substring is missing, matching Python's `str.index`.
-/
def pyStringIndex : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => panic! "ValueError: substring not found"

/-- Concrete string implementation for Python `startswith`. -/
def pyStringStartswith : String → (pfx : String) → Bool
  | s, pfx => s.startsWith pfx

/-- Concrete string implementation for Python `endswith`. -/
def pyStringEndswith : String → (sfx : String) → Bool
  | s, sfx => s.endsWith sfx

/-- Concrete string implementation for Python `lower`. -/
def pyStringLower : String → String
  | s => s.toList.map Char.toLower |> String.ofList

/-- Concrete string implementation for Python `upper`. -/
def pyStringUpper : String → String
  | s => s.toList.map Char.toUpper |> String.ofList

def pyStringCapitalize : String → String
  | s => s.capitalize

/--
Concrete string implementation for Python `split`.

With an explicit separator, this uses `splitOn`. With no explicit separator, it uses
Python-like whitespace splitting.
-/
def pyStringSplit : String → (sep : String := " ") → List String
  | s, sep =>
      if sep = " " then
        splitOnPyWhitespace s
      else
        if sep = "" then
          panic! "ValueError: empty separator"
        else
          s.splitOn sep

/-- Concrete string implementation for Python `splitlines()`. -/
def pyStringSplitLines : String → List String
  | s => s.splitOn "\n"

/-- Public runtime surface for Python `split`. -/
def pySplit : String → (sep : String := " ") → List String
  | s, sep => pyStringSplit s sep

/-- Public runtime surface for Python `replace`. -/
def pyReplace : String → (old : String) → (new : String) → String :=
  pyStringReplace

/-- Public runtime surface for Python `strip`. -/
def pyStrip : String → (chars : String := " ") → String
  | s, chars => pyStringStrip s chars

def pyStringCount : String → (sub : String) → Int
   | s, "" => s.length + 1
   | s, sub => (s.splitOn sub |>.length) - 1

-- #check String.count
def pyIsLower : String → Bool
  | s => s.toList.filter Char.isAlpha |>.all Char.isLower

def pyIsUpper : String → Bool
  | s => s.toList.filter Char.isAlpha |>.all Char.isUpper

def pyIsAlpha : String → Bool
  | s => s.toList.all Char.isAlpha

def pyIsDecimal : String → Bool
  | s => s.toList.all Char.isDigit

def pyIsAlphanum : String → Bool
  | s => s.toList.all Char.isAlphanum

def pyIsWhitespace : String → Bool
  | s => s.toList.all isPyWhitespace


def pyPartition : String → (sep : String) → (String × String × String)
  | s, sep =>
    match sep with
    | "" => panic! "ValueError: empty separator"
    | _ =>
      match s.find? sep with
      | some idx =>
          -- let idx := idx.offset.byteIdx
          let chars := s.toList
          let pfx := String.ofList (chars.take idx.offset.byteIdx)
          let suffix := String.ofList (chars.drop (idx.offset.byteIdx + sep.length))
          (pfx, sep, suffix)
      | none => (s, "", "")

theorem pyLower_is_lower (s : String) : pyIsLower s = true → pyStringLower s = s := by
  intro h
  unfold pyIsLower at h
  unfold pyStringLower
  simp_all only [List.all_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  have eq : List.map Char.toLower s.toList = s.toList := by
    have h'' : (List.map Char.toLower s.toList).length = s.toList.length := by grind
    apply List.ext_getElem!
    · exact h''
    · intro n
      by_cases h' : n < s.toList.length
      · simp_all only [List.length_map, String.length_toList, getElem!_pos, List.getElem_map]
        have g : s.toList[n] ∈ s.toList := by simp
        have g' : s.toList[n].isAlpha = false ∨ s.toList[n].isLower = true := by simp[h,g]
        by_cases sc : s.toList[n].isLower
        · grind only [Char.not_isLower_of_isUpper, Char.toLower_eq_of_not_isUpper]
        · grind only [Char.isAlpha, Char.toLower_eq_of_not_isUpper]
      · grind only [= getElem!_neg]
  simp [eq]


theorem pyUpper_is_upper (s : String) : pyIsUpper s = true → pyStringUpper s = s := by
  intro h
  unfold pyIsUpper at h
  unfold pyStringUpper
  simp_all only [List.all_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  have eq : List.map Char.toUpper s.toList = s.toList := by
    have h'' : (List.map Char.toUpper s.toList).length = s.toList.length := by grind
    apply List.ext_getElem!
    · exact h''
    · intro n
      by_cases h' : n < s.toList.length
      · simp_all only [List.length_map, String.length_toList, getElem!_pos, List.getElem_map]
        have g : s.toList[n] ∈ s.toList := by simp
        have g' : s.toList[n].isAlpha = false ∨ s.toList[n].isUpper = true := by simp[h,g]
        by_cases sc : s.toList[n].isUpper
        · grind only [Char.toUpper_eq_of_not_isLower, Char.not_isLower_of_isUpper]
        · grind only [Char.isAlpha, Char.toUpper_eq_of_not_isLower]
      · grind only [= getElem!_neg]
  simp [eq]

theorem pyLower_is_true_lower (s : String) : pyIsLower (pyStringLower s) = true := by
  unfold pyIsLower pyStringLower
  simp

theorem pyUpper_is_true_upper (s : String) : pyIsUpper (pyStringUpper s) = true := by
  unfold pyIsUpper pyStringUpper
  simp

theorem pyLower_idempotent (s : String) : pyStringLower (pyStringLower s) = pyStringLower s := by
  simp [pyLower_is_lower, pyLower_is_true_lower]

theorem pyUpper_idempotent (s : String) : pyStringUpper (pyStringUpper s) = pyStringUpper s := by
  simp [pyUpper_is_upper, pyUpper_is_true_upper]

theorem pyLower_length_invariant (s : String) : (pyStringLower s).length = s.length := by
  unfold pyStringLower
  grind only [String.length_eq_list_length, = List.length_map, String.length_toList]

theorem pyUpper_length_invariant (s : String) : (pyStringUpper s).length = s.length := by
  unfold pyStringUpper
  grind only [String.length_eq_list_length, = List.length_map, String.length_toList]

theorem pyFind_eq_pyIndex (s sub : String) : pyStringFind s sub ≠ -1 → pyStringFind s sub = pyStringIndex s sub := by
  intro h
  match eq : s.find? sub with
  | some idx =>
      simp [pyStringFind, pyStringIndex,eq]
  | none => simp [pyStringFind, eq] at h

-- #check String.split
end PastaLean
