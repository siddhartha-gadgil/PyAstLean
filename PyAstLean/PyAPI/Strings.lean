import Mathlib

namespace PyAstLean

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
Concrete string implementation for Python `join`.

The receiver string is the separator, so `"sep".join(xs)` becomes `pyStringJoin "sep" xs`.
-/
def pyStringJoin : String → List String → String
  | sep, lst => String.intercalate sep lst

/-- Concrete string implementation for Python `replace`. -/
def pyStringReplace : String → (old : String) → (new : String) → String
  | s, old, new => s.replace old new

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
  | s => s.toLower

/-- Concrete string implementation for Python `upper`. -/
def pyStringUpper : String → String
  | s => s.toUpper

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
        s.splitOn sep

/-- Concrete string implementation for Python `splitlines()`. -/
def pyStringSplitLines : String → List String
  | s => s.splitOn "\n"

/-- Public runtime surface for Python `split`. -/
def pySplit : String → (sep : String := " ") → List String
  | s, sep => pyStringSplit s sep

/-- Public runtime surface for Python `join`. -/
def pyJoin : String → List String → String :=
  pyStringJoin

/-- Public runtime surface for Python `replace`. -/
def pyReplace : String → (old : String) → (new : String) → String :=
  pyStringReplace

/-- Public runtime surface for Python `strip`. -/
def pyStrip : String → (chars : String := " ") → String
  | s, chars => pyStringStrip s chars

/-- Public runtime surface for Python `find`. -/
def pyFind : String → (sub : String) → Int :=
  pyStringFind

end PyAstLean
