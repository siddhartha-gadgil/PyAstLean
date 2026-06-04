import Mathlib

namespace PyAstLean

/-!
This is for python's `chr()` builtin, which returns a string representing a character whose Unicode code point is the integer passed. For example, `chr(97)` returns the string `'a'`.
-/

def pyChr (n : Int) : String :=
  if n < 0 || n > 0x10FFFF then
    panic! "ValueError: chr() arg not in range(0x110000)"
  else
    String.singleton (Char.ofNat n.toNat)


/-!
This is for python's `ord()` builtin, which returns an integer representing the Unicode code point of a given character. For example, `ord('a')` returns `97`.
-/

def pyOrd (s : String) : Nat :=
  if s.length != 1 then
    panic! "TypeError: ord() expected a character, but string of length " ++ toString s.length ++ " found"
  else
    Char.toNat (String.Pos.Raw.get! s 0)

end PyAstLean
