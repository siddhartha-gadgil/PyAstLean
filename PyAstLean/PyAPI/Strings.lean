import Mathlib

namespace PyAstLean

def pySplit : String → (sep : String := " ") → List String
  | s, sep => s.splitOn sep

def pyJoin : String → List String → String
  | sep, lst => String.intercalate sep lst

def pyReplace : String → (old : String) → (new : String) → String
  | s, old, new => s.replace old new

def pyStrip : String → (chars : String := " ") → String
  | s, chars => s.replace chars ""

def pyFind : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => -1

def pyIndex : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => panic! "ValueError: substring not found"

def pyStartswith : String → (pfx : String) → Bool
  | s, pfx => s.startsWith pfx

def pyEndswith : String → (sfx : String) → Bool
  | s, sfx => s.endsWith sfx

def pyLower : String → String
  | s => s.toLower

def pyUpper : String → String
  | s => s.toUpper

end PyAstLean
