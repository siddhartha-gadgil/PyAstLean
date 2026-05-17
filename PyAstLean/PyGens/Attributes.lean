import Mathlib
import PyAstLean.Codegen
open Lean Meta Elab Term Qq Std

namespace PyAstLean

def pySplit : String → (sep :String := " ") → List String
  | s, sep => s.splitOn sep

-- Need to extend this to allow tuples and other iterables whenever they are implemented
def pyJoin : String → List String  → String
  | sep, lst => String.intercalate sep lst

def pyReplace : String → (old : String) → (new : String) → String
  | s, old, new => s.replace old new

def pyStrip : String → (chars : String := " ") → String
  | s, chars => s.replace chars ""

def pyFind : String → (sub : String) → Int
  | s, sub => match s.find? sub with
    | some idx => idx.offset.byteIdx
    | none => -1

def pyIndex : String → (sub : String) → Int
  | s, sub => match s.find? sub with
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

def pyAppend : List α → α → List α
  | lst, elem => lst ++ [elem]

def pyItems [BEq α] [Hashable α]: Std.HashMap α β → List (α × β)
  | m => m.toList

def pythonMethodMap (attr : String) : Option Name :=
  match attr with
  | "split"      => some ``pySplit
  | "join"       => some ``pyJoin
  | "replace"    => some ``pyReplace
  | "strip"      => some ``pyStrip
  | "find"       => some ``pyFind
  | "index"      => some ``pyIndex
  | "startswith" => some ``pyStartswith
  | "endswith"   => some ``pyEndswith
  | "lower"      => some ``pyLower
  | "upper"      => some ``pyUpper
  | "append"     => some ``pyAppend
  | "items"      => some ``pyItems
  | _            => none


-- @[pygen "Attribute"]
-- def attributeKind : (kind : SyntaxNodeKind) → Json →
--     PygenM (TSyntax kind)
--   | `term, json => do
--     let .ok valuejson := json.getObjValAs? Json "value" | throwError
--       "Attribute node missing 'value' field or it is not a Json object"
--     let .ok attr := json.getObjValAs? Json "attr" | throwError
--       "Attribute node missing 'attr' field or it is not a string"
--     let valCode ← getCode valuejson `term
--     match attr with
--     | "split" => `(pySplit $valCode)
--     | "join" => `(pyJoin $valCode)
--     | "replace" => `(pyReplace $valCode)
--     | "strip" => `(pyStrip $valCode)
--     | "find" => `(pyFind $valCode)
--     | "index" => `(pyIndex $valCode)
--     | "startswith" => `(pyStartswith $valCode)
--     | "endswith" => `(pyEndswith $valCode)
--     | "lower" => `(pyLower $valCode)
--     | "upper" => `(pyUpper $valCode)
--     | _ => throwError s!"Unsupported attribute '{attr}' in Attribute node"
--   | _, _ => throwError "Expected Attribute node"


end PyAstLean
