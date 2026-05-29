import PyAstLean.PyGens.SpecialCalls.Functools

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Try each registered special term-level call lowerer until one claims the call. -/
def lowerSpecialCallTerm? (funcJson : Json) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (Option (TSyntax `term)) := do
  match ← lowerFunctoolsCallTerm? funcJson argsArray argsCodes keyWordsMap with
  | some lowered => return some lowered
  | none => return none

/-- Try each registered special `doElem` call lowerer until one claims the call. -/
def lowerSpecialCallDoElem? (funcJson : Json) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (Option (TSyntax `doElem)) := do
  match ← lowerFunctoolsCallDoElem? funcJson argsArray argsCodes keyWordsMap with
  | some lowered => return some lowered
  | none => return none

/-- info: 2 -/
#guard_msgs in
#eval 1+1

end PyAstLean
