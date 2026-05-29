import PyAstLean.PyGens.Core.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Python imports are currently runtime no-ops; library behavior is handled via symbol mapping. -/
def importDoElem : PygenM (TSyntax `doElem) :=
  `(doElem| let _ := ())

/-- Thread an import statement through the pure `Head_*` path by ignoring it and continuing. -/
def importHeadSyntax (json : Json) : PygenM (TSyntax `term) := do
  let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
    s!"Import head node does not have a 'rest' field or it is not a JSON value: {json}"
  let splitRest ← splitList rest
  withoutCheck do
    getCode splitRest `term

@[pygen "Import"]
def importSyntax : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `command, _ => pure ⟨mkNullNode #[]⟩
  | `doElem, _ => importDoElem
  | _, _ => throwError s!"Unsupported syntax category for Import node"

@[pygen "ImportFrom"]
def importFromSyntax : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `command, _ => pure ⟨mkNullNode #[]⟩
  | `doElem, _ => importDoElem
  | _, _ => throwError s!"Unsupported syntax category for ImportFrom node"

@[pygen "Head_Import"]
def importHeadPygen : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `term, json => importHeadSyntax json
  | _, _ => throwError s!"Unsupported syntax category for Head_Import node"

@[pygen "Head_ImportFrom"]
def importFromHeadPygen : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `term, json => importHeadSyntax json
  | _, _ => throwError s!"Unsupported syntax category for Head_ImportFrom node"

end PyAstLean
