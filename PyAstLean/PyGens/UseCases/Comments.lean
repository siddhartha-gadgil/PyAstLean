import PyAstLean.PyGens.Core.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Internal placeholder prefix used while rendering Python comments/docstrings through Lean syntax. -/
def commentPlaceholderPrefix : String := "__pyastlean_comment_"

/-- Build the placeholder identifier used for later comment/docstring post-processing. -/
def commentPlaceholderIdent (json : Json) : PygenM (TSyntax `ident) := do
  let .ok commentId := json.getObjValAs? String "comment_id" | throwError
    s!"Comment node does not have a 'comment_id' field or it is not a string: {json}"
  pure <| mkIdent (s!"{commentPlaceholderPrefix}{commentId}").toName

/-- All comment/docstring nodes lower to a recognizable placeholder assignment first. -/
def commentPlaceholderDoElem (json : Json) : PygenM (TSyntax `doElem) := do
  let ident ← commentPlaceholderIdent json
  `(doElem| let $ident := ())

/-- Thread a comment/docstring placeholder through the pure `Head_*` body lowering path. -/
def commentHeadSyntax (json : Json) : PygenM (TSyntax `term) := do
  let ident ← commentPlaceholderIdent json
  let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
    s!"Comment head node does not have a 'rest' field or it is not a JSON value: {json}"
  let splitRest ← splitList rest
  let tailCode ← withoutCheck do
    getCode splitRest `term
  `(let $ident := ()
    $tailCode)

@[pygen "Comment"]
def commentSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let ident ← commentPlaceholderIdent json
        `(def $ident := ())
    | `doElem, json => commentPlaceholderDoElem json
    | `term, _ => throwError "Standalone comment nodes are statement-only."
    | _, _ => throwError s!"Unsupported syntax category for Comment node"

@[pygen "DocString"]
def docStringSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let ident ← commentPlaceholderIdent json
        `(def $ident := ())
    | `doElem, json => commentPlaceholderDoElem json
    | `term, _ => throwError "Standalone docstring nodes are statement-only."
    | _, _ => throwError s!"Unsupported syntax category for DocString node"

@[pygen "Head_Comment"]
def commentHeadPygen : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => commentHeadSyntax json
    | _, _ => throwError s!"Unsupported syntax category for Head_Comment node"

@[pygen "Head_DocString"]
def docStringHeadPygen : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => commentHeadSyntax json
    | _, _ => throwError s!"Unsupported syntax category for Head_DocString node"

end PyAstLean
