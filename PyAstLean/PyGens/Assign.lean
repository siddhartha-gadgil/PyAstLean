import PyAstLean.PyGens.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Simple returned expressions can stay unparenthesized; more complex or effectful ones
keep parentheses so Lean parses multiline `return` expressions reliably. -/
def shouldParenthesizeReturnValue (value : Json) : Bool :=
  if jsonUsesExceptionEffect value then
    true
  else
    match jsonNodeType? value with
    | some "Name" => false
    | some "Constant" => false
    | some "Attribute" => false
    | _ => true

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(def $nameIdent := $valueStx)
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        let rhs ←
          if jsonUsesExceptionEffect value then
            `((← $valueStx))
          else
            pure valueStx
        if ← hasVar nameIdent.getId then
            `(doElem| $nameIdent:ident := $rhs)
        else
            let stx ← `(doElem| let mut $nameIdent:ident := $rhs)
            addVar nameIdent.getId
            return stx
    | _, _ => throwError s!"Unsupported syntax category for Assign node"

/--
`AnnAssign` represents Python's annotated assignment syntax (`x : T = v` or `x : T`).
The remaining declaration-only form is currently treated as a no-op in `do` blocks, and
rejected at top level until the backend grows explicit type-directed declarations.
-/
@[pygen "AnnAssign"]
def annAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            throwError "Declaration-only annotated assignments are not yet supported at top level."
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `command json
    | `doElem, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            `(doElem| let _ := ())
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `doElem json
    | _, _ => throwError s!"Unsupported syntax category for AnnAssign node"

@[pygen "Return"]
def returnSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        match value with
        | .null =>
            `(doElem| return (()))
        | _ =>
            let valueStx ← getCode value `term
            let retValue ←
              if jsonUsesExceptionEffect value then
                `((← $valueStx))
              else
                pure valueStx
            if shouldParenthesizeReturnValue value then
              `(doElem| return ($retValue))
            else
              `(doElem| return $retValue)
    | _, _ => throwError s!"Unsupported syntax category for Return node"

end PyAstLean
