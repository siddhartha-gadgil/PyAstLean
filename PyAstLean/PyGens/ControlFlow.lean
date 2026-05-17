import PyAstLean.PyGens.Assign

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- `Pass` is a statement-level no-op in Python, so we lower it to an empty command
or a trivial `do` element. -/
@[pygen "Pass"]
def passSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| let _ := ())
    | _, _ => throwError s!"Unsupported syntax category for Pass node"

@[pygen "Continue"]
def continueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| continue)
    | _, _ => throwError s!"Unsupported syntax category for Continue node"

@[pygen "Break"]
def breakSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| break)
    | _, _ => throwError s!"Unsupported syntax category for Break node"

@[pygen "While"]
def whileSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok test := json.getObjVal? "test" | throwError
          s!"While node does not have a 'test' field or it is not a JSON value: {json}"
        let testStx ← getCode test `term
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"While node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"While node does not have an 'orelse' field or it is not a JSON array: {json}"
        unless orelseElems.isEmpty do
          throwError "Python while-else blocks are not supported."
        let mut bodyStxArray := #[]
        for elem in bodyElems do
            let elemStx ← getCode elem `doElem
            bodyStxArray := bodyStxArray.push elemStx
        `(doElem| while $testStx do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for While node"

@[pygen "AugAssign"]
def augAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"AugAssign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok op := json.getObjValAs? String "op" | throwError
          s!"AugAssign node does not have an 'op' field or it is not a string: {json}"
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"AugAssign node does not have a 'value' field or it is not a JSON value: {json}"
        let targetIdent ← getCode targetJson `ident
        let valueCode ← getCode valueJson `term
        let updated ← match op with
          | "add" => `($targetIdent +ₚ $valueCode)
          | "sub" => `($targetIdent -ₚ $valueCode)
          | "mul" => `($targetIdent *ₚ $valueCode)
          | _ => throwError s!"Unsupported augmented assignment operator: {op}"
        `(doElem| $targetIdent:ident := $updated)
    | _, _ => throwError s!"Unsupported syntax category for AugAssign node"

@[pygen "For"]
def forSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"For node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok iterJson := json.getObjValAs? Json "iter" | throwError
          s!"For node does not have an 'iter' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"For node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"For node does not have an 'orelse' field or it is not a JSON array: {json}"
        unless orelseElems.isEmpty do
          throwError "Python for-else blocks are not supported."
        let targetIdent ← getCode targetJson `ident
        let iterCode ← rangeIterSyntax iterJson
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        `(doElem| for $targetIdent:ident in $iterCode do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for For node"

@[pygen "If"]
def ifSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        let testStx ← getCode testJson `term
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        let mut orelseStxArray := #[]
        for elem in orelseElems do
          let elemStx ← getCode elem `doElem
          orelseStxArray := orelseStxArray.push elemStx
        if orelseStxArray.isEmpty then
          let noop ← noopDoElemSyntax
          `(doElem| if $testStx then
              $[$bodyStxArray:doElem]*
            else
              $noop:doElem
          )
        else
          `(doElem| if $testStx then
              $[$bodyStxArray:doElem]*
            else
              $[$orelseStxArray:doElem]*)
    | `command, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        unless isMainGuardTest testJson do
          throwError "Only top-level `if __name__ == \"__main__\":` blocks are supported."
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := bodyStxArray.push elemStx
        let mainIdent := mkIdent `main
        if bodyNeedsExceptionMonad bodyElems then
          let exceptIdent := mkIdent ``PyAstLean.PyExcept
          `(command| def $mainIdent := (((do
              $[$bodyStxArray:doElem]*) : $exceptIdent _)))
        else
          let idRunIdent := mkIdent ``Id.run
          `(command| def $mainIdent := $idRunIdent do
              $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for If node"

end PyAstLean
