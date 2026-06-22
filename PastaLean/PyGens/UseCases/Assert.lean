import PastaLean.PyGens.Core.Utils
import PastaLean.PyVerify.AssertTactic

open Lean Meta Elab Term Qq Std

namespace PastaLean

@[pygen "Assert"]
def assertSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok testJson := json.getObjValAs? Json "test" |
          throwError
          s!"Assert node does not have a 'test' field or it is not a JSON value: {json}"
        let testTerm ← getCode testJson `term
        let hName := mkIdent (← freshName `ht)
        `(doElem | have $hName : ($testTerm = true) := by
            taste?
         )
    | `command, json => do
        -- A top-level `assert` (outside any function) has no `do` block to host a `have`, so emit a
        -- top-level `theorem` instead: it records the asserted proposition as a checked obligation
        -- (proved by `grind`, else left as `sorry`). Same `(test = true)` shape as the inline case.
        let .ok testJson := json.getObjValAs? Json "test" |
          throwError
          s!"Assert node does not have a 'test' field or it is not a JSON value: {json}"
        let testTerm ← getCode testJson `term
        let hName := mkIdent (← freshName `assert_stmt)
        `(command| theorem $hName : ($testTerm = true) := by
            taste?
          )
    | _, _ => throwError s!"Unsupported syntax category for Assert node"


end PastaLean
