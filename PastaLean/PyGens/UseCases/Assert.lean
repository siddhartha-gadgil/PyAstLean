import PastaLean.PyGens.Core.Utils
import PastaLean.PyVerify.AssertTactic

open Lean Meta Elab Term Qq Std

namespace PastaLean

@[pygen "Assert"]
def assertSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        -- An `assert` is a PROOF obligation — only meaningful in the prove (exact) version. The
        -- runnable `'rn` / `--mode run` (approx) twin exists to execute, not to prove, so drop the
        -- `have` there and emit a no-op statement instead.
        if (← getNumericMode) == .approx then
          return ← `(doElem| let _ := ())
        let .ok testJson := json.getObjValAs? Json "test" |
          throwError
          s!"Assert node does not have a 'test' field or it is not a JSON value: {json}"
        let testTerm ← withPropCondition true (getCode testJson `term)
        let hName := mkIdent (← freshName `ht)
        `(doElem | have $hName : $testTerm := by
            taste?
         )
    | `command, json => do
        -- A top-level `assert` (outside any function) has no `do` block to host a `have`, so emit a
        -- top-level `theorem` instead (prove version only — the run twin drops it). Proved by
        -- `taste?`, else left as `sorry`. Same `(test = true)` shape as the inline case.
        if (← getNumericMode) == .approx then
          return ⟨mkNullNode #[]⟩
        let .ok testJson := json.getObjValAs? Json "test" |
          throwError
          s!"Assert node does not have a 'test' field or it is not a JSON value: {json}"
        let testTerm ← withPropCondition true (getCode testJson `term)
        let hName := mkIdent (← freshName `assert_stmt)
        `(command| theorem $hName : $testTerm := by
            taste?
          )
    | _, _ => throwError s!"Unsupported syntax category for Assert node"

/-- Term-position `assert`, used by the *pure* (non-monadic) body path: an `assert` followed by the
rest of the body lowers to `have ht : … := by taste?; <rest>`, exactly the way `Head_Assign` threads
`let x := v; <rest>`. This is what keeps an assert-bearing function NON-monadic (no `Id.run do`) when
its other statements are pure — only the absence of this generator previously forced the monadic
fallback. The run twin (approx) drops the obligation and continues with the rest. -/
@[pygen "Head_Assert"]
def assertHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assert node does not have a 'rest' field or it is not a JSON value: {json}"
        -- The continuation: the remaining statements as a term, or `()` if the assert is last.
        let tailCode ← if rest.isEmpty then `(()) else withoutCheck do getCode (← splitList rest) `term
        if (← getNumericMode) == .approx then
          return tailCode
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"Assert node does not have a 'test' field or it is not a JSON value: {json}"
        let testTerm ← withPropCondition true (getCode testJson `term)
        let hName := mkIdent (← freshName `ht)
        `(have $hName : $testTerm := by taste?
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_Assert node"


end PastaLean
