import PastaLean.PyGens.Core.Utils

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Project the `.kind` field from a caught `PyException`. -/
def exceptionKindTerm (caughtIdent : TSyntax `ident) : PygenM (TSyntax `term) := do
  let caughtTerm : TSyntax `term := mkIdent caughtIdent.getId
  `(($(caughtTerm):term).OfKind)

/-- Raise a structured `PyException` value in generated `Except` code. -/
def throwExceptionDoElemSyntax (value : TSyntax `term) : PygenM (TSyntax `doElem) := do
  `(doElem| throw $value)

/-- Recover the exception constructor name from the JSON term used in `raise` / `except`. -/
def exceptionNameFromTermJson (json : Json) : PygenM String := do
  let .ok nodeType := json.getObjValAs? String "node_type" | throwError
    s!"Exception term is missing a 'node_type' field: {json}"
  match nodeType with
  | "Name" =>
      let .ok id := json.getObjValAs? String "id" | throwError
        s!"Exception name node is missing an 'id': {json}"
      return id
  | "Attribute" =>
      let .ok attr := json.getObjValAs? String "attr" | throwError
        s!"Exception attribute node is missing an 'attr': {json}"
      return attr
  | _ =>
      throwError s!"Unsupported exception type node: {nodeType}"

/-- Lower a Python `raise` payload into a `PyException` runtime value. -/
def exceptionValueTerm (excJson? : Option Json) : PygenM (TSyntax `term) := do
  let mkExcIdent := mkIdent ``PastaLean.PyException.Raise
  match excJson? with
  | none => `($mkExcIdent "Exception" "Python raise")
  | some excJson =>
      let .ok nodeType := excJson.getObjValAs? String "node_type" | throwError
        s!"Raise node exception term is missing a 'node_type' field: {excJson}"
      match nodeType with
      | "Name" =>
          let excName ← exceptionNameFromTermJson excJson
          `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | "Attribute" =>
          let excName ← exceptionNameFromTermJson excJson
          `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | "Call" =>
          let .ok funcJson := excJson.getObjValAs? Json "func" | throwError
            s!"Raise call is missing a 'func' field: {excJson}"
          let excName ← exceptionNameFromTermJson funcJson
          let .ok argsJson := excJson.getObjValAs? (Array Json) "args" | throwError
            s!"Raise call is missing an 'args' field: {excJson}"
          match argsJson[0]? with
          | some firstArg =>
              let argTerm ← getCode firstArg `term
              let toStringIdent := mkIdent ``toString
              `($mkExcIdent $(Syntax.mkStrLit excName) ($toStringIdent $argTerm))
          | none =>
              `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | _ =>
          let msgTerm ← getCode excJson `term
          `($mkExcIdent "Exception" (toString $msgTerm))

/-- Whether a statement may `return` a value on some path, scanning the statement and the
control-flow branches it owns (`If`/`For`/`While`/`With`/nested `Try`) but **not** descending into
nested `FunctionDef`/`Lambda` bodies (whose `return`s belong to the inner scope). Used to decide
whether a `try` body produces a non-`Unit` value that must be propagated out of the `try`. -/
partial def statementMayYieldValue (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" =>
      -- A bare `return` (no value) yields `Unit`; a `return <expr>` yields a value.
      match jsonFieldOption stmt "value" with
      | some _ => true
      | none => false
  | some "FunctionDef" => false
  | some "Lambda" => false
  | some _ =>
      match stmt with
      | .obj fields =>
          fields.toList.any fun (key, value) =>
            -- Only recurse into fields that hold owned sub-statements.
            if key == "body" || key == "orelse" || key == "finalbody"
                || key == "handlers" then
              match value with
              | .arr elems => elems.toList.any statementMayYieldValue
              | _ => statementMayYieldValue value
            else
              false
      | _ => false
  | none => false

/-- Whether any statement in `bodyElems` may `return` a value (see `statementMayYieldValue`). -/
def statementListMayYieldValue (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any statementMayYieldValue

/-- Whether any `except` handler's body may `return` a value. If a handler returns a value, the
whole `try` expression has a non-`Unit` result type, so the `try` branch must also produce that
type (even when the try-body itself only raises). -/
def handlersListMayYieldValue (handlersElems : Array Json) : Bool :=
  handlersElems.toList.any fun handlerJson =>
    match handlerJson.getObjValAs? (Array Json) "body" with
    | .ok bodyElems => statementListMayYieldValue bodyElems
    | .error _ => false

/-- Build the guard deciding whether a caught exception should enter a given handler. -/
def handlerConditionTerm (caughtIdent : TSyntax `ident) (handlerType? : Option Json) : PygenM (TSyntax `term) := do
  match handlerType? with
  | none => pure trueTerm
  | some handlerTypeJson =>
      let caughtKind ← exceptionKindTerm caughtIdent
      let .ok nodeType := handlerTypeJson.getObjValAs? String "node_type" | throwError
        s!"ExceptHandler type is missing a 'node_type' field: {handlerTypeJson}"
      match nodeType with
      | "Tuple" =>
          let .ok eltsJson := handlerTypeJson.getObjValAs? (Array Json) "elts" | throwError
            s!"Tuple handler type is missing an 'elts' field: {handlerTypeJson}"
          let mut cond? : Option (TSyntax `term) := none
          for elt in eltsJson do
            let excName := (← exceptionNameFromTermJson elt)
            let altCond ←
              if excName == "Exception" then
                pure trueTerm
              else
                `($caughtKind == $(Syntax.mkStrLit excName))
            cond? ← match cond? with
              | none => pure (some altCond)
              | some prev => pure (some (← orTerm prev altCond))
          pure <| cond?.getD falseTerm
      | _ =>
          let excName ← exceptionNameFromTermJson handlerTypeJson
          if excName == "Exception" then
            pure trueTerm
          else
            `($caughtKind == $(Syntax.mkStrLit excName))

mutual

/-- Compile the `except` chain into nested handler tests over the caught exception value. -/
partial def exceptHandlersDoElemSyntax (caughtIdent : TSyntax `ident) (handlers : List Json) :
    PygenM (TSyntax `doElem) := do
  match handlers with
  | [] => throwExceptionDoElemSyntax caughtIdent
  | handlerJson :: restHandlers => do
      let handlerType? := jsonFieldOption handlerJson "type"
      let handlerName? := handlerJson.getObjValAs? String "name" |>.toOption
      let .ok bodyElemsJson := handlerJson.getObjValAs? (Array Json) "body" | throwError
        s!"ExceptHandler node is missing a 'body' field: {handlerJson}"
      let cond ← handlerConditionTerm caughtIdent handlerType?
      let mut bodyElems := #[]
      if let some handlerName := handlerName? then
        bodyElems := bodyElems.push (← `(doElem| let $(mkIdent handlerName.toName) := $caughtIdent))
      bodyElems := bodyElems ++ (← tryBranchBodySyntax bodyElemsJson)
      let nextHandler ← exceptHandlersDoElemSyntax caughtIdent restHandlers
      if bodyElems.isEmpty then
        let noop ← noopDoElemSyntax
        `(doElem| if $cond then
            $noop:doElem
          else
            $nextHandler:doElem)
      else
        -- Splice the handler statements straight into the `then` branch (a `doSeq`), no `do` wrapper.
        `(doElem| if $cond then
            $[$bodyElems:doElem]*
          else
            $nextHandler:doElem)

/-- Compile a try-body / catch-body sequence, lowering nested `Try` nodes to inner
`PyExcept` terms so only genuinely nested tries introduce nested exception wrappers. -/
partial def tryBranchBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  for elem in bodyElems do
    let elemStx ←
      if jsonNodeType? elem == some "Try" then
        let nestedTry ← tryExceptTerm elem
        if statementDefinitelyReturns elem then
          `(doElem| $nestedTry:term)
        else
          `(doElem| let _ ← $nestedTry:term)
      else
        withoutCheck do
          getCode elem `doElem
    bodyStxArray := appendDoElems bodyStxArray elemStx
    if statementDefinitelyReturns elem then
      break
  return bodyStxArray

/-- Lower a Python `try` block to an inner `PyExcept` term so it can be reused in both
statement position and nested-expression-like contexts. -/
partial def tryExceptTerm (json : Json) : PygenM (TSyntax `term) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"Try node does not have a 'body' field or it is not a JSON array: {json}"
  let .ok handlersElems := json.getObjValAs? (Array Json) "handlers" | throwError
    s!"Try node does not have a 'handlers' field or it is not a JSON array: {json}"
  let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
    s!"Try node does not have an 'orelse' field or it is not a JSON array: {json}"
  let .ok finalbodyElems := json.getObjValAs? (Array Json) "finalbody" | throwError
    s!"Try node does not have a 'finalbody' field or it is not a JSON array: {json}"
  let bodyAndElse ← tryBranchBodySyntax (bodyElems ++ orelseElems)
  -- Splice the body statements straight into the `captureIOErrors (do …)` block — don't pre-wrap
  -- them in a `do` (which would nest `do (do …)`).
  let noopElem ← noopDoElemSyntax
  let innerBodyElems := if bodyAndElse.isEmpty then #[noopElem] else bodyAndElse
  let catchIdent := mkIdent `caught
  let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
  -- Wrap the body in `captureIOErrors` only when using the IO-backed `PyExcept` monad
  -- (i.e., when the function body uses real IO). For pure `PyExceptId`, no wrapping is needed.
  -- The wrapping converts IO errors (e.g., EOFError from input()) into catchable PyExceptions.
  let needsIOCapture := bodyNeedsIOMonad bodyElems
  let wrappedBody ←
    if needsIOCapture then
      let captureIdent := mkIdent ``PastaLean.PyExcept.captureIOErrors
      `($captureIdent (do $[$innerBodyElems:doElem]*))
    else
      `(do $[$innerBodyElems:doElem]*)
  -- If the try-body (or its `else`) can `return` a value, that value is the result of the whole
  -- `try` expression and must be propagated out; binding-and-discarding with `let _ ←` would pin
  -- the try-branch to `Unit` and clash with a value-returning `catch`. When the body is purely
  -- effectful we keep `let _ ←` so the try-branch stays `Unit` (e.g. inside a loop body, where an
  -- unconditional `return` would wrongly exit the enclosing function).
  -- The whole `try` expression yields a value if the body (or `else`) can `return` one, OR if any
  -- `except` handler can — in the latter case the `catch` branch produces a value, so the `try`
  -- branch must produce the same type. We bind the body's result to a fresh name and `return` it
  -- (rather than emitting a bare `return (← …)`, which mis-pretty-prints into an illegal
  -- mid-sequence `return`). When the body only raises, `wrappedBody` is polymorphic and unifies
  -- with the handler's value type.
  let bodyYieldsValue :=
    statementListMayYieldValue (bodyElems ++ orelseElems)
      || handlersListMayYieldValue handlersElems
  -- Emit the try-branch statements directly into the `try` block (spliced, not wrapped in a `do`).
  let tryBranchElems : Array (TSyntax `doElem) ←
    if bodyYieldsValue then do
      let tryValName := mkIdent (← freshName `__py_try_val)
      let bindElem ← `(doElem| let $tryValName ← $wrappedBody:term)
      let retElem ← `(doElem| return $tryValName)
      pure #[bindElem, retElem]
    else do
      let discardElem ← `(doElem| let _ ← $wrappedBody:term)
      pure #[discardElem]
  -- Don't hardcode the exception monad type - let Lean infer it from the function's return type.
  -- This allows the same try/catch code to work with both PyExcept (IO-backed) and PyExceptId (pure).
  if finalbodyElems.isEmpty then
    `(do
          try
            $[$tryBranchElems:doElem]*
          catch $catchIdent =>
            $catchBody:doElem)
  else
    let finalElems ← tryBranchBodySyntax finalbodyElems
    let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
    `(do
          try
            $[$tryBranchElems:doElem]*
          catch $catchIdent =>
            $catchBody:doElem
          finally
            $finalBlock:doElem)

end

@[pygen "Raise"]
def raiseSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let excJson? := jsonFieldOption json "exc"
        let excTerm ← exceptionValueTerm excJson?
        throwExceptionDoElemSyntax excTerm
    | _, _ => throwError s!"Unsupported syntax category for Raise node"

@[pygen "Try"]
def trySyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        tryExceptTerm json
    | `doElem, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Try node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok handlersElems := json.getObjValAs? (Array Json) "handlers" | throwError
          s!"Try node does not have a 'handlers' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"Try node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok finalbodyElems := json.getObjValAs? (Array Json) "finalbody" | throwError
          s!"Try node does not have a 'finalbody' field or it is not a JSON array: {json}"
        let bodyAndElse ← tryBranchBodySyntax (bodyElems ++ orelseElems)
        -- Splice body statements straight into `captureIOErrors (do …)` (no nested `do (do …)`).
        let noopElem ← noopDoElemSyntax
        let innerBodyElems := if bodyAndElse.isEmpty then #[noopElem] else bodyAndElse
        let catchIdent := mkIdent `caught
        let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
        -- Wrap the body in `captureIOErrors` only when using the IO-backed `PyExcept` monad.
        -- For pure `PyExceptId`, no wrapping is needed since there's no IO to capture.
        let needsIOCapture := bodyNeedsIOMonad bodyElems
        let wrappedBody ←
          if needsIOCapture then
            let captureIdent := mkIdent ``PastaLean.PyExcept.captureIOErrors
            `($captureIdent (do $[$innerBodyElems:doElem]*))
          else
            `(do $[$innerBodyElems:doElem]*)
        -- See `tryExceptTerm`: propagate the body's value out of the `try` when it (or any handler)
        -- can `return` one, binding it to a fresh name and returning it; otherwise keep the
        -- effectful `let _ ←` form. Splice the statements directly into `try` (no wrapping `do`).
        let bodyYieldsValue :=
          statementListMayYieldValue (bodyElems ++ orelseElems)
            || handlersListMayYieldValue handlersElems
        let tryBranchElems : Array (TSyntax `doElem) ←
          if bodyYieldsValue then do
            let tryValName := mkIdent (← freshName `__py_try_val)
            let bindElem ← `(doElem| let $tryValName ← $wrappedBody:term)
            let retElem ← `(doElem| return $tryValName)
            pure #[bindElem, retElem]
          else do
            let discardElem ← `(doElem| let _ ← $wrappedBody:term)
            pure #[discardElem]
        if finalbodyElems.isEmpty then
          `(doElem| try
              $[$tryBranchElems:doElem]*
            catch $catchIdent =>
              $catchBody:doElem)
        else
          let finalElems ← tryBranchBodySyntax finalbodyElems
          let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
          `(doElem| try
              $[$tryBranchElems:doElem]*
            catch $catchIdent =>
              $catchBody:doElem
            finally
              $finalBlock:doElem)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Try node"

end PastaLean
