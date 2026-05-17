import PyAstLean.PyGens.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

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
  let mkExcIdent := mkIdent ``PyAstLean.PyException.Raise
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
        let bodyBlock ← `(doElem| do
            $[$bodyElems:doElem]*)
        `(doElem| if $cond then
            $bodyBlock:doElem
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
    bodyStxArray := bodyStxArray.push elemStx
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
  let bodyBlock ← sequenceDoElems bodyAndElse (← noopDoElemSyntax)
  let catchIdent := mkIdent `caught
  let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
  let exceptIdent := mkIdent ``PyAstLean.PyExcept
  if finalbodyElems.isEmpty then
    `(((do
          try
            $bodyBlock:doElem
          catch $catchIdent =>
            $catchBody:doElem) : $exceptIdent _))
  else
    let finalElems ← tryBranchBodySyntax finalbodyElems
    let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
    `(((do
          try
            $bodyBlock:doElem
          catch $catchIdent =>
            $catchBody:doElem
          finally
            $finalBlock:doElem) : $exceptIdent _))

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
        let bodyBlock ← sequenceDoElems bodyAndElse (← noopDoElemSyntax)
        let catchIdent := mkIdent `caught
        let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
        if finalbodyElems.isEmpty then
          `(doElem| try
              $bodyBlock:doElem
            catch $catchIdent =>
              $catchBody:doElem)
        else
          let finalElems ← tryBranchBodySyntax finalbodyElems
          let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
          `(doElem| try
              $bodyBlock:doElem
            catch $catchIdent =>
              $catchBody:doElem
            finally
              $finalBlock:doElem)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Try node"

end PyAstLean
