import PyAstLean.PyGens.Core.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

/-- Extract the node type tag from a structural pattern JSON node. -/
def matchPatternNodeType (patternJson : Json) : PygenM String := do
  let .ok nodeType := patternJson.getObjValAs? String "node_type" | throwError
    s!"Pattern node does not have a 'node_type' field or it is not a string: {patternJson}"
  return nodeType

/-- Wrap a match branch body in the `let` bindings introduced by the matched pattern. -/
partial def matchWrapBindingsTerm (bindings : Array (TSyntax `ident × TSyntax `term)) (body : TSyntax `term) :
    PygenM (TSyntax `term) := do
  let mut result := body
  for (nameIdent, valueTerm) in bindings.toList.reverse do
    result ← `(let $nameIdent := $valueTerm
      $result)
  return result

/-- Turn match pattern bindings into `do`-notation `let`s for an effectful branch. -/
def matchBindingDoElems (bindings : Array (TSyntax `ident × TSyntax `term)) :
    PygenM (Array (TSyntax `doElem)) := do
  let mut elems := #[]
  for (nameIdent, valueTerm) in bindings do
    elems := elems.push (← `(doElem| let $nameIdent := $valueTerm))
  return elems

/-- Compile the tail of a pure match branch, or use `()` if no statements remain. -/
def matchSplitListOrPureUnit (xs : List Json) : PygenM (TSyntax `term) := do
  if xs.isEmpty then
    `(())
  else
    let split ← splitList xs
    withoutCheck do
      getCode split `term

/-- Detect patterns that are guaranteed to match, so the final branch can omit a synthetic fallback. -/
partial def isIrrefutableMatchPattern (patternJson : Json) : Bool :=
  match patternJson.getObjValAs? String "node_type" with
  | .ok "MatchAs" =>
      match jsonFieldOption patternJson "pattern" with
      | none => true
      | some inner => isIrrefutableMatchPattern inner
  | .ok "MatchStar" => true
  | .ok "MatchSequence" =>
      match patternJson.getObjValAs? (Array Json) "patterns" with
      | .ok patterns => patterns.toList.all isIrrefutableMatchPattern
      | _ => false
  | .ok "MatchOr" =>
      match patternJson.getObjValAs? (Array Json) "patterns" with
      | .ok patterns => patterns.toList.any isIrrefutableMatchPattern
      | _ => false
  | _ => false

/-- Check whether a pattern can be represented directly as a Lean pattern. -/
partial def canLowerDirectMatchPattern (patternJson : Json) : Bool :=
  match patternJson.getObjValAs? String "node_type" with
  | .ok "MatchValue" => true
  | .ok "MatchSingleton" => true
  | .ok "MatchAs" =>
      match jsonFieldOption patternJson "pattern" with
      | none => true
      | some inner => canLowerDirectMatchPattern inner
  | .ok "MatchOr" =>
      match patternJson.getObjValAs? (Array Json) "patterns" with
      | .ok patterns => patterns.toList.all canLowerDirectMatchPattern
      | _ => false
  | .ok "MatchSequence" =>
      match patternJson.getObjValAs? (Array Json) "patterns" with
      | .ok patterns => patterns.size == 2 && patterns.toList.all canLowerDirectMatchPattern
      | _ => false
  | _ => false

/-- Check whether a case can use direct Lean `match` lowering instead of the `if` fallback. -/
def canLowerDirectMatchCase (caseJson : Json) : Bool :=
  match caseJson.getObjValAs? Json "pattern", jsonFieldOption caseJson "guard" with
  | .ok patternJson, none => canLowerDirectMatchPattern patternJson
  | _, _ => false

/-- Use direct Lean `match` syntax when every case is an unguarded structural pattern we know how to lower. -/
def canUseDirectLeanMatch (cases : List Json) : Bool :=
  !cases.isEmpty && cases.all canLowerDirectMatchCase

/-- Build the cartesian product of tuple subpatterns when lowering `MatchSequence`. -/
def tuplePatternProducts (lhs rhs : Array (TSyntax `term)) : PygenM (Array (TSyntax `term)) := do
  let mut out := #[]
  for l in lhs do
    for r in rhs do
      out := out.push (← `(term| ($l, $r)))
  return out

/-- Expand a Python pattern into one or more direct Lean patterns. `MatchOr` becomes several branches. -/
partial def directLeanMatchPatterns (patternJson : Json) : PygenM (Array (TSyntax `term)) := do
  let nodeType ← matchPatternNodeType patternJson
  match nodeType with
  | "MatchValue" =>
      let .ok valueJson := patternJson.getObjValAs? Json "value" | throwError
        s!"MatchValue node is missing a 'value' field: {patternJson}"
      return #[← getCode valueJson `term]
  | "MatchSingleton" =>
      let .ok valueJson := patternJson.getObjValAs? Json "value" | throwError
        s!"MatchSingleton node is missing a 'value' field: {patternJson}"
      return #[← getCode (Json.mkObj [("node_type", Json.str "Constant"), ("value", valueJson)]) `term]
  | "MatchAs" =>
      let name? := patternJson.getObjValAs? String "name" |>.toOption
      let pattern? := jsonFieldOption patternJson "pattern"
      match pattern?, name? with
      | none, none =>
          return #[← `(term| _)]
      | none, some name =>
          return #[mkIdent name.toName]
      | some inner, none =>
          directLeanMatchPatterns inner
      | some _, some _ =>
          throwError "Aliased match patterns are not yet supported in direct Lean match lowering."
  | "MatchOr" =>
      let .ok patternsJson := patternJson.getObjValAs? (Array Json) "patterns" | throwError
        s!"MatchOr node is missing a 'patterns' field: {patternJson}"
      let mut out := #[]
      for alt in patternsJson do
        out := out ++ (← directLeanMatchPatterns alt)
      return out
  | "MatchSequence" =>
      let .ok patternsJson := patternJson.getObjValAs? (Array Json) "patterns" | throwError
        s!"MatchSequence node is missing a 'patterns' field: {patternJson}"
      unless patternsJson.size == 2 do
        throwError "Only 2-element MatchSequence patterns are currently supported."
      let lhs ← directLeanMatchPatterns patternsJson[0]!
      let rhs ← directLeanMatchPatterns patternsJson[1]!
      tuplePatternProducts lhs rhs
  | _ =>
      throwError s!"Pattern node type {nodeType} is not supported for direct Lean match lowering."

/-- Build one pure Lean match alternative from a Python case body. -/
def directLeanMatchTermAlt (pattern : TSyntax `term) (bodyElemsJson : Array Json) (rest : List Json) :
    PygenM (TSyntax `Lean.Parser.Term.matchAlt) := do
  let bodyTerm ← matchSplitListOrPureUnit (bodyElemsJson.toList ++ rest)
  `(matchAltExpr| | $pattern:term => $bodyTerm)

/-- Lower a Python `match` into a direct Lean `match` term when the patterns are simple enough. -/
def directLeanMatchTermSyntax (subject : TSyntax `term) (cases : List Json) (rest : List Json) :
    PygenM (TSyntax `term) := do
  let mut alts : Array (TSyntax `Lean.Parser.Term.matchAlt) := #[]
  let mut exhaustive := false
  for caseJson in cases do
    let .ok patternJson := caseJson.getObjValAs? Json "pattern" | throwError
      s!"match_case node does not have a 'pattern' field: {caseJson}"
    let .ok bodyElemsJson := caseJson.getObjValAs? (Array Json) "body" | throwError
      s!"match_case node does not have a 'body' field: {caseJson}"
    let patterns ← directLeanMatchPatterns patternJson
    for pattern in patterns do
      alts := alts.push (← directLeanMatchTermAlt pattern bodyElemsJson rest)
    if isIrrefutableMatchPattern patternJson then
      exhaustive := true
  if !exhaustive then
    let fallbackBody ← matchSplitListOrPureUnit rest
    alts := alts.push (← `(matchAltExpr| | _ => $fallbackBody))
  `(term| match $subject:term with $alts:matchAlt*)

/-- Convert a match pattern into a boolean condition plus any names it binds. -/
partial def matchPatternConditionBindings (subject : TSyntax `term) (patternJson : Json) :
    PygenM (TSyntax `term × Array (TSyntax `ident × TSyntax `term)) := do
  let nodeType ← matchPatternNodeType patternJson
  match nodeType with
  | "MatchValue" =>
      let .ok valueJson := patternJson.getObjValAs? Json "value" | throwError
        s!"MatchValue node is missing a 'value' field: {patternJson}"
      let valueTerm ← getCode valueJson `term
      let cond ← `($subject == $valueTerm)
      return (cond, #[])
  | "MatchSingleton" =>
      let .ok valueJson := patternJson.getObjValAs? Json "value" | throwError
        s!"MatchSingleton node is missing a 'value' field: {patternJson}"
      let valueTerm ← getCode (Json.mkObj [("node_type", Json.str "Constant"), ("value", valueJson)]) `term
      let cond ← `($subject == $valueTerm)
      return (cond, #[])
  | "MatchAs" =>
      let name? := patternJson.getObjValAs? String "name" |>.toOption
      let pattern? := jsonFieldOption patternJson "pattern"
      match pattern? with
      | none =>
          let bindings := match name? with
            | some name => #[(mkIdent name.toName, subject)]
            | none => #[]
          return (trueTerm, bindings)
      | some innerPattern =>
          let (cond, bindings) ← matchPatternConditionBindings subject innerPattern
          let bindings := match name? with
            | some name => bindings.push (mkIdent name.toName, subject)
            | none => bindings
          return (cond, bindings)
  | "MatchOr" =>
      let .ok patternsJson := patternJson.getObjValAs? (Array Json) "patterns" | throwError
        s!"MatchOr node is missing a 'patterns' field: {patternJson}"
      let mut cond? : Option (TSyntax `term) := none
      for alt in patternsJson do
        let (altCond, altBindings) ← matchPatternConditionBindings subject alt
        unless altBindings.isEmpty do
          throwError "MatchOr patterns with variable bindings are not yet supported."
        cond? ← match cond? with
          | none => pure (some altCond)
          | some prev => pure (some (← orTerm prev altCond))
      return (cond?.getD falseTerm, #[])
  | "MatchSequence" =>
      let .ok patternsJson := patternJson.getObjValAs? (Array Json) "patterns" | throwError
        s!"MatchSequence node is missing a 'patterns' field: {patternJson}"
      unless patternsJson.size == 2 do
        throwError "Only 2-element MatchSequence patterns are currently supported."
      let fstTerm ← `(Prod.fst $subject)
      let sndTerm ← `(Prod.snd $subject)
      let (fstCond, fstBindings) ← matchPatternConditionBindings fstTerm patternsJson[0]!
      let (sndCond, sndBindings) ← matchPatternConditionBindings sndTerm patternsJson[1]!
      return (← andTerm fstCond sndCond, fstBindings ++ sndBindings)
  | "MatchStar" =>
      let name? := patternJson.getObjValAs? String "name" |>.toOption
      let bindings := match name? with
        | some name => #[(mkIdent name.toName, subject)]
        | none => #[]
      return (trueTerm, bindings)
  | "MatchClass" =>
      throwError "MatchClass patterns are not yet supported."
  | "MatchMapping" =>
      throwError "MatchMapping patterns are not yet supported."
  | _ =>
      throwError s!"Unsupported match pattern node type: {nodeType}"

/-- Lower a Python `match` statement into nested effectful `if` branches. -/
partial def matchCaseDoElemSyntax (subject : TSyntax `term) (cases : List Json) :
    PygenM (TSyntax `doElem) := do
  match cases with
  | [] => noopDoElemSyntax
  | caseJson :: restCases => do
      let .ok patternJson := caseJson.getObjValAs? Json "pattern" | throwError
        s!"match_case node does not have a 'pattern' field: {caseJson}"
      let guard? := jsonFieldOption caseJson "guard"
      let .ok bodyElemsJson := caseJson.getObjValAs? (Array Json) "body" | throwError
        s!"match_case node does not have a 'body' field: {caseJson}"
      let (cond, bindings) ← matchPatternConditionBindings subject patternJson
      let bindingElems ← matchBindingDoElems bindings
      let bodyElems ← monadicFunctionBodySyntax bodyElemsJson
      let noop ← noopDoElemSyntax
      let nextCase ← matchCaseDoElemSyntax subject restCases
      let branchBody ← match guard? with
        | none =>
            sequenceDoElems (bindingElems ++ bodyElems) noop
        | some guardJson =>
            let guardTerm ← getCode guardJson `term
            let successBody ← sequenceDoElems bodyElems noop
            let guardedBody ← sequenceDoElems bindingElems (← `(doElem| if $guardTerm then
                $successBody:doElem
              else
                $nextCase:doElem))
            pure guardedBody
      if restCases.isEmpty && guard?.isNone && isIrrefutableMatchPattern patternJson then
        pure branchBody
      else
        `(doElem| if $cond then
            $branchBody:doElem
          else
            $nextCase:doElem)

/-- Lower a Python `match` expression-ish head into nested pure `if` terms. -/
partial def matchCaseTermSyntax (subject : TSyntax `term) (cases : List Json) (rest : List Json) :
    PygenM (TSyntax `term) := do
  if !rest.isEmpty &&
      cases.any (fun caseJson =>
        match caseJson.getObjValAs? (Array Json) "body" with
        | .ok bodyElems => !statementListDefinitelyReturns bodyElems.toList
        | .error _ => true) then
    throwError
      "Match branches that fall through into later statements require monadic lowering."
  else if canUseDirectLeanMatch cases then
    directLeanMatchTermSyntax subject cases rest
  else
    match cases with
    | [] => matchSplitListOrPureUnit rest
    | caseJson :: restCases => do
        let .ok patternJson := caseJson.getObjValAs? Json "pattern" | throwError
          s!"match_case node does not have a 'pattern' field: {caseJson}"
        let guard? := jsonFieldOption caseJson "guard"
        let .ok bodyElemsJson := caseJson.getObjValAs? (Array Json) "body" | throwError
          s!"match_case node does not have a 'body' field: {caseJson}"
        let (cond, bindings) ← matchPatternConditionBindings subject patternJson
        let nextCase ← matchCaseTermSyntax subject restCases rest
        let caseBody ← matchSplitListOrPureUnit (bodyElemsJson.toList ++ rest)
        let branchBody ← match guard? with
          | none =>
              matchWrapBindingsTerm bindings caseBody
          | some guardJson =>
              let guardTerm ← getCode guardJson `term
              let guardedBody ← `(if $guardTerm then $caseBody else $nextCase)
              matchWrapBindingsTerm bindings guardedBody
        if restCases.isEmpty && guard?.isNone && isIrrefutableMatchPattern patternJson then
          pure branchBody
        else
          `(if $cond then $branchBody else $nextCase)

@[pygen "Match"]
def matchSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok subjectJson := json.getObjValAs? Json "subject" | throwError
          s!"Match node does not have a 'subject' field or it is not a JSON value: {json}"
        let .ok casesJson := json.getObjValAs? (Array Json) "cases" | throwError
          s!"Match node does not have a 'cases' field or it is not a JSON array: {json}"
        let subjectTerm ← getCode subjectJson `term
        matchCaseDoElemSyntax subjectTerm casesJson.toList
    | _, _ => throwError s!"Unsupported syntax category for Match node"

end PyAstLean
