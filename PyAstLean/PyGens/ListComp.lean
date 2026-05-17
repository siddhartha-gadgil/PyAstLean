import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Pick a fresh local name for generated comprehension destructuring. -/
partial def freshListCompName (base : Name) (idx : Nat := 0) : PygenM Name := do
  let candidate :=
    if idx == 0 then base else base.appendIndexAfter idx
  if ← hasVar candidate then
    freshListCompName base (idx + 1)
  else
    addVar candidate
    pure candidate

/-- Build a lambda binder for a comprehension target. Simple tuple unpacking is lowered with an
intermediate pair binding so later clauses can use the unpacked names. -/
partial def listCompTargetLambda (targetJson : Json) (body : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match jsonNodeType? targetJson with
  | some "Name" =>
      let targetIdent ← getCode targetJson `ident
      `(fun $targetIdent => $body)
  | some "Tuple" =>
      let .ok elts := targetJson.getObjValAs? (Array Json) "elts" | throwError
        s!"Tuple comprehension target does not have an 'elts' field: {targetJson}"
      match elts[0]?, elts[1]? with
      | some leftJson, some rightJson =>
          let leftIdent ← getCode leftJson `ident
          let rightIdent ← getCode rightJson `ident
          let pairIdent := mkIdent (← freshListCompName `_pair)
          `(fun $pairIdent =>
              let ($leftIdent, $rightIdent) := $pairIdent
              $body)
      | _, _ =>
          throwError "Only two-element tuple unpacking targets are supported in comprehensions."
  | _ =>
      throwError s!"Unsupported comprehension target: {targetJson}"

/-- Filter a generator iterable through all of its `if` clauses, after normalizing it via `pyIter`. -/
def comprehensionIterSyntax (compJson : Json) : PygenM (TSyntax `term) := do
  let .ok targetJson := compJson.getObjValAs? Json "target" | throwError
    s!"comprehension node does not have a 'target' field: {compJson}"
  let .ok iterJson := compJson.getObjValAs? Json "iter" | throwError
    s!"comprehension node does not have an 'iter' field: {compJson}"
  let .ok ifsJson := compJson.getObjValAs? Json "ifs" | throwError
    s!"comprehension node does not have an 'ifs' field: {compJson}"
  let rawIterCode ← getCode iterJson `term
  let iterCode ←
    match jsonNodeType? iterJson with
    | some "BinOp" => do
        let pyIterIdent := mkIdent ``pyIter
        `($pyIterIdent $rawIterCode)
    | some "Constant" => do
        let pyIterIdent := mkIdent ``pyIter
        `($pyIterIdent $rawIterCode)
    | _ => pure rawIterCode
  let ifTerms ← match ifsJson with
    | .arr arr => arr.mapM (fun ifJson => getCode ifJson `term)
    | _ => throwError s!"comprehension node 'ifs' field is not an array: {ifsJson}"
  if ifTerms.isEmpty then
    pure iterCode
  else
    let mut predicate := ifTerms[0]!
    for ifTerm in ifTerms.toList.drop 1 do
      predicate ← `($predicate && $ifTerm)
    let predicateLambda ← listCompTargetLambda targetJson predicate
    `(List.filter $predicateLambda $iterCode)

/-- Recursively lower a Python list/generator comprehension through all generators. -/
partial def lowerComprehensionClauses (eltJson : Json) (generators : List Json) :
    PygenM (TSyntax `term) := do
  match generators with
  | [] =>
      let eltCode ← getCode eltJson `term
      `([$eltCode])
  | compJson :: rest => do
      let .ok targetJson := compJson.getObjValAs? Json "target" | throwError
        s!"comprehension node does not have a 'target' field: {compJson}"
      let iterCode ← comprehensionIterSyntax compJson
      if rest.isEmpty then
        let eltCode ← getCode eltJson `term
        let mapper ← listCompTargetLambda targetJson eltCode
        `(List.map $mapper $iterCode)
      else
        let nested ← lowerComprehensionClauses eltJson rest
        let binder ← listCompTargetLambda targetJson nested
        let flatMapIdent := mkIdent ``List.flatMap
        `($flatMapIdent $binder $iterCode)

@[pygen "ListComp"]
def listCompSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
      let .ok eltJson := json.getObjValAs? Json "elt" | throwError
        s!"ListComp node does not have an 'elt' field: {json}"
      let .ok generatorsJson := json.getObjValAs? Json "generators" | throwError
        s!"ListComp node does not have a 'generators' field: {json}"
      match generatorsJson with
      | .arr arr => lowerComprehensionClauses eltJson arr.toList
      | _ => throwError s!"ListComp node 'generators' field is not an array: {generatorsJson}"
  | _, _ => throwError s!"Unsupported syntax category for ListComp node"

@[pygen "GeneratorExp"]
def generatorExpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => listCompSyntax `term json
  | _, _ => throwError s!"Unsupported syntax category for GeneratorExp node"

@[pygen "Range"]
def rangeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Range node does not have an 'args' field: {json}"
      let argCodes ← match argsJson with
        | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
        | _ => throwError s!"Range node 'args' field is not an array: {argsJson}"
      let pyRangeIdent := mkIdent ``pyRange
      match argCodes.size with
      | 1 => `($pyRangeIdent $(argCodes[0]!))
      | 2 => `($pyRangeIdent $(argCodes[1]!) $(argCodes[0]!))
      | 3 => `($pyRangeIdent $(argCodes[1]!) $(argCodes[0]!) $(argCodes[2]!))
      | _ => throwError "range expects between one and three positional arguments."
  | _, _ => throwError s!"Unsupported syntax category for Range node"

end PyAstLean
