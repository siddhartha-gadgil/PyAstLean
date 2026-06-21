import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Core.Assign

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Build a lambda binder for a comprehension target. Tuple unpacking is lowered with
intermediate pair bindings so later clauses can use the unpacked names. -/
def listCompTargetLambda (targetJson : Json) (body : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match jsonNodeType? targetJson with
  | some "Name" =>
      let targetIdent ← getCode targetJson `ident
      `(fun $targetIdent => $body)
  | some "Tuple" =>
      let .ok elts := targetJson.getObjValAs? (Array Json) "elts" | throwError
        s!"Tuple comprehension target does not have an 'elts' field: {targetJson}"
      if elts.size < 2 then
        throwError "Tuple comprehension target must have at least two elements."
      let mut idents := #[]
      for elt in elts do
        unless jsonNodeType? elt == some "Name" do
          throwError "Only Name targets are supported in tuple comprehension unpacking."
        idents := idents.push (← getCode elt `ident)
      let n := idents.size
      let pairIdent := mkIdent (← freshName `_pair)
      let mut result := body
      for i in (List.range n).reverse do
        let acc ← tupleAccessTerm pairIdent i n
        result ← `(let $(idents[i]!) := $acc; $result)
      `(fun $pairIdent => $result)
  | _ =>
      throwError s!"Unsupported comprehension target: {targetJson}"

/-- Apply a comprehension generator's `pyIter` normalization and `if`-clause filters to an
already-lowered base iterable term `baseIter`. Factored out so the same logic applies whether
the iterable is pure or has been awaited from an `IO` action. -/
def comprehensionFilterOver (compJson : Json) (baseIter : TSyntax `term) : PygenM (TSyntax `term) := do
  let .ok targetJson := compJson.getObjValAs? Json "target" | throwError
    s!"comprehension node does not have a 'target' field: {compJson}"
  let .ok iterJson := compJson.getObjValAs? Json "iter" | throwError
    s!"comprehension node does not have an 'iter' field: {compJson}"
  let .ok ifsJson := compJson.getObjValAs? Json "ifs" | throwError
    s!"comprehension node does not have an 'ifs' field: {compJson}"
  -- Normalize the iterable through `pyIter` so `List.map`/`filter`/`flatMap` always receive a
  -- `List` and the element type is governed uniformly by the `PyIterable` instances (a string
  -- yields one-character strings, a dict yields keys). `range(...)` already lowers to a
  -- `List Int`, so it is passed through directly.
  let iterCode ←
    if isRangeIter iterJson then pure baseIter
    else `($(mkIdent ``pyIter) $baseIter)
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

/-- Filter a generator iterable through all of its `if` clauses, after normalizing it via `pyIter`. -/
def comprehensionIterSyntax (compJson : Json) : PygenM (TSyntax `term) := do
  let .ok iterJson := compJson.getObjValAs? Json "iter" | throwError
    s!"comprehension node does not have an 'iter' field: {compJson}"
  comprehensionFilterOver compJson (← getCode iterJson `term)

/-- Recursively lower a Python list/generator comprehension through all generators. -/
def lowerComprehensionClauses (eltJson : Json) (generators : List Json) :
    PygenM (TSyntax `term) := do
  match generators with
  | [] =>
      let eltCode ← getCode eltJson `term
      `([$eltCode])
  | compJson :: rest => do
      let .ok targetJson := compJson.getObjValAs? Json "target" | throwError
        s!"comprehension node does not have a 'target' field: {compJson}"
      let .ok iterJson := compJson.getObjValAs? Json "iter" | throwError
        s!"comprehension node does not have an 'iter' field: {compJson}"
      if rest.isEmpty then
        let eltCode ← getCode eltJson `term
        let mapper ← listCompTargetLambda targetJson eltCode
        let mapMethod := if jsonUsesMonadicEffect eltJson then mkIdent `mapM else mkIdent `map
        -- `[f(x) for x in input().split()]`: the iterable is IO. Lower it with an inline `←`
        -- (the codebase's convention for IO values), which binds in the enclosing `do`, so the
        -- map/filter run over the awaited `List` rather than a raw `IO (List _)`.
        let baseIter ←
          if jsonUsesIOEffect iterJson then inlineIOTerm iterJson
          else getCode iterJson `term
        let filtered ← comprehensionFilterOver compJson baseIter
        -- Emit dot-form `iterable.map (fun x => …)` so the iterable (whose element type is known,
        -- e.g. `List ℤ`) elaborates first and *binds* the lambda's parameter type. With the
        -- prefix form `List.map (fun x => …) iterable`, an operator default-instance (e.g. the
        -- `Rat` default on `*ₚ`) would prematurely pin the unconstrained `x` to `ℚ`, forcing
        -- `pyIter a` to yield `ℚ` and failing against `List ℤ`.
        `(($filtered).$mapMethod:ident $mapper)
      else
        let iterCode ← comprehensionIterSyntax compJson
        let nested ← lowerComprehensionClauses eltJson rest
        let binder ← listCompTargetLambda targetJson nested
        -- Dot-form `iterable.flatMap (fun x => …)` (not prefix `List.flatMap (fun x => …) iterable`)
        -- so the iterable's known element type binds the lambda parameter before an operator
        -- default-instance (e.g. the `Rat` default on `*ₚ`) can pin it — same fix as the `.map`
        -- path above, needed for multi-clause comprehensions like `[x*y for x in xs for y in ys]`.
        `(($iterCode).flatMap $binder)

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

@[pygen "SetComp"]
def setCompSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
      -- A set comprehension lowers exactly like a list comprehension, then the resulting list is
      -- deduplicated into the (list-backed) set runtime, matching `{f(x) for x in …}`.
      let .ok eltJson := json.getObjValAs? Json "elt" | throwError
        s!"SetComp node does not have an 'elt' field: {json}"
      let .ok generatorsJson := json.getObjValAs? (Array Json) "generators" | throwError
        s!"SetComp node does not have a 'generators' field: {json}"
      let listCode ← lowerComprehensionClauses eltJson generatorsJson.toList
      `($(mkIdent ``PastaLean.pySetFromList) $listCode)
  | _, _ => throwError s!"Unsupported syntax category for SetComp node"

@[pygen "DictComp"]
def dictCompSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
      -- A dict comprehension `{k: v for x in …}` lowers like a list comprehension whose element
      -- is the pair `(k, v)`, producing a `List (κ × ν)`, then builds a hash map from the pairs
      -- (later keys overwrite earlier ones, matching Python).
      let .ok keyJson := json.getObjValAs? Json "key" | throwError
        s!"DictComp node does not have a 'key' field: {json}"
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"DictComp node does not have a 'value' field: {json}"
      let .ok generatorsJson := json.getObjValAs? (Array Json) "generators" | throwError
        s!"DictComp node does not have a 'generators' field: {json}"
      -- Synthesize a `(key, value)` tuple element and reuse the list-comprehension lowering.
      let pairElt := Json.mkObj [("node_type", Json.str "Tuple"),
        ("elts", Json.arr #[keyJson, valueJson])]
      let pairsCode ← lowerComprehensionClauses pairElt generatorsJson.toList
      `($(mkIdent ``Std.HashMap.ofList) $pairsCode)
  | _, _ => throwError s!"Unsupported syntax category for DictComp node"

@[pygen "Range"]
def rangeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
      let .ok argsArray := json.getObjValAs? (Array Json) "args" | throwError
        s!"Range node does not have an 'args' field or it is not a JSON array: {json}"
      let argCodes ← argsArray.mapM (fun argJson => getCode argJson `term)
      let pyRangeIdent := mkIdent ``pyRange
      let mkRange : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
        match resolved.size with
        | 1 => `($pyRangeIdent $(resolved[0]!))
        | 2 => `($pyRangeIdent $(resolved[1]!) $(resolved[0]!))
        | 3 => `($pyRangeIdent $(resolved[1]!) $(resolved[0]!) $(resolved[2]!))
        | _ => throwError "range expects between one and three positional arguments."
      -- `range(int(input()))` has an IO argument; lift the whole call into `IO (List Int)`
      -- by awaiting the argument, so the iterable can be bound with `←` instead of passing a
      -- raw `IO Int` to `pyRange`.
      if argsArray.any basicJsonUsesIOEffect then
        buildIOPureApplicationFromArgs argsArray argCodes mkRange
      else
        mkRange argCodes
  | _, _ => throwError s!"Unsupported syntax category for Range node"

end PastaLean
