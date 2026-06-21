import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term

def withFreshVariables {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField
    (·.varNames)
    (fun st varNames => { st with varNames := varNames })
    (HashSet.emptyWithCapacity 100)
    x

/--
Append one generated command into an accumulator, flattening null-node wrappers that
represent "many commands" or "no commands" from an earlier lowering pass.
-/
def appendCommandSyntax (cmds : Array (TSyntax `command)) (cmd : TSyntax `command) :
    Array (TSyntax `command) :=
  if cmd.raw.isOfKind nullKind then
    cmds ++ cmd.raw.getArgs.map (fun arg => ⟨arg⟩)
  else
    cmds.push cmd

/--
Append one generated `doElem` into an accumulator, flattening null-node wrappers that
represent "many doElems" from a lowering that produced several sibling statements (e.g.
tuple-unpack assignment). Flattening keeps the bindings as siblings in the enclosing `do`
rather than scoping them inside a nested `do` block.
-/
def appendDoElems (elems : Array (TSyntax `doElem)) (elem : TSyntax `doElem) :
    Array (TSyntax `doElem) :=
  if elem.raw.isOfKind nullKind then
    elems ++ elem.raw.getArgs.map (fun arg => ⟨arg⟩)
  else
    elems.push elem

/-- Pick a fresh local name for generated bindings. -/
partial def freshName (base : Name) (idx : Nat := 0) : PygenM Name := do
  let candidate :=
    if idx == 0 then base else base.appendIndexAfter idx
  if ← hasVar candidate then
    freshName base (idx + 1)
  else
    addVar candidate
    pure candidate

def isMainGuardTest (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Compare" =>
      match json.getObjValAs? String "op", json.getObjValAs? Json "left", json.getObjValAs? Json "right" with
      | .ok "eq", .ok leftJson, .ok rightJson =>
          match leftJson.getObjValAs? String "node_type", leftJson.getObjValAs? String "id",
              rightJson.getObjValAs? String "node_type", rightJson.getObjValAs? Json "value" with
          | .ok "Name", .ok "__name__", .ok "Constant", .ok (.str "__main__") => true
          | _, _, _, _ => false
      | _, _, _ => false
  | _ => false

/-- Detect a `range(...)` iterable, which is lowered directly to `pyRange` (already a `List Int`)
rather than being normalized through `pyIter`. The annotation pre-pass rewrites `range(...)`
calls to a dedicated `Range` node; a raw `Call` to `range` is also recognized defensively. -/
def isRangeIter (iterJson : Json) : Bool :=
  match iterJson.getObjValAs? String "node_type" with
  | .ok "Range" => true
  | .ok "Call" =>
      match iterJson.getObjValAs? Json "func" with
      | .ok funcJson =>
          funcJson.getObjValAs? String "node_type" == .ok "Name" &&
            funcJson.getObjValAs? String "id" == .ok "range"
      | _ => false
  | _ => false

/-- Lower a `for`/comprehension iterable to a Lean term that can be iterated as a `List`.

`range(...)` lowers directly to `pyRange` (already a `List Int`). Every other iterable is
normalized through `pyIter`, so the element type is governed uniformly by the `PyIterable`
instances: a `String` yields one-character `String`s, a `Std.HashMap` yields its keys, a `List`
is unchanged. This is what makes iteration over a string behave like Python (`for c in s` binds
length-1 strings, not `Char`s) and keeps loop bodies interoperable with string literals. -/
def rangeIterSyntax (iterJson : Json) : PygenM (TSyntax `term) := do
  let .ok iterNodeType := iterJson.getObjValAs? String "node_type" | throwError
    s!"For iterator is missing a node_type field: {iterJson}"
  if iterNodeType == "Range" then
    -- The pre-pass already produced a `Range` node; lower it straight to `pyRange`.
    getCode iterJson `term
  else if iterNodeType == "Call" &&
      (iterJson.getObjValAs? Json "func").toOption.any
        (fun f => f.getObjValAs? String "id" == .ok "range") then
    -- Defensive path for a raw `range(...)` call that escaped the pre-pass rewrite.
    let funcJson := (iterJson.getObjVal? "func").toOption.getD (Json.mkObj [])
    let argsJson := (iterJson.getObjVal? "args").toOption.getD (Json.arr #[])
    let keywordsJson := (iterJson.getObjVal? "keywords").toOption.getD (Json.mkObj [])
    let rangeJson := Json.mkObj [
      ("node_type", Json.str "Range"),
      ("func", funcJson),
      ("args", argsJson),
      ("keywords", keywordsJson)
    ]
    getCode rangeJson `term
  else
    `($(mkIdent ``pyIter) $(← getCode iterJson `term))

/-- Reusable syntax nodes for boolean literals in generated terms. -/
def trueTerm : TSyntax `term := mkIdent ``true

def falseTerm : TSyntax `term := mkIdent ``false

/-- Read the `node_type` tag from a JSON AST node when present. -/
def jsonNodeType? (json : Json) : Option String :=
  json.getObjValAs? String "node_type" |>.toOption

/--
Reformat a list of Json to an object with `node_type` the `node_type` of the original list's
first element with "Head_" prefixed, and `rest` the remaining statements.
-/
def splitList : List Json -> PygenM Json
| [] => throwError "Cannot split an empty list"
| (first :: rest) => do
    let .ok nodeType := first.getObjValAs? String "node_type" | throwError
      s!"First element of list does not have a 'node_type' field or it is not a string: {first}"
    let newNodeType := "Head_" ++ nodeType
    let newJson := first.mergeObj (Json.mkObj [("node_type", newNodeType), ("rest", toJson rest)])
    return newJson

/-- Try to compile a function body as one pure term by threading the remaining statements
through `Head_*` nodes. -/
def pureFunctionBodySyntax (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let spl ← splitList bodyElems.toList
  withoutCheck do
    getCode spl `term

mutual

/--
Check whether a statement list definitely returns on every path without needing any outer
continuation. This is used to decide whether nested control-flow can stay in the pure
threaded lowering, or whether we should fall back to the monadic statement path instead.
-/
partial def statementListDefinitelyReturns : List Json → Bool
| [] => false
| stmt :: rest =>
    if statementDefinitelyReturns stmt then
      true
    else
      statementListDefinitelyReturns rest

/-- Check whether one statement definitely returns on every path. -/
partial def statementDefinitelyReturns (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" => true
  | some "Raise" => true
  | some "If" =>
      match stmt.getObjValAs? (Array Json) "body", stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok orelseElems =>
          !orelseElems.isEmpty &&
            statementListDefinitelyReturns bodyElems.toList &&
            statementListDefinitelyReturns orelseElems.toList
      | _, _ => false
  | some "Try" =>
      match stmt.getObjValAs? (Array Json) "body",
          stmt.getObjValAs? (Array Json) "handlers",
          stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok handlerElems, .ok orelseElems =>
          let bodyReturns := statementListDefinitelyReturns (bodyElems.toList ++ orelseElems.toList)
          let handlersReturn :=
            handlerElems.toList.all fun handlerJson =>
              match handlerJson.getObjValAs? (Array Json) "body" with
              | .ok handlerBody => statementListDefinitelyReturns handlerBody.toList
              | .error _ => false
          bodyReturns && handlersReturn
      | _, _, _ => false
  | some "Match" =>
      match stmt.getObjValAs? (Array Json) "cases" with
      | .ok cases =>
          -- All cases must return AND the last case must be irrefutable (covers all inputs)
          let allCasesReturn := cases.toList.all fun caseJson =>
            match caseJson.getObjValAs? (Array Json) "body" with
            | .ok bodyElems => statementListDefinitelyReturns bodyElems.toList
            | .error _ => false
          let lastCaseExhaustive := match cases.toList.getLast? with
            | none => false
            | some lastCase =>
                let guardAbsent := match lastCase.getObjValAs? Json "guard" with
                  | .ok .null => true
                  | .error _ => true
                  | _ => false
                match guardAbsent, lastCase.getObjVal? "pattern" with
                | true, .ok patternJson =>
                    match patternJson.getObjValAs? String "node_type" with
                    | .ok "MatchAs" => true
                    | .ok "MatchStar" => true
                    | _ => false
                | _, _ => false
          allCasesReturn && lastCaseExhaustive
      | _ => false
  | _ => false

end

/-- Compile a function body statement-by-statement into `doElem`s for the monadic fallback path. -/
def monadicFunctionBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  for elem in bodyElems do
    let elemStx ← withoutCheck do
      getCode elem `doElem
    bodyStxArray := appendDoElems bodyStxArray elemStx
    if statementDefinitelyReturns elem then
      break
  return bodyStxArray

/-- Build a Lean conjunction term. -/
def andTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs && $rhs)

/-- Build a Lean disjunction term. -/
def orTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs || $rhs)

/-- Read an optional JSON field and treat explicit `null` the same as an absent value. -/
def jsonFieldOption (json : Json) (field : String) : Option Json :=
  match json.getObjValAs? Json field |>.toOption with
  | some .null => none
  | other => other

/-- Recursively check whether a JSON subtree contains any node type from `targets`. -/
partial def jsonContainsNodeType (json : Json) (targets : List String) : Bool :=
  let currentMatches :=
    match json.getObjValAs? String "node_type" with
    | .ok nodeType => targets.contains nodeType
    | .error _ => false
  if currentMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonContainsNodeType elem targets)
    | .obj fields => fields.toList.any (fun (_, value) => jsonContainsNodeType value targets)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated exceptions. -/
partial def jsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesExceptionEffect value)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated `IO` effects. -/
partial def jsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesIOEffect value)
    | _ => false

/-- Detect whether a statement list uses translated exceptions and therefore should not run under `Id`. -/
def bodyNeedsExceptionMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesExceptionEffect

/-- Detect whether a statement list uses translated `IO` effects and therefore should run under `IO`. -/
def bodyNeedsIOMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesIOEffect

/-- Values using either translated exceptions or translated `IO` require monadic binding in `do`. -/
def jsonUsesMonadicEffect (json : Json) : Bool :=
  jsonUsesExceptionEffect json || jsonUsesIOEffect json

/-- Sequence a list of `doElem`s into one `doElem`, using `fallback` for the empty case. -/
def sequenceDoElems (elems : Array (TSyntax `doElem)) (fallback : TSyntax `doElem) :
    PygenM (TSyntax `doElem) := do
  if elems.isEmpty then
    return fallback
  `(doElem| do
    $[$elems:doElem]*)

/-- Emit an explicit no-op statement inside `do` notation. -/
def noopDoElemSyntax : PygenM (TSyntax `doElem) := do
  `(doElem| let _ := ())

/--
A Python name is module-private when it starts with an underscore but is **not** a dunder.
This matches what `from module import *` excludes:

  - `foo`      → public
  - `_foo`     → private (single-underscore "internal use" convention)
  - `__foo`    → private (double underscore, no trailing — strong private / name-mangled)
  - `__foo__`  → public  (dunder: `__init__`, `__name__`, ... are the public protocol)

Private names map to a Lean `private def` so they cannot be imported from other modules.
-/
def pythonNameIsPrivate (name : String) : Bool :=
  name.startsWith "_"
    && name != "_"                                  -- bare `_` is the wildcard
    && !(name.startsWith "__" && name.endsWith "__") -- `__dunder__` is public

/-- Splice a `private` modifier into an existing `def`/declaration command.

`private` is a `declModifiers` prefix that the parser only accepts directly before a `def`
keyword, so we cannot wrap an already-built command. Instead we harvest the `private`
modifier node from a throwaway declaration and swap it into the target's `declModifiers`
slot (the first child of a `Command.declaration`). Non-declaration commands are unchanged. -/
def makeCommandPrivate (cmd : TSyntax `command) : PygenM (TSyntax `command) := do
  let template ← `(command| private def __PastaLean_priv_tmpl := ())
  let privMods := match template.raw with
    | .node _ ``Lean.Parser.Command.declaration #[mods, _] => mods
    | _ => Syntax.missing
  match cmd.raw with
  | .node info ``Lean.Parser.Command.declaration #[_oldMods, decl] =>
      return ⟨.node info ``Lean.Parser.Command.declaration #[privMods, decl]⟩
  | _ => return cmd

/--
Prefix a top-level `def` command with `private` when its Python `name` follows the
leading-underscore privacy convention, so it cannot be imported from other modules
(matching Python's intent). Names are otherwise preserved verbatim (`_foo` stays `_foo`).
Null-node command wrappers (multiple commands) are returned unchanged.
-/
def applyPrivacy (name : String) (cmd : TSyntax `command) : PygenM (TSyntax `command) := do
  if pythonNameIsPrivate name && !cmd.raw.isOfKind nullKind then
    makeCommandPrivate cmd
  else
    pure cmd

end PastaLean
