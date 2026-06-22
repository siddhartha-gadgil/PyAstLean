import PastaLean.PyGens.Core.Assign

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Lower a standalone Python expression statement inside `do` notation. -/
def exprStmtDoElemSyntax (valueJson : Json) : PygenM (TSyntax `doElem) := do
  try
    getCode valueJson `doElem
  catch _ =>
    let valueStx ← getCode valueJson `term
    -- If the expression carries an effect (e.g. a statement-position ternary
    -- `print(a) if c else print(b)`, whose branches are `IO`), it must be *run*, not merely
    -- bound — `let _ := ioAction` discards the action unexecuted. Await it so the effect happens.
    if jsonUsesMonadicEffect valueJson then
      `(doElem| let _ ← $valueStx:term)
    else
      `(doElem| let _ := $valueStx)

/-- Stable helper name for top-level expression statements lowered as commands. The hash is
truncated to keep the generated name short while staying unique across the handful of top-level
expression statements in a module. -/
def topLevelExprCommandIdent (json : Json) : TSyntax `ident :=
  let h := (hash json).toNat % 1000000
  mkIdent <| Name.mkSimple s!"pyStmt_{h}"

@[pygen "Expr"]
def exprSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Expr node does not have a 'value' field or it is not a JSON value: {json}"
        exprStmtDoElemSyntax valueJson
    | `command, json => do
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Expr node does not have a 'value' field or it is not a JSON value: {json}"
        if jsonUsesExceptionEffect valueJson then
          let bodyElem ← exprStmtDoElemSyntax valueJson
          let exprIdent := topLevelExprCommandIdent json
          let exceptIdent := mkIdent ``PastaLean.PyExcept
          `(command| def $exprIdent : $exceptIdent Unit := do
              $bodyElem:doElem
              pure ())
        else if jsonUsesIOEffect valueJson then
          let bodyElem ← exprStmtDoElemSyntax valueJson
          let exprIdent := topLevelExprCommandIdent json
          let ioIdent := mkIdent ``IO
          `(command| def $exprIdent : $ioIdent Unit := do
              $bodyElem:doElem
              pure ())
        else
          pure ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Expr node"

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
        -- Inside a loop carrying a Python `else`, record that we broke so the `else` is skipped.
        match ← getBreakFlag with
        | some flag =>
            let flagIdent := mkIdent flag
            let setFlag ← `(doElem| $flagIdent:ident := true)
            let brk ← `(doElem| break)
            pure ⟨mkNullNode #[setFlag.raw, brk.raw]⟩
        | none => `(doElem| break)
    | _, _ => throwError s!"Unsupported syntax category for Break node"

@[pygen "AugAssign"]
def augAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => withRealIfMarked json do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"AugAssign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok op := json.getObjValAs? String "op" | throwError
          s!"AugAssign node does not have an 'op' field or it is not a string: {json}"
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"AugAssign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueCode ← getCode valueJson `term
        -- The current value: for a Name target this is the variable; for a subscript target
        -- `s[i]` it is the element read, so `s[i] += v` works on both.
        let curTerm ← getCode targetJson `term
        let updated ← match op with
          | "add" => `($curTerm +ₚ $valueCode)
          | "sub" => `($curTerm -ₚ $valueCode)
          | "mul" => `($curTerm *ₚ $valueCode)
          | "div" => `($curTerm /ₚ $valueCode)
          | "mod" => `($curTerm %ₚ $valueCode)
          | "pow" => `($curTerm ^ₚ $valueCode)
          | "floordiv" =>
              let floorDivIdent := mkIdent ``PastaLean.pyFloorDiv
              `($floorDivIdent $curTerm $valueCode)
          -- AUGASSIGN_MAP spells bitwise ops `and`/`or`/`xor` (vs BINOP's `bitand`/...).
          | "and" => `($(mkIdent ``PastaLean.pyBitAnd) $curTerm $valueCode)
          | "or" => `($(mkIdent ``PastaLean.pyBitOr) $curTerm $valueCode)
          | "xor" => `($(mkIdent ``PastaLean.pyBitXor) $curTerm $valueCode)
          | "lshift" => `($(mkIdent ``PastaLean.pyShiftLeft) $curTerm $valueCode)
          | "rshift" => `($(mkIdent ``PastaLean.pyShiftRight) $curTerm $valueCode)
          | _ => throwError s!"Unsupported augmented assignment operator: {op}"
        -- `self.X += v` inside a class method: `curTerm` already reads `self.X`, so rebuild
        -- `self` with the updated field (value semantics). Guarded on a mutable `self` in scope.
        if let some attr := selfAttrTarget? targetJson then
          if ← hasVar `self then
            return ← selfRecordUpdateDoElem attr updated
        match ← nestedSubscriptSetDoElem? targetJson updated with
        | some setStx =>
            -- `s[i] += v` (and nested `g[i][j] += v`) rebuild the container with the new element.
            pure setStx
        | none =>
            let targetIdent ← getCode targetJson `ident
            `(doElem| $targetIdent:ident := $updated)
    | _, _ => throwError s!"Unsupported syntax category for AugAssign node"

/-- Lower a for-loop target into a binder and optional destructuring prelude. -/
def forTargetBinder (targetJson : Json) :
    PygenM (TSyntax `ident × Array (TSyntax `doElem)) := do
  match jsonNodeType? targetJson with
  | some "Name" =>
      let targetIdent ← getCode targetJson `ident
      -- Lean forbids a `for` binder from shadowing an enclosing `let mut`. When Python reuses
      -- a name that is already a mutable variable in scope (`p = 2; ...; for p in ...:`), bind
      -- a fresh loop variable and assign it into the existing mutable, matching Python's rebind.
      if ← hasVar targetIdent.getId then
        let loopIdent := mkIdent (← freshName `__py_loop)
        let assign ← `(doElem| $targetIdent:ident := $loopIdent)
        pure (loopIdent, #[assign])
      else
        pure (targetIdent, #[])
  | some "Tuple" =>
      let .ok elts := targetJson.getObjValAs? (Array Json) "elts" | throwError
        s!"For-loop tuple target does not have an 'elts' field: {targetJson}"
      if elts.size < 2 then
        throwError "For-loop tuple target must have at least two elements."
      let mut idents := #[]
      for elt in elts do
        unless jsonNodeType? elt == some "Name" do
          throwError "Only Name targets are supported in for-loop tuple unpacking."
        idents := idents.push (← getCode elt `ident)
      let n := idents.size
      let pairIdent := mkIdent (← freshName `_pair)
      let mut prelude : Array (TSyntax `doElem) := #[]
      for i in List.range n do
        let acc ← tupleAccessTerm pairIdent i n
        prelude := prelude.push (← `(doElem| let $(idents[i]!) := $acc))
      pure (pairIdent, prelude)
  | _ =>
      throwError s!"Unsupported for-loop target: {targetJson}"

/-!
  Top-level state threading.

  Lean has no top-level statement execution, so a bare `for` at module scope cannot
  mutate a module global. The Python pre-pass annotates such a block with
  `mutated_names` (the names it reassigns) and `state_init` (the versioned
  initializer to read for each name's pre-block value). We lower the block to a
  fold that returns the updated names as a tuple, then re-export each name as a
  fresh top-level `def` — keeping translated top-level names reusable declarations
  rather than hiding them inside `main`.
-/

/-- Read the `mutated_names` annotation (sorted name list) from a top-level block. -/
def blockMutatedNames? (json : Json) : Option (Array String) :=
  match json.getObjValAs? (Array String) "mutated_names" with
  | .ok names => if names.isEmpty then none else some names
  | .error _ => none

/-- Read the `state_init` map entry: the versioned initializer identifier for `name`. -/
def blockStateInit (json : Json) (name : String) : PygenM (TSyntax `ident) := do
  let .ok initObj := json.getObjVal? "state_init" | throwError
    s!"Top-level block is missing a 'state_init' field: {json}"
  let .ok initName := initObj.getObjValAs? String name | throwError
    s!"state_init has no entry for mutated name '{name}': {initObj}"
  pure (mkIdent initName.toName)

/-- Name the generated result `def` after the block's `block_id` (a short, position-based,
name-independent hash) so distinct top-level blocks never collide — even two identical ones.
`kindPrefix` distinguishes the construct (`__py_for`, `__py_if`, ...). -/
def blockResultIdent (json : Json) (kindPrefix : String) : PygenM (TSyntax `ident) := do
  let .ok blockId := json.getObjValAs? String "block_id" | throwError
    s!"Top-level block is missing a 'block_id' field: {json}"
  pure (mkIdent (Name.mkSimple s!"{kindPrefix}_{blockId}"))

/-- Build the right-nested tuple term `(n0, (n1, n2))` from a list of idents. -/
partial def buildNameTuple (idents : Array (TSyntax `ident)) : PygenM (TSyntax `term) := do
  match idents.toList with
  | [] => `(())
  | [single] => `($single)
  | first :: rest => do
      let restTuple ← buildNameTuple rest.toArray
      `(($first, $restTuple))

/-- Read the re-export identifier for a mutated `name`: the clean `name` when this block
holds its final value, or a versioned (dead) name when a later assignment shadows it. -/
def blockReexportName (json : Json) (name : String) : String :=
  match json.getObjVal? "reexport_names" with
  | .ok obj =>
      match obj.getObjValAs? String name with
      | .ok reexport => reexport
      | .error _ => name
  | .error _ => name

/-- Re-export each mutated name as a fresh top-level `def` reading from the block's
result. A single name needs no projection; multiple names project the result tuple.
The re-export identifier comes from the block's `reexport_names` annotation so a shadowed
result (re-initialized later) gets a versioned name instead of colliding on the clean one. -/
def reexportCommands (json : Json) (resultIdent : TSyntax `ident) (names : Array String) :
    PygenM (Array (TSyntax `command)) := do
  let n := names.size
  if n == 1 then
    let nameIdent := mkIdent (blockReexportName json names[0]!).toName
    -- Privacy keys on the original Python name, not the (possibly versioned) re-export id.
    pure #[← applyPrivacy names[0]! (← `(command| def $nameIdent := $resultIdent))]
  else
    let mut cmds := #[]
    for i in List.range n do
      let nameIdent := mkIdent (blockReexportName json names[i]!).toName
      let acc ← tupleAccessTerm resultIdent i n
      cmds := cmds.push (← applyPrivacy names[i]! (← `(command| def $nameIdent := $acc)))
    pure cmds

/-- Build `mut` prelude bindings that bind each mutated `name` to its projection of
the accumulator identifier `sourceIdent` (the whole value for a single name). -/
def stateMutPrelude (sourceIdent : TSyntax `ident) (names : Array String) :
    PygenM (Array (TSyntax `doElem)) := do
  let n := names.size
  let mut elems : Array (TSyntax `doElem) := #[]
  if n == 1 then
    let nameIdent := mkIdent names[0]!.toName
    elems := elems.push (← `(doElem| let mut $nameIdent := $sourceIdent))
  else
    for i in List.range n do
      let nameIdent := mkIdent names[i]!.toName
      let acc ← tupleAccessTerm sourceIdent i n
      elems := elems.push (← `(doElem| let mut $nameIdent := $acc))
  pure elems

/-- Build `Id.run do <prelude>; <body>; return (names...)` for a state-threading block.
The body statements run through the existing `doElem` generators, so `Assign`/`AugAssign`
on the mutated names lower to reassignment of the `mut` locals. -/
def stateRunBlock (prelude : Array (TSyntax `doElem)) (bodyElems : Array Json)
    (names : Array String) : PygenM (TSyntax `term) := do
  let mut doElems := prelude
  for elem in bodyElems do
    doElems := appendDoElems doElems (← getCode elem `doElem)
  let returnTuple ← buildNameTuple (names.map (mkIdent ·.toName))
  doElems := doElems.push (← `(doElem| return $returnTuple))
  let idRunIdent := mkIdent ``Id.run
  `($idRunIdent do
      $[$doElems:doElem]*)

/-- Reject top-level state-threading blocks that carry I/O or exception effects.

These would need the block (and every re-exported name, transitively) to be lowered in
`IO`/`PyExcept` rather than the pure `Id.run`, which is not implemented yet. Lowering them
as pure would silently drop the effect, so we fail loudly instead. -/
def ensureTopLevelBlockIsPure (bodyElems : Array Json) (what : String) : PygenM Unit := do
  if bodyElems.any jsonUsesIOEffect then
    throwError "Top-level {what} that performs I/O (e.g. `print`/`input`) is not supported \
      yet; move it into a function or an `if __name__ == \"__main__\"` block."
  if bodyElems.any jsonUsesExceptionEffect then
    throwError "Top-level {what} that can raise (e.g. `raise`/`try`) is not supported yet; \
      move it into a function or an `if __name__ == \"__main__\"` block."

/-- Lower a top-level `for` block with state threading: emit `def __py_for := List.foldl
(fun state i => Id.run do ...) init iter`, then re-export the mutated names. -/
def topLevelForCommands (json : Json) (names : Array String) : PygenM (Array (TSyntax `command)) := do
  let .ok targetJson := json.getObjValAs? Json "target" | throwError
    s!"Top-level For is missing a 'target' field: {json}"
  let .ok iterJson := json.getObjValAs? Json "iter" | throwError
    s!"Top-level For is missing an 'iter' field: {json}"
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"Top-level For is missing a 'body' field: {json}"
  let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
    s!"Top-level For is missing an 'orelse' field: {json}"
  unless orelseElems.isEmpty do
    throwError "Top-level for-else blocks are not supported."
  ensureTopLevelBlockIsPure bodyElems "for-loop"
  let loopVarIdent ← match jsonNodeType? targetJson with
    | some "Name" => getCode targetJson `ident
    | _ => throwError "Only a simple Name loop target is supported in top-level for state threading."
  -- Initial accumulator: tuple of the versioned initializers.
  let initIdents ← names.mapM (blockStateInit json)
  let initTuple ← buildNameTuple initIdents
  -- Register the mutated names so body `Assign`/`AugAssign` lower to reassignment.
  for name in names do
    addVar name.toName
  -- Fold step: bind state names as `mut` from the accumulator, run the body, return tuple.
  let stateIdent := mkIdent (← freshName `_state)
  let prelude ← stateMutPrelude stateIdent names
  let foldBody ← stateRunBlock prelude bodyElems names
  let iterCode ← rangeIterSyntax iterJson
  let resultIdent ← blockResultIdent json "__py_for"
  let foldlIdent := mkIdent ``List.foldl
  let foldDef ← `(command|
    def $resultIdent := $foldlIdent (fun $stateIdent $loopVarIdent => $foldBody) $initTuple $iterCode)
  let reexports ← reexportCommands json resultIdent names
  pure (#[foldDef] ++ reexports)

/-- Lower a top-level single-statement block (`if`/`match`/`while`) with state threading.

Unlike `for`, there is no iterable to fold over: the block runs once. We emit
`def __py_block := Id.run do let mut n := n₀; ...; <stmt>; return (n...)` then re-export.
The block's own statement (the `if`/`match`/`while`) lowers through its existing `doElem`
generator, so branches, `orelse`, and nested mutation all work, and names absent from a
branch keep their initial value. -/
def topLevelStmtCommands (json : Json) (names : Array String) (kindPrefix : String)
    (label : String) : PygenM (Array (TSyntax `command)) := do
  ensureTopLevelBlockIsPure #[json] label
  -- Bind each mutated name as `mut` from its versioned initializer, then run the
  -- whole block statement and return the updated tuple.
  for name in names do
    addVar name.toName
  let mut prelude : Array (TSyntax `doElem) := #[]
  let n := names.size
  if n == 1 then
    let nameIdent := mkIdent names[0]!.toName
    let initIdent ← blockStateInit json names[0]!
    prelude := prelude.push (← `(doElem| let mut $nameIdent := $initIdent))
  else
    for name in names do
      let nameIdent := mkIdent name.toName
      let initIdent ← blockStateInit json name
      prelude := prelude.push (← `(doElem| let mut $nameIdent := $initIdent))
  -- The single block statement (this `json`) lowers through its `doElem` generator.
  let blockBody ← stateRunBlock prelude #[json] names
  let resultIdent ← blockResultIdent json kindPrefix
  let blockDef ← `(command| def $resultIdent := $blockBody)
  let reexports ← reexportCommands json resultIdent names
  pure (#[blockDef] ++ reexports)

/-- Wrap a lowered loop (`coreElems`) with Python `else`-clause handling. With no `else`
(`breakFlag?` is `none`) the loop's statements are emitted unchanged. Otherwise the break flag is
declared `let mut f := false` before the loop and the `else` body runs afterward guarded by
`if !f`, so it executes only when the loop completed without `break`. -/
def loopWithElseDoElem (breakFlag? : Option Name) (coreElems : Array (TSyntax `doElem))
    (orelseElems : Array Json) : PygenM (TSyntax `doElem) := do
  match breakFlag? with
  | none => pure ⟨mkNullNode (coreElems.map TSyntax.raw)⟩
  | some flag =>
      let flagIdent := mkIdent flag
      let initFlag ← `(doElem| let mut $flagIdent:ident := false)
      let elseStxArray ← withFixedVariables do
        let mut arr : Array (TSyntax `doElem) := #[]
        for elem in orelseElems do
          arr := appendDoElems arr (← getCode elem `doElem)
        pure arr
      let noop ← noopDoElemSyntax
      let elseCheck ← `(doElem| if (!$flagIdent) then
          $[$elseStxArray:doElem]*
        else
          $noop:doElem)
      pure ⟨mkNullNode (#[initFlag.raw] ++ coreElems.map TSyntax.raw ++ #[elseCheck.raw])⟩

@[pygen "While"]
def whileSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok test := json.getObjVal? "test" | throwError
          s!"While node does not have a 'test' field or it is not a JSON value: {json}"
        let testStx ← truthyConditionTerm test (← withPropCondition true (getCode test `term))
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"While node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"While node does not have an 'orelse' field or it is not a JSON array: {json}"
        -- Python `while … else`: the `else` runs iff the loop exited normally (test became false),
        -- not via `break`. Tracked with a flag set inside `break` (scoped via `withBreakFlag`).
        let breakFlag? ← if orelseElems.isEmpty then pure none
          else pure (some (← freshName `__py_broke))
        -- Scope the body's variable declarations to the loop (see the `for` case): names
        -- first bound in the body do not leak to the enclosing scope.
        let bodyStxArray ← withFixedVariables do withBreakFlag breakFlag? do
          let mut bodyStxArray := #[]
          for elem in bodyElems do
              let elemStx ← getCode elem `doElem
              bodyStxArray := appendDoElems bodyStxArray elemStx
          pure bodyStxArray
        -- Parenthesize the test so its last token never glues to the `do` keyword.
        let whileLoop ← `(doElem| while ($testStx) do
            $[$bodyStxArray:doElem]*)
        loopWithElseDoElem breakFlag? #[whileLoop] orelseElems
    | `command, json => do
        -- A top-level `while` that mutates module globals is a state transformer.
        -- It lowers like `if`/`match`: `Id.run do let mut n := n₀; while ...; return (n...)`.
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelStmtCommands json names "__py_while" "while-loop"
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none =>
            throwError "Top-level `while` is only supported when it mutates a module global \
              (state threading)."
    | _, _ => throwError s!"Unsupported syntax category for While node"

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
        -- Python `for … else`: the `else` runs iff the loop completed without `break`. Track that
        -- with a `let mut` flag set inside `break` (scoped to this loop via `withBreakFlag`).
        let breakFlag? ← if orelseElems.isEmpty then pure none
          else pure (some (← freshName `__py_broke))
        -- Scope the loop's target and body variable declarations to the loop: names first
        -- bound inside the body must not leak into the enclosing scope, so a later
        -- `x = ...` after the loop is emitted as a fresh `let mut` rather than a reassignment
        -- of a variable whose `let mut` was confined to the loop body (Python rebinds anyway).
        let (targetIdent, bodyStxArray) ← withFixedVariables do withBreakFlag breakFlag? do
          let (targetIdent, preludeElems) ← forTargetBinder targetJson
          let mut bodyStxArray := preludeElems
          for elem in bodyElems do
            let elemStx ← getCode elem `doElem
            bodyStxArray := appendDoElems bodyStxArray elemStx
          pure (targetIdent, bodyStxArray)
        -- Parenthesize the iterable so its last token never glues to the `do` keyword
        -- (e.g. an iterable ending in `none` would otherwise pretty-print as `nonedo`).
        let coreElems : Array (TSyntax `doElem) ←
          if jsonUsesIOEffect iterJson then
            -- The iterable is IO-derived (e.g. `range(int(input()))` → `IO (List Int)`, or
            -- `input()` → `IO String`). Await it once into a local, then iterate over the pure
            -- value — otherwise a raw `IO X` would flow into a pure position. The awaited value is
            -- normalized through `pyIter` (unless it is a `range`, already a `List Int`) so a
            -- string iterable binds one-character strings, matching the pure path.
            let rawIter ← getCode iterJson `term
            let itIdent := mkIdent (← freshName `__py_iter)
            let bindIt ← `(doElem| let $itIdent:ident ← $rawIter:term)
            let iterTerm ←
              if isRangeIter iterJson then pure (itIdent : TSyntax `term)
              else `($(mkIdent ``pyIter) $itIdent)
            let forLoop ← `(doElem| for $targetIdent:ident in ($iterTerm) do
                $[$bodyStxArray:doElem]*)
            pure #[bindIt, forLoop]
          else
            let iterCode ← rangeIterSyntax iterJson
            let forLoop ← `(doElem| for $targetIdent:ident in ($iterCode) do
                $[$bodyStxArray:doElem]*)
            pure #[forLoop]
        loopWithElseDoElem breakFlag? coreElems orelseElems
    | `command, json => do
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelForCommands json names
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none =>
            throwError "Top-level `for` without state threading is not supported; \
              a top-level loop must mutate at least one module global."
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
        -- Lower the test in condition position so a direct comparison may be a provable `Prop`
        -- (paired with the `if h : …` hypothesis below); `and`/`or`/`not` reset this to `Bool`.
        let testStx ← truthyConditionTerm testJson (← withPropCondition true (getCode testJson `term))
        -- Hoist names that are first bound inside a branch but escape the `if` (read after it).
        -- Each branch lowers to its own `do` block, so a `let mut` there is invisible to the
        -- other branch and to following statements. Pre-declaring `let mut name := default`
        -- before the `if` (and registering it) turns both branch assignments into reassignments
        -- of one enclosing-scope variable, matching Python's cross-branch binding. Only names
        -- the pre-pass found to escape are listed; branch-local names keep their per-branch scope.
        let assignedNames :=
          (json.getObjValAs? (Array String) "if_assigned_names").toOption.getD #[]
        let mut hoistDecls : Array (TSyntax `doElem) := #[]
        for nm in assignedNames do
          let nmName := nm.toName
          unless (← hasVar nmName) do
            let nmIdent := mkIdent nmName
            hoistDecls := hoistDecls.push (← `(doElem| let mut $nmIdent:ident := default))
            addVar nmName
        -- Bind the branch condition as a hypothesis (`if h : cond then …`), so proofs about the
        -- generated code have the test available: `h` in the then-branch, `¬h` in the else.
        -- Reserve the name *before* lowering the branch bodies: `freshName` registers it, so a
        -- nested `if` inside the body gets `h_1` (not another `h`) and the outer hypothesis stays
        -- visible inside the nested branch instead of being shadowed. (`withFixedVariables` below
        -- restores per-branch scope, which is why the reservation must happen out here first.)
        let hName := mkIdent (← freshName `h)
        -- Scope each branch's variable declarations to that branch: a name first bound in the
        -- `then` branch must not leak into the `else` branch's scope (which would make the `else`
        -- assignment a reassignment of a `let mut` it cannot see). Names that escape the whole
        -- `if` are handled by the hoist above; everything else stays branch-local.
        let bodyStxArray ← withFixedVariables do
          let mut arr : Array (TSyntax `doElem) := #[]
          for elem in bodyElems do
            arr := appendDoElems arr (← getCode elem `doElem)
          pure arr
        let orelseStxArray ← withFixedVariables do
          let mut arr : Array (TSyntax `doElem) := #[]
          for elem in orelseElems do
            arr := appendDoElems arr (← getCode elem `doElem)
          pure arr
        let ifStx ←
          if orelseStxArray.isEmpty then
            let noop ← noopDoElemSyntax
            `(doElem| if $hName : $testStx then
                $[$bodyStxArray:doElem]*
              else
                $noop:doElem
            )
          else
            `(doElem| if $hName : $testStx then
                $[$bodyStxArray:doElem]*
              else
                $[$orelseStxArray:doElem]*)
        if hoistDecls.isEmpty then
          pure ifStx
        else
          pure ⟨mkNullNode ((hoistDecls.push ifStx).map TSyntax.raw)⟩
    | `command, json => do
        -- A top-level `if` that mutates module globals is a state transformer.
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelStmtCommands json names "__py_if" "if-block"
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none => pure ()
        -- Otherwise, the only supported top-level `if` is the `__main__` guard, which
        -- becomes Lean's `main` entry point.
        let isGuard := json.getObjValAs? Bool "is_main_guard" |>.toOption.getD false
        unless isGuard do
          throwError "A top-level `if` must either mutate a module global \
            (state threading) or be an `if __name__ == \"__main__\"` guard."
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := appendDoElems bodyStxArray elemStx
        -- Run-twin (`--mode both`): the entry wrapper is emitted as `main'rn` (and its body call to
        -- `main'` is suffixed to `main''rn` by the Name pygen), leaving the prove `main` as the file's
        -- single Lean entry point.
        let mainIdent := mkIdent (← withRunSuffix "main").toName
        -- A guard that calls into a real-valued (`ℝ`, exact mode) function makes the `main`
        -- wrapper depend on a `noncomputable` def, so it must itself be `noncomputable` (it
        -- still elaborates / compile-checks; it just can't be run — use `--approx` to run).
        let isReal := (← getNumericMode) == .exact && json.getObjValAs? Bool "_real_fn" == .ok true
        let mkMain : TSyntax `term → PygenM (TSyntax `command) := fun body =>
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $body)
          else `(command| def $mainIdent : IO Unit := $body)
        if bodyNeedsExceptionMonad bodyElems then
          let exceptIdent := mkIdent ``PastaLean.PyExcept
          let ioUserErrorIdent := mkIdent ``IO.userError
          mkMain (← `(do
              let result ← (((do
                  $[$bodyStxArray:doElem]*
                  pure ()
                ) : $exceptIdent Unit)).run
              match result with
              | .ok _ => pure ()
              | .error err => throw ($ioUserErrorIdent (toString err))))
        else if bodyNeedsIOMonad bodyElems then
          mkMain (← `(do
              $[$bodyStxArray:doElem]*
              pure ()))
        else
          let idRunIdent := mkIdent ``Id.run
          mkMain (← `(do
              let _ := $idRunIdent do
                $[$bodyStxArray:doElem]*
              pure ()))
    | _, _ => throwError s!"Unsupported syntax category for If node"


end PastaLean
