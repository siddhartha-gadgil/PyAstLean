import PyAstLean.PyGens.Core.Assign

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Lower a standalone Python expression statement inside `do` notation. -/
def exprStmtDoElemSyntax (valueJson : Json) : PygenM (TSyntax `doElem) := do
  try
    getCode valueJson `doElem
  catch _ =>
    let valueStx ← getCode valueJson `term
    `(doElem| let _ := $valueStx)

/-- Stable helper name for top-level expression statements lowered as commands. -/
def topLevelExprCommandIdent (json : Json) : TSyntax `ident :=
  mkIdent <| Name.mkSimple s!"__py_expr_{hash json |>.toNat}"

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
          let exceptIdent := mkIdent ``PyAstLean.PyExcept
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
        `(doElem| break)
    | _, _ => throwError s!"Unsupported syntax category for Break node"

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
              let floorDivIdent := mkIdent ``PyAstLean.pyFloorDiv
              `($floorDivIdent $curTerm $valueCode)
          -- AUGASSIGN_MAP spells bitwise ops `and`/`or`/`xor` (vs BINOP's `bitand`/...).
          | "and" => `($(mkIdent ``PyAstLean.pyBitAnd) $curTerm $valueCode)
          | "or" => `($(mkIdent ``PyAstLean.pyBitOr) $curTerm $valueCode)
          | "xor" => `($(mkIdent ``PyAstLean.pyBitXor) $curTerm $valueCode)
          | "lshift" => `($(mkIdent ``PyAstLean.pyShiftLeft) $curTerm $valueCode)
          | "rshift" => `($(mkIdent ``PyAstLean.pyShiftRight) $curTerm $valueCode)
          | _ => throwError s!"Unsupported augmented assignment operator: {op}"
        match ← subscriptTargetParts? targetJson with
        | some (containerIdent, indexTerm) =>
            -- `s[i] += v` rebuilds the container with the updated element.
            subscriptSetDoElem containerIdent indexTerm updated
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
            bodyStxArray := appendDoElems bodyStxArray elemStx
        `(doElem| while $testStx do
            $[$bodyStxArray:doElem]*)
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
        unless orelseElems.isEmpty do
          throwError "Python for-else blocks are not supported."
        let (targetIdent, preludeElems) ← forTargetBinder targetJson
        let iterCode ← rangeIterSyntax iterJson
        let mut bodyStxArray := preludeElems
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := appendDoElems bodyStxArray elemStx
        `(doElem| for $targetIdent:ident in $iterCode do
            $[$bodyStxArray:doElem]*)
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
        let testStx ← getCode testJson `term
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := appendDoElems bodyStxArray elemStx
        let mut orelseStxArray := #[]
        for elem in orelseElems do
          let elemStx ← getCode elem `doElem
          orelseStxArray := appendDoElems orelseStxArray elemStx
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
        let mainIdent := mkIdent `main
        if bodyNeedsExceptionMonad bodyElems then
          let exceptIdent := mkIdent ``PyAstLean.PyExcept
          let ioUserErrorIdent := mkIdent ``IO.userError
          `(command| def $mainIdent : IO Unit := do
              let result ← (((do
                  $[$bodyStxArray:doElem]*
                  pure ()
                ) : $exceptIdent Unit)).run
              match result with
              | .ok _ => pure ()
              | .error err => throw ($ioUserErrorIdent (toString err)))
        else if bodyNeedsIOMonad bodyElems then
          `(command| def $mainIdent : IO Unit := do
              $[$bodyStxArray:doElem]*
              pure ())
        else
          let idRunIdent := mkIdent ``Id.run
          `(command| def $mainIdent : IO Unit := do
              let _ := $idRunIdent do
                $[$bodyStxArray:doElem]*
              pure ())
    | _, _ => throwError s!"Unsupported syntax category for If node"


end PyAstLean
