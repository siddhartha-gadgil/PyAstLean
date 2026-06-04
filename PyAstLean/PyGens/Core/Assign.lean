import PyAstLean.PyGens.Core.Utils
import PyAstLean.PyGens.Calls.CallEffects

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Read all Name idents from a tuple assignment target (any arity ≥ 2). -/
def tupleAssignTargetNames? (target : Json) : PygenM (Option (Array (TSyntax `ident))) := do
  unless jsonNodeType? target == some "Tuple" do
    return none
  let .ok elts := target.getObjValAs? (Array Json) "elts" | throwError
    s!"Tuple assignment target does not have an 'elts' field or it is not a JSON value: {target}"
  if elts.size < 2 then
    throwError "Tuple assignment target must have at least two elements."
  let mut idents := #[]
  for elt in elts do
    unless jsonNodeType? elt == some "Name" do
      throwError "Only Name targets are supported in tuple assignment."
    idents := idents.push (← getCode elt `ident)
  return some idents

/-- Build the accessor term to reach element `idx` of an N-element right-nested pair `pairIdent`.
`buildTuple` produces `(e0, (e1, (e2, e3)))`, so:
  - element 0 → `Prod.fst p`
  - element 1 → `Prod.fst (Prod.snd p)`
  - element N-2 → `Prod.fst (Prod.snd^(N-2) p)`
  - element N-1 → `Prod.snd^(N-1) p` -/
def tupleAccessTerm (pairIdent : TSyntax `ident) (idx n : Nat) : PygenM (TSyntax `term) := do
  let fstIdent := mkIdent ``Prod.fst
  let sndIdent := mkIdent ``Prod.snd
  let mut base : TSyntax `term := mkIdent pairIdent.getId
  for _ in List.range idx do
    base ← `($sndIdent $base)
  if idx == n - 1 then
    pure base
  else
    `($fstIdent $base)

/-- Build the accessor to reach element `idx` of an unpack source.

Python unpacking (`a, b, c = rhs`) iterates the RHS, but our two runtime shapes need different
accessors: a tuple *literal* RHS builds a right-nested `Prod` (so use `Prod.fst`/`Prod.snd`),
while anything else (a `list`, a `map(...)`/`split()` result, a variable) is a `List` (so index
with `pyListGetItem`). `isTuple` selects which. -/
def unpackAccessTerm (isTuple : Bool) (sourceIdent : TSyntax `ident) (idx n : Nat) :
    PygenM (TSyntax `term) := do
  if isTuple then
    tupleAccessTerm sourceIdent idx n
  else
    let getIdent := mkIdent ``PyAstLean.pyListGetItem
    let idxStx ← intToStx (Int.ofNat idx)
    `($getIdent $sourceIdent $idxStx)

/-- Emit either a fresh `let mut` or a reassignment for one local binding. -/
def bindOrAssignLocal (nameIdent : TSyntax `ident) (rhs : TSyntax `term) : PygenM (TSyntax `doElem) := do
  if ← hasVar nameIdent.getId then
    `(doElem| $nameIdent:ident := $rhs)
  else
    let stx ← `(doElem| let mut $nameIdent:ident := $rhs)
    addVar nameIdent.getId
    pure stx

/-- Normalize Python-style two-target unpacking through the iterable protocol. -/
def unpack2Term (value : TSyntax `term) : PygenM (TSyntax `term) := do
  let pyUnpack2Ident := mkIdent ``PyAstLean.pyUnpack2
  `($pyUnpack2Ident $value)

/-- Recognize a single-level subscript assignment target `name[index]`, returning the
container ident (the `mut` variable to rebuild) and the index term. Returns `none` for
non-subscript targets; throws a clear error for unsupported subscript shapes (nested
subscripts, non-Name containers, slice targets). -/
def subscriptTargetParts? (target : Json) : PygenM (Option (TSyntax `ident × TSyntax `term)) := do
  unless jsonNodeType? target == some "Subscript" do
    return none
  let .ok containerJson := target.getObjValAs? Json "value" | throwError
    s!"Subscript assignment target is missing a 'value' field: {target}"
  let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
    s!"Subscript assignment target is missing a 'slice' field: {target}"
  -- Slice targets (`s[a:b] = ...`) are item-list replacement, handled by `sliceTargetParts?`.
  if jsonNodeType? sliceJson == some "Slice" then
    return none
  unless jsonNodeType? containerJson == some "Name" do
    throwError "Only `name[index] = ...` subscript assignment (single-level, Name container) \
      is supported."
  let containerIdent ← getCode containerJson `ident
  let indexTerm ← getCode sliceJson `term
  return some (containerIdent, indexTerm)

/-- Emit `container := pySetItem container index value` for a subscript item assignment. -/
def subscriptSetDoElem (containerIdent : TSyntax `ident) (indexTerm value : TSyntax `term) :
    PygenM (TSyntax `doElem) := do
  let setItemIdent := mkIdent ``PyAstLean.pySetItem
  `(doElem| $containerIdent:ident := $setItemIdent $containerIdent $indexTerm $value)

/-- Lower an optional slice bound expression to a `some _`/`none` `Option Int` term. -/
def sliceBoundOptTerm (boundJson? : Option Json) : PygenM (TSyntax `term) := do
  match boundJson? with
  | none => `(none)
  | some boundJson => `(some $(← getCode boundJson `term))

/-- Recognize a slice assignment target `name[lower:upper]`, returning the container ident
and the two optional bound terms. Returns `none` for non-slice subscript targets. A step
(`name[a:b:c]`) is rejected. -/
def sliceTargetParts? (target : Json) :
    PygenM (Option (TSyntax `ident × TSyntax `term × TSyntax `term)) := do
  unless jsonNodeType? target == some "Subscript" do
    return none
  let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
    s!"Subscript assignment target is missing a 'slice' field: {target}"
  unless jsonNodeType? sliceJson == some "Slice" do
    return none
  unless (jsonFieldOption sliceJson "step").isNone do
    throwError "Slice assignment with a step (`s[a:b:c] = ...`) is not supported yet."
  let .ok containerJson := target.getObjValAs? Json "value" | throwError
    s!"Slice assignment target is missing a 'value' field: {target}"
  unless jsonNodeType? containerJson == some "Name" do
    throwError "Only `name[a:b] = ...` slice assignment (Name container) is supported."
  let containerIdent ← getCode containerJson `ident
  let lowerTerm ← sliceBoundOptTerm (jsonFieldOption sliceJson "lower")
  let upperTerm ← sliceBoundOptTerm (jsonFieldOption sliceJson "upper")
  return some (containerIdent, lowerTerm, upperTerm)

/-- Simple returned expressions can stay unparenthesized; more complex or effectful ones
keep parentheses so Lean parses multiline `return` expressions reliably. -/
def shouldParenthesizeReturnValue (value : Json) : Bool :=
  if jsonUsesMonadicEffect value then
    true
  else
    match jsonNodeType? value with
    | some "Name" => false
    | some "Constant" => false
    | some "Attribute" => false
    | _ => true

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        match ← tupleAssignTargetNames? target with
        | some idents => do
            let n := idents.size
            let valueStx ← getCode value `term
            let unpackTmpIdent := mkIdent (Name.mkSimple s!"__py_unpack_{idents.toList.map (·.getId.toString) |> String.intercalate "_"}")
            -- The unpack temporary is always private (an implementation detail).
            let cmd0 ← makeCommandPrivate (← `(command| def $unpackTmpIdent := $valueStx))
            let isTuple := jsonNodeType? value == some "Tuple"
            let mut cmds : Array (TSyntax `command) := #[cmd0]
            for i in List.range n do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              let cmd ← applyPrivacy idents[i]!.getId.toString (← `(command| def $(idents[i]!) := $acc))
              cmds := cmds.push cmd
            pure ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none => do
            if jsonNodeType? target == some "Subscript" then
              throwError "Top-level subscript assignment (`s[i] = ...`) is not supported; \
                it mutates a global, which has no top-level form. Move it into a function \
                or an `if __name__ == \"__main__\"` block."
            let nameIdent ← getCode target `ident
            let valueStx ← getCode value `term
            applyPrivacy nameIdent.getId.toString (← `(def $nameIdent := $valueStx))
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        match ← tupleAssignTargetNames? target with
        | some idents => do
            let n := idents.size
            let valueStx ← getCode value `term
            let valueTmpIdent := mkIdent (← freshName `__unpack_value)
            let unpackTmpIdent := mkIdent (← freshName `__unpack_pair)
            let bindValueTmp ←
              if jsonUsesIOEffect value || jsonUsesMonadicEffect value then
                `(doElem| let $valueTmpIdent:ident ← $valueStx:term)
              else
                `(doElem| let $valueTmpIdent:ident := $valueStx)
            let bindUnpackTmp ← `(doElem| let $unpackTmpIdent:ident := $valueTmpIdent)
            let isTuple := jsonNodeType? value == some "Tuple"
            let mut binds : Array (TSyntax `doElem) := #[bindValueTmp, bindUnpackTmp]
            for i in List.range n do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              binds := binds.push (← bindOrAssignLocal idents[i]! acc)
            -- Return the bindings as siblings (a flattened null-node), NOT wrapped in a
            -- nested `do` — wrapping would scope the unpacked names away from following
            -- statements. Consumers flatten via `appendDoElems`.
            pure ⟨mkNullNode (binds.map TSyntax.raw)⟩
        | none => do
            let rhs ←
              if jsonUsesIOEffect value then
                inlineIOTerm value
              else
                let valueStx ← getCode value `term
                if jsonUsesMonadicEffect value then
                  `((← $valueStx))
                else
                  pure valueStx
            match ← sliceTargetParts? target with
            | some (containerIdent, lowerTerm, upperTerm) =>
                -- `s[a:b] = repl` replaces the slice and reassigns the variable.
                let sliceSetIdent := mkIdent ``PyAstLean.pySliceSet
                `(doElem| $containerIdent:ident := $sliceSetIdent $containerIdent $lowerTerm $upperTerm $rhs)
            | none =>
            match ← subscriptTargetParts? target with
            | some (containerIdent, indexTerm) =>
                -- `s[i] = v` rebuilds the list/dict and reassigns the variable.
                subscriptSetDoElem containerIdent indexTerm rhs
            | none =>
                let nameIdent ← getCode target `ident
                bindOrAssignLocal nameIdent rhs
    | _, _ => throwError s!"Unsupported syntax category for Assign node"

/--
`AnnAssign` represents Python's annotated assignment syntax (`x : T = v` or `x : T`).
The remaining declaration-only form is currently treated as a no-op in `do` blocks, and
rejected at top level until the backend grows explicit type-directed declarations.
-/
@[pygen "AnnAssign"]
def annAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            throwError "Declaration-only annotated assignments are not yet supported at top level."
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `command json
    | `doElem, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            `(doElem| let _ := ())
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `doElem json
    | _, _ => throwError s!"Unsupported syntax category for AnnAssign node"

@[pygen "Return"]
def returnSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        match value with
        | .null =>
            `(doElem| return (()))
        | _ =>
            let valueStx ←
              if jsonUsesIOEffect value then
                inlineIOTerm value
              else
                let s ← getCode value `term
                if jsonUsesMonadicEffect value then `((← $s:term)) else pure s
            -- Bind the return value to a temporary, then `return` the temporary. A wide
            -- expression placed directly after `return` can be split onto the next line by the
            -- pretty-printer, which re-parses as `return` (Unit) followed by a stray term
            -- ("must be last element in a `do` sequence"). A `let` binding wraps safely, and
            -- `return <ident>` is always narrow enough to stay on one line.
            let retIdent := mkIdent (← freshName `__py_ret)
            let bind ← `(doElem| let $retIdent:ident := $valueStx)
            let ret ← `(doElem| return $retIdent)
            pure ⟨mkNullNode #[bind.raw, ret.raw]⟩
    | _, _ => throwError s!"Unsupported syntax category for Return node"

end PyAstLean
