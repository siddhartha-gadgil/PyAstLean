import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Calls.CallEffects
import PastaLean.PyGens.Calls.CallShared

open Lean Meta Elab Term Qq Std

namespace PastaLean

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
    let getIdent := mkIdent ``PastaLean.pyListGetItem
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
  let pyUnpack2Ident := mkIdent ``PastaLean.pyUnpack2
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
  let setItemIdent := mkIdent ``PastaLean.pySetItem
  `(doElem| $containerIdent:ident := $setItemIdent $containerIdent $indexTerm $value)

/-- Lower a possibly-nested subscript assignment `a[i]…[k] = value` to a reassignment of the
base variable. Each level is rebuilt innermost-first with `pySetItem`: `a[i][j] = v` becomes
`a := pySetItem a i (pySetItem (pyGetItem a i) j v)`. This mirrors Python, where mutating the
inner list and leaving outer bindings pointing at the (now-rebuilt) value is observationally the
same for the local variable. Returns `none` when the target is not a subscript (or is an outer
slice, handled by `sliceTargetParts?`); throws if the base is not a variable. -/
partial def nestedSubscriptSetDoElem? (target : Json) (value : TSyntax `term) :
    PygenM (Option (TSyntax `doElem)) := do
  unless jsonNodeType? target == some "Subscript" do return none
  let .ok containerJson := target.getObjValAs? Json "value" | throwError
    s!"Subscript assignment target is missing a 'value' field: {target}"
  let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
    s!"Subscript assignment target is missing a 'slice' field: {target}"
  if jsonNodeType? sliceJson == some "Slice" then return none
  let indexTerm ← getCode sliceJson `term
  let setItemIdent := mkIdent ``PastaLean.pySetItem
  let containerCode ← getCode containerJson `term
  let newContainer ← `($setItemIdent $containerCode $indexTerm $value)
  match jsonNodeType? containerJson with
  | some "Name" =>
      let containerIdent ← getCode containerJson `ident
      return some (← `(doElem| $containerIdent:ident := $newContainer))
  | some "Subscript" =>
      nestedSubscriptSetDoElem? containerJson newContainer
  | _ =>
      throwError "Subscript assignment requires the base container to be a variable \
        (`a[i]…[k] = v`); got an unsupported container expression."

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

/-- If `target` is `self.X` (an `Attribute` whose base is the `Name` `self`), return the attribute
name `X`. Used to lower attribute writes inside a class method to a `self` record update. -/
def selfAttrTarget? (target : Json) : Option String :=
  if jsonNodeType? target == some "Attribute" then
    match (target.getObjVal? "value").toOption, (target.getObjValAs? String "attr").toOption with
    | some v, some attr =>
        if jsonNodeType? v == some "Name" && v.getObjValAs? String "id" == .ok "self" then
          some attr
        else none
    | _, _ => none
  else none

/-- Emit `self := { self with X := rhs }` — the value-semantics lowering of `self.X = rhs` inside a
class method body (`self` is the method's `let mut` shadow). -/
def selfRecordUpdateDoElem (attr : String) (rhs : TSyntax `term) : PygenM (TSyntax `doElem) := do
  let selfId := mkIdent `self
  let attrId := mkIdent attr.toName
  let fields := #[← `(Lean.Parser.Term.structInstField| $attrId:ident := $rhs)]
  `(doElem| $selfId:ident := { $selfId:term with $fields:structInstField,* })

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
    | `command, json => withRealIfMarked json do
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
            -- A literal `Tuple` RHS builds a `Prod` (use `Prod.fst`/`Prod.snd`); so does a
            -- function call returning a `tuple[...]` (the Python pre-pass only leaves such
            -- tuple-returning calls as native unpacking — list-returning RHSs are pre-split
            -- into subscripts and never reach here, so a `Call` here means a `Prod` result).
            let isTuple := jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
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
    | `doElem, json => withRealIfMarked json do
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
            -- A literal `Tuple` RHS builds a `Prod` (use `Prod.fst`/`Prod.snd`); so does a
            -- function call returning a `tuple[...]` (the Python pre-pass only leaves such
            -- tuple-returning calls as native unpacking — list-returning RHSs are pre-split
            -- into subscripts and never reach here, so a `Call` here means a `Prod` result).
            let isTuple := jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            let mut binds : Array (TSyntax `doElem) := #[bindValueTmp, bindUnpackTmp]
            for i in List.range n do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              binds := binds.push (← bindOrAssignLocal idents[i]! acc)
            -- Return the bindings as siblings (a flattened null-node), NOT wrapped in a
            -- nested `do` — wrapping would scope the unpacked names away from following
            -- statements. Consumers flatten via `appendDoElems`.
            pure ⟨mkNullNode (binds.map TSyntax.raw)⟩
        | none => do
            -- Some RHS calls both mutate their receiver and yield a value (e.g. `x.pop()`), which a
            -- pure term cannot express. The Calls layer lowers these to a value term plus a
            -- container-update statement, both reading the original container; assignment binds the
            -- target to the value first, then applies the update.
            if jsonNodeType? target == some "Name" then
              if let some (valueTerm, update) ← mutatingCallRhsLowering? value then
                let bindTarget ← bindOrAssignLocal (← getCode target `ident) valueTerm
                return ⟨mkNullNode #[bindTarget.raw, update.raw]⟩
            let rhs ←
              if jsonUsesIOEffect value then
                inlineIOTerm value
              else
                let valueStx ← getCode value `term
                if jsonUsesMonadicEffect value then
                  `((← $valueStx))
                else
                  pure valueStx
            -- `self.X = v` inside a class method (where `self` is the `let mut` shadow) rebuilds
            -- `self` via record update. The `hasVar self` guard keeps top-level `obj.x = v`
            -- (no mutable `self` in scope) on its normal path.
            if let some attr := selfAttrTarget? target then
              if ← hasVar `self then
                return ← selfRecordUpdateDoElem attr rhs
            match ← sliceTargetParts? target with
            | some (containerIdent, lowerTerm, upperTerm) =>
                -- `s[a:b] = repl` replaces the slice and reassigns the variable.
                let sliceSetIdent := mkIdent ``PastaLean.pySliceSet
                `(doElem| $containerIdent:ident := $sliceSetIdent $containerIdent $lowerTerm $upperTerm $rhs)
            | none =>
            match ← nestedSubscriptSetDoElem? target rhs with
            | some setStx =>
                -- `s[i] = v` (and nested `g[i][j] = v`) rebuild the container(s) and reassign.
                pure setStx
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
    | `doElem, json => withRealIfMarked json do
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
            -- A simple atom (`return x` / `return 42`) is always narrow, so return it directly.
            -- A wide expression placed directly after `return`, however, can be split onto the
            -- next line by the pretty-printer, which re-parses as `return` (Unit) followed by a
            -- stray term ("must be last element in a `do` sequence"). For those we bind the value
            -- to a temporary first and `return <ident>`, which always stays on one line.
            match jsonNodeType? value with
            | some "Name" | some "Constant" =>
                `(doElem| return $valueStx)
            | _ =>
                let retIdent := mkIdent (← freshName `__py_ret)
                let bind ← `(doElem| let $retIdent:ident := $valueStx)
                let ret ← `(doElem| return $retIdent)
                pure ⟨mkNullNode #[bind.raw, ret.raw]⟩
    | _, _ => throwError s!"Unsupported syntax category for Return node"

end PastaLean
