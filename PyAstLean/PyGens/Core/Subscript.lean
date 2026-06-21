import PyAstLean.PyAPI.Core
import PyAstLean.PyGens.Basic

namespace PyAstLean

/-- Check if a JSON node represents a string constant. -/
def isStringConstant (json : Lean.Json) : Bool :=
    let nodeType := json.getObjValAs? (α := Lean.Json) (k := "node_type")
    let value := json.getObjValAs? (α := Lean.Json) (k := "value")
    match nodeType, value with
    | Except.ok "Constant", Except.ok (.str _) => true
    | _, _ => false

open Lean Elab Term Meta
open PyAstLean

/-- Build the Lean term for `value[slice]` from an *already-lowered* `valueCode`. Factoring this
out of the `@[pygen]` entry point lets IO inlining/hoisting rebuild a subscript over an awaited
container (`foo()[i]` where `foo()` is `IO _`) without re-lowering — and re-awaiting — the base. -/
def subscriptTermFromValue (valueJson sliceJson : Json) (valueCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
    let isTuple := match valueJson.getObjValAs? String "node_type" with
    | .ok "Tuple" => true
    | _ =>
      -- A `Name` that codegen has marked as a known pair-typed value (e.g. a lambda parameter
      -- bound to `α × β` and used via `pair[0]`/`pair[1]`) is treated like a tuple literal so a
      -- constant `0`/`1` index lowers to `Prod.fst`/`Prod.snd` rather than the generic
      -- `pyGetItem` notation (which has no `PyGetItem` instance for heterogeneous products).
      match valueJson.getObjValAs? Bool "_pyastlean_pair" with
      | .ok true => true
      | _ => false
    let isString := isStringConstant valueJson

    let sliceType := sliceJson.getObjValAs? String "node_type"
    if sliceType == .ok "Slice" then
        -- Lower each slice bound to an `Option Int` term. A missing or `None` bound is `none`;
        -- any other bound expression (constant, variable, arithmetic) is lowered through `getCode`
        -- and wrapped in `some`, so `a[i:j]`, `a[n-1::-1]`, etc. all carry the real bound rather
        -- than being silently dropped to a full slice.
        let boundStx (field : String) : PygenM (TSyntax `term) := do
            match (sliceJson.getObjVal? field).toOption with
            | none => `(none)
            | some j =>
                if j.getObjValAs? String "node_type" == .ok "Constant"
                    && (j.getObjVal? "value").toOption.any (· == Json.null) then
                  `(none)
                else
                  match j with
                  | .null => `(none)
                  | _ => `(some $(← getCode j `term))
        let startStx ← boundStx "lower"
        let stopStx ← boundStx "upper"
        let stepStx ← boundStx "step"
        -- Generic slice dispatch: a `String` slices to `String`, a `List` to `List`; the `step`
        -- bound makes `a[::-1]`/`a[::2]` correct. (A bare string literal uses the String slicer
        -- directly for predictable output.)
        let sliceIdent :=
          if isString then mkIdent `PyAstLean.pyStringSliceStep
          else mkIdent `PyAstLean.pySlice
        `($sliceIdent $valueCode $startStx $stopStx $stepStx)
    else if sliceType == .ok "Tuple" then
        -- numpy-style 2-D indexing on a `List (List _)`: `a[i,j]`, `a[:,j]` (column), `a[i,:]` (row).
        match sliceJson.getObjValAs? (Array Json) "elts" with
        | .ok elts =>
            if elts.size == 2 then
                let a := elts[0]!
                let b := elts[1]!
                let aSlice := a.getObjValAs? String "node_type" == .ok "Slice"
                let bSlice := b.getObjValAs? String "node_type" == .ok "Slice"
                if aSlice && !bSlice then
                    let jCode ← getCode b `term
                    `(List.map (fun row => row⦋$jCode⦌) $valueCode)
                else if !aSlice && bSlice then
                    `($valueCode⦋$(← getCode a `term)⦌)
                else if !aSlice && !bSlice then
                    `($valueCode⦋$(← getCode a `term)⦌⦋$(← getCode b `term)⦌)
                else
                    pure valueCode
            else
                throwError "Only 2-D tuple subscripts are supported."
        | .error _ => throwError "Tuple subscript is missing its 'elts' field."
    else if isTuple then
        match sliceJson.getObjValAs? String "node_type", sliceJson.getObjValAs? Json "value" with
        | .ok "Constant", .ok (.num (JsonNumber.mk 0 0)) =>
            let fstIdent := mkIdent ``Prod.fst
            `($fstIdent $valueCode)
        | .ok "Constant", .ok (.num (JsonNumber.mk 1 0)) =>
            let sndIdent := mkIdent ``Prod.snd
            `($sndIdent $valueCode)
        | _, _ =>
            let sliceCode ← getCode sliceJson `term
            let getIdent := mkIdent `getElem!
            `($getIdent $valueCode $sliceCode)
    else if isString then
        -- Indexing a string literal yields a one-character string (Python has no char type),
        -- matching `pyGetItem`/`PyGetItem String Int String` on string variables.
        let getIdent := mkIdent `PyAstLean.pyStringGetItemStr
        let sliceType := sliceJson.getObjValAs? String "node_type"
        match sliceType with
        | .ok "Constant" =>
            let idx := sliceJson.getObjValAs? Int "value"
            match idx with
            | .ok i =>
                let iStx ← intToStx i
                `($getIdent $valueCode $iStx)
            | _ =>
                let sliceCode ← getCode sliceJson `term
                `($getIdent $valueCode $sliceCode)
        | _ =>
            let sliceCode ← getCode sliceJson `term
            `($getIdent $valueCode $sliceCode)
    else
        -- General container indexing `c[i]`, emitted with the readable `c⦋i⦌` notation (which is
        -- definitionally `pyGetItem c i`, so it dispatches through any `PyGetItem` instance).
        let sliceType := sliceJson.getObjValAs? String "node_type"
        match sliceType with
        | .ok "Constant" =>
            let idx := sliceJson.getObjValAs? Int "value"
            match idx with
            | .ok i =>
                let iStx ← intToStx i
                `($valueCode⦋$iStx⦌)
            | _ =>
                let sliceCode ← getCode sliceJson `term
                `($valueCode⦋$sliceCode⦌)
        | .ok "UnaryOp" =>
            let op := sliceJson.getObjValAs? String "op"
            let operand := sliceJson.getObjValAs? Json "operand"
            if op == .ok "neg" then
                match operand with
                | .ok j =>
                    let val := j.getObjVal? "value"
                    match val with
                    | .ok jVal =>
                        match jVal.getNat? with
                        | .ok n =>
                            let iStx ← intToStx (-(n : Int))
                            `($valueCode⦋$iStx⦌)
                        | _ =>
                            let sliceCode ← getCode sliceJson `term
                            let getIdent := mkIdent `getElem!
                            `($getIdent $valueCode $sliceCode)
                    | _ =>
                        let sliceCode ← getCode sliceJson `term
                        `($valueCode⦋$sliceCode⦌)
                | _ =>
                    let sliceCode ← getCode sliceJson `term
                    `($valueCode⦋$sliceCode⦌)
            else
                let sliceCode ← getCode sliceJson `term
                `($valueCode⦋$sliceCode⦌)
        | _ =>
            let sliceCode ← getCode sliceJson `term
            `($valueCode⦋$sliceCode⦌)

@[pygen "Subscript"]
def subscriptSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Subscript node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok sliceJson := json.getObjValAs? Json "slice" | throwError
      s!"Subscript node does not have a 'slice' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    subscriptTermFromValue valueJson sliceJson valueCode
  | _, _ => throwError s!"Unsupported syntax category for Subscript node"

end PyAstLean
