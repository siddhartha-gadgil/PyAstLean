import PastaLean.PyGens.Core.Utils
import PastaLean.PyVerify.AssertTactic

/-!
# PASSTA contract codegen (Track P)

Detection and theorem-building for the `Libraries.passta` contract markers (`Requires`/`Ensures`/
`Assert`/`Assume`/`Invariant`/`Decreases`). This is the *pure, non-monadic* track: a straight-line
function carrying contracts emits its ordinary runnable `def` (contracts stripped) plus a named
`<fn>_spec` theorem `∀ params, Requires → (let …; Ensures)` discharged by `taste?`.

The emission hook itself lives in `PyGens/UseCases/FuncDef.lean` (it needs `functionValueSyntax`);
this file holds the reusable, codegen-coupled pieces.
-/

open Lean Meta Elab Term Qq Std
open Lean.Parser.Term

namespace PastaLean

/-- A PASSTA contract `Expr`-statement `pyPass<Member> (arg)` → `(member, arg)`, where `member` is
`"Requires"`/`"Ensures"`/`"Assert"`/`"Assume"`/`"Invariant"`/`"Decreases"` (the Python
`library_member` tag, preserved on the call's `func`). `none` for any non-contract statement. -/
def contractArg? (stmt : Json) : Option (String × Json) :=
  match jsonNodeType? stmt with
  | some "Expr" =>
    match (stmt.getObjVal? "value").toOption with
    | some value =>
      match jsonNodeType? value, (value.getObjVal? "func").toOption with
      | some "Call", some func =>
        match func.getObjValAs? String "library_module", func.getObjValAs? String "library_member",
              (value.getObjValAs? (Array Json) "args").toOption with
        | .ok "passta", .ok member, some args =>
          match args[0]? with
          | some arg => some (member, arg)
          | none => none
        | _, _, _ => none
      | _, _ => none
    | none => none
  | _ => none

/-- Build `@[taste_ingr] theorem <thmName> : ∀ params, <hyps> → (let-binders; <concl>) := by taste?`
from extracted proof data. Shared by the lone-assert promotion (`theoremShape?`) and the contract
(`_spec`) path. Built outside-in: conclusion, hypothesis arrows, `let`-binders, then `∀`s; everything
lowered as a `Prop` (so `==`→`=`, `<`/`≤`→the real order). -/
def buildSpecTheorem (thmName : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (letJsons hypJsons : Array Json) (conclJson : Json) : PygenM (TSyntax `command) :=
  withFreshVariables do
    for letJson in letJsons do
      if let .ok tname := (letJson.getObjVal? "target").bind (·.getObjValAs? String "id") then
        addVar tname.toName
    let mut propTy ← withPropCondition true (getCode conclJson `term)
    for hypJson in hypJsons.reverse do
      propTy ← `($(← withPropCondition true (getCode hypJson `term)) → $propTy)
    for letJson in letJsons.reverse do
      let .ok target := letJson.getObjVal? "target" | throwError "buildSpecTheorem: Assign without target"
      let .ok value := letJson.getObjVal? "value" | throwError "buildSpecTheorem: Assign without value"
      propTy ← `(let $(← getCode target `ident) := $(← getCode value `term)
                 $propTy)
    for (argIdent, ty?) in argInfos.reverse do
      propTy ← match ty? with
        | some ty => `(∀ ($argIdent : $ty), $propTy)
        | none => `(∀ $argIdent, $propTy)
    `(command| @[taste_ingr] theorem $thmName : $propTy := by taste?)

/-- Track P: a *pure, straight-line* contracted function (`Requires`/`Ensures`, `let`s, `return` —
no loops, IO, or `raise`). Splits the body into the runnable statements (contracts stripped) and the
proof data. Returns `(cleanBody, lets, hyps, concl)`. `none` if monadic, if any statement isn't a
fresh `let`/`return`/contract, if an `Invariant`/`Decreases` appears (those imply a loop ⇒ Track M),
or if there's no `Ensures`/`Assert` to prove. Multiple `Ensures` conjoin into one conclusion. -/
def contractShape? (paramNames : Array String) (body substantive : Array Json) :
    Option (Array Json × Array Json × Array Json × Json) := Id.run do
  if bodyNeedsIOMonad body || bodyNeedsExceptionMonad body then return none
  let mut lets : Array Json := #[]
  let mut hyps : Array Json := #[]
  let mut concls : Array Json := #[]
  let mut clean : Array Json := #[]
  let mut seen : Array String := #[]
  let mut sawContract := false
  let mut sawReturn := false
  for s in substantive do
    match contractArg? s with
    | some (member, arg) =>
      sawContract := true
      match member with
      | "Requires" | "Assume" => hyps := hyps.push arg
      | "Ensures" | "Assert" => concls := concls.push arg
      | _ => return none
    | none =>
      match jsonNodeType? s with
      | some "Return" => sawReturn := true; clean := clean.push s
      | some "Assign" =>
        let .ok target := s.getObjVal? "target" | return none
        if jsonNodeType? target != some "Name" then return none
        let .ok tname := target.getObjValAs? String "id" | return none
        if paramNames.contains tname || seen.contains tname then return none
        seen := seen.push tname
        lets := lets.push s
        clean := clean.push s
      | _ => return none
  if !sawContract || concls.isEmpty || !sawReturn then return none
  let concl := if concls.size == 1 then concls[0]!
    else Json.mkObj [("node_type", Json.str "BoolOp"), ("op", Json.str "and"), ("values", Json.arr concls)]
  return some (clean, lets, hyps, concl)

end PastaLean
