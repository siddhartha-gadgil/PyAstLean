import Lean
open Lean Meta Elab Term Std

open Lean.Parser.Term
def letEg : MetaM Unit := do
  let stx ← `(let x := 2; x + 1)
  logInfo m!"stx: {repr stx}"
  let stx' ← `(do
    let x := 1)
  let stx'' ← `(doElem| let mut x := 1)
  let stx''' ← `(doElem| x := x + 1)
  let ar ← `(← x)
  logInfo m!"stx': {repr stx'}"
  logInfo m!"stx'': {repr stx''}"
  logInfo m!"stx''': {repr stx'''}"
  logInfo m!"ar: {repr ar}"
  return

#eval letEg

#check Lean.Parser.Term.let
#check Lean.Parser.Term.do
#check Lean.Parser.Term.letDecl
#check Lean.Parser.Term.doLet
#check Expr.isAppOf

def eg : Id Unit := Id.run do
    let mut n := 1
    while n < 10 do
        let m := n * 2
        n := m + 1
    return
