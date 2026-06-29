import Lean

/-!
# Pastafolio proof search — core types & helpers

A reusable, configurable tactic-portfolio driver — a domain-tunable cousin of `try?`/hammer.

The split is deliberate: this engine is **domain-agnostic**. Everything that varies between use
cases (which tactic candidates to try, in what order, how to read the goal) lives in a `Profile`
value supplied by the caller. The engine provides the *mechanism*:

* per-candidate heartbeat isolation (`withBudget`),
* progress detection (`goalTargets`),
* `simp?`/`grind?` → concrete-tactic resolution (`firstTryThisSince`),
* and (in `Search.lean`) tiered racing + recording the discovered proof.

Import `PastaLean.PyVerify.Pastafolio`, build a `Profile`, and hand it to `runPastafolio`.
-/

open Lean Elab Tactic Meta

namespace PastaLean.Pastafolio

/-- Pretty-print a tactic to a single clean string (drops inaccessible-name markers). -/
def tacToString (tac : TSyntax `tactic) : TacticM String := do
  return (← Lean.PrettyPrinter.ppTactic tac).pretty.replace "✝" ""

/-- Collapse every run of whitespace to a single space (and trim). Keeps a multi-line resolved
suggestion (`simp only [\n  a, b ]`) on one line so it splices cleanly. -/
def collapseWs (s : String) : String := Id.run do
  let mut out := ""
  let mut needSep := false  -- emitted a word, now inside a whitespace gap
  for c in s.toList do
    if c.isWhitespace then
      if !out.isEmpty then needSep := true
    else
      if needSep then out := out.push ' '
      out := out.push c
      needSep := false
  return out

/-- Each open goal's target type, metavariables instantiated. We compare these to decide progress:
a tactic helped iff some goal's statement changed or a goal closed/opened. -/
def goalTargets : TacticM (List Expr) := do
  (← getGoals).mapM fun g => do instantiateMVars (← g.getType)

/-- A trace tactic (`simp?`/`grind?`) logs its resolved form as a `Try this: <tac>` info message.
Recover the first such suggestion from the messages logged since `nBefore` messages were present,
so the recorded proof is the concrete `simp only [...]` rather than the `?` placeholder. -/
def firstTryThisSince (nBefore : Nat) : TacticM (Option String) := do
  let msgs := (← getThe Core.State).messages.toList.drop nBefore
  for msg in msgs do
    let s ← msg.data.toString
    match (s.splitOn "Try this:")[1]? with
    | some rest =>
      -- the rendered message is `Try this:\n[apply] <tactic>` — `[apply]` is the apply-widget's
      -- link text, so drop it to recover just the tactic.
      let tac0 := collapseWs rest
      let tac := if tac0.startsWith "[apply] " then String.ofList (tac0.toList.drop 8) else tac0
      unless tac.isEmpty do
        return some tac
    | none => pure ()
  return none

/-- Parse a tactic string back into syntax (`none` if it doesn't parse). -/
def parseTactic? (s : String) : TacticM (Option (TSyntax `tactic)) := do
  match Lean.Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => return some ⟨stx⟩
  | .error _ => return none

/-- Run `x` with a *fresh* heartbeat budget of `n` (`0` = unlimited). We reset the elapsed-heartbeat
baseline (`initHeartbeats`) and set the cap in a single lexical `withTheReader`, so a candidate that
exhausts its budget throws cleanly and the override is unwound on the exception path — no leakage to
later candidates. (Nesting the cap *inside* `withCurrHeartbeats`' `controlAt` leaks it; this doesn't.)
Applied per candidate so one expensive tactic can't drain the whole search. -/
def withBudget {α : Type} (n : Nat) (x : TacticM α) : TacticM α := do
  let hb ← IO.getNumHeartbeats
  withTheReader Core.Context (fun c => { c with maxHeartbeats := n, initHeartbeats := hb }) x

/-- The *preferences* for a portfolio search — everything domain-specific. Build one of these and
hand it to `runPastafolio`.

The search has two phases, which is the load-bearing distinction:

* **simplifiers** make *progress* (change the goal) without needing to close it — `intros`, `simp`,
  `push_cast`. They're raced and committed greedily, re-derived against each new residual, until
  none moves the goal (with cycle detection so `simp`/`ring_nf` churn can't loop).
* **closers** must *fully close* the goal — `ring`, `nlinarith`, `positivity`, `grind`, `aesop`.
  Tried only once simplification stalls; the first that discharges the goal wins. A closer that
  merely normalizes (e.g. `ring` reshaping an inequality it can't prove) is **rejected**, so it
  never lands in the recorded proof as dead weight.

Both are re-derived from the current goal each round, so a profile can classify the post-simp
residual and reorder (e.g. promote `nlinarith` ahead of `grind` once the goal is nonlinear). -/
structure Profile where
  /-- Tactics that make progress without having to close the goal (raced, committed greedily). -/
  simplifiers : TacticM (Array (TSyntax `tactic))
  /-- Tactics that must *fully close* the goal; the first that does wins. -/
  closers     : TacticM (Array (TSyntax `tactic))
  /-- Per-candidate heartbeat cap as a function of the ambient `maxHeartbeats`. Default: the ambient
  value unchanged. Cap it (e.g. `fun n => min n 800000000`) to bound expensive candidates harder. -/
  budget      : Nat → Nat := id
  /-- Max number of committed simplifier steps — guards against runaway simplification. -/
  fuel        : Nat := 24
  /-- Optional sink for each discovered proof, keyed by the *byte offset* of its tactic syntax (used
  by splice-back pipelines such as `py2lean`'s prove-and-replace, which matches each proof to its
  `taste?` token by position — so a token whose goals `mvcgen` self-closed records nothing and the
  splice can tell). `none` to just emit the "Try this" suggestion. -/
  winnersRef? : Option (IO.Ref (Array (Nat × String))) := none

end PastaLean.Pastafolio
