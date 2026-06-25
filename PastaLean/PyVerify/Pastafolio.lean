import PastaLean.PyVerify.Pastafolio.Basic
import PastaLean.PyVerify.Pastafolio.Search

/-!
# `PastaLean.PyVerify.Pastafolio`

A small, reusable tactic-portfolio proof-search engine (a domain-tunable cousin of `try?`/hammer).

Build a `Pastafolio.Profile` describing your *preferences* — the tiered candidate tactics, how the
goal is read/classified, the per-candidate heartbeat budget — and hand it to `Pastafolio.runPastafolio`
inside a `syntax` + `@[tactic]` wrapper to get a tactic. The engine handles heartbeat isolation,
progress detection, `simp?`/`grind?` → concrete-tactic resolution, tiered racing, "Try this"
suggestions, and recording the discovered proof for splice-back pipelines.

See `PastaLean.PyVerify.AssertTactic` for the `taste?` profile built on top of this.
-/
