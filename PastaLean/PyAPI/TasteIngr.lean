import Mathlib

/-- Targeted simp set for proving transpiled `assert`s. It collects the Python-operator rewrite
lemmas (`Operators.lean`) plus every pure prove-version function (tagged by the code generator), so
`taste?` can `simp [taste_ingr]` — fast, unlike full `simp`/`simp_all`, which chokes on the
`*ₚ` typeclass operators. Registered in its own module because an attribute can't be *used* in the
same file that registers it. Proving aid only; the runnable `'rn` twin is never tagged. -/
register_simp_attr taste_ingr
