import Mathlib
import Libraries.scipy.ScipyDef

namespace Libraries.scipy

/-- Library-local registry for Python's `scipy` members (flattened across its submodules
`special` / `constants` / `stats` / `linalg`). -/
def pythonScipyMemberMap? (member : String) : Option Lean.Name :=
  match member with
  -- scipy.constants
  | "pi" => some ``pyScipyPi
  | "golden" => some ``pyScipyGolden
  | "golden_ratio" => some ``pyScipyGolden
  -- scipy.special
  | "factorial" => some ``pyScipyFactorial
  | "comb" => some ``pyScipyComb
  | "perm" => some ``pyScipyPerm
  | "gamma" => some ``pyScipyGamma
  | "erf" => some ``pyScipyErf
  -- scipy.stats
  | "tmean" => some ``pyScipyTmean
  | "gmean" => some ``pyScipyGmean
  | "hmean" => some ``pyScipyHmean
  -- scipy.linalg
  | "norm" => some ``pyScipyNorm
  | "det" => some ``pyScipyDet
  -- scipy.integrate
  | "odeint" => some ``pyScipyOdeint
  | _ => none

/-- Exact (`ℝ`) versions of scipy scalar members, used in the default numeric mode.
`none` for everything else (those keep their regular `pythonScipyMemberMap?` mapping). -/
def pythonScipyMemberMapReal? (member : String) : Option Lean.Name :=
  match member with
  | "pi" => some ``pyScipyPiR
  | "gamma" => some ``pyScipyGammaR
  | "gmean" => some ``pyScipyGmeanR
  | "norm" => some ``pyScipyNormR
  | _ => none

end Libraries.scipy
