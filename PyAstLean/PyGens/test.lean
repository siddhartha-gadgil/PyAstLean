import PyAstLean
import Libraries

open PyAstLean
open Libraries

def logger :=
  pyUnsupported "logger: Logger = logging.getLogger(__name__)"

def total_score := fun (scores : List Int) ↦
  Id.run
    (do
      let _ := pyUnsupported "logger.info(\"scoring\")"
      let mut blob := pyUnsupported "blob = requests.get(\"http://x\")"
      let mut total := (0 : Int)
      for s in (PyAstLean.pyIter scores)do
        total := total +ₚ s
      return total)

def main' :=
  ((do
      let _ := pyUnsupported "logging.basicConfig(level=logging.INFO)"
      let mut scores := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let _ ← pyPrintIO [pyPrintArg "total", pyPrintArg (total_score scores)]
      let _ ← pyPrintIO [pyPrintArg "doubled", pyPrintArg (total_score scores *ₚ (2 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ ← main'
  pure ()
