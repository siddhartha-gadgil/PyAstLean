import Mathlib
import PastaLean.PyAPI.Builtins.Casting

namespace PastaLean

/-- Read one Python-style input line, optionally printing a prompt first. -/
def pyInputIO (prompt : String := "") : IO String := do
  if !prompt.isEmpty then
    IO.print prompt
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  -- `getLine` returns "" only at end of input (an empty *line* is "\n"). Python's `input()`
  -- raises `EOFError` there; raising it lets the common read-until-EOF idiom
  -- (`while True: try: input() … except: break`) terminate instead of spinning on "" forever.
  if line.isEmpty then
    throw (IO.userError "EOFError")
  return line.trimAsciiEnd.toString

end PastaLean
