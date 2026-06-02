import PyAstLean
import Libraries
import PyAstLean.PyGens.test2

open PyAstLean
open Libraries

def testfoo : IO Unit := do
  let x := foo
  IO.println s!"Value of foo: {x}"

def testfoo2 : IO Unit := do
  IO.println s!"Value of _not_really_private: {_not_really_private}"
  let y := foo2 5
  IO.println s!"Value of foo2(5): {y}"

#eval testfoo2
#eval _priv
