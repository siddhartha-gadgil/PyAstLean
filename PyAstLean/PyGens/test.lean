import PyAstLean
import Libraries
import PyAstLean.PyGens.test2
import Lean

open Lean






open PyAstLean
open Libraries


def main : IO Unit := do
  let mut t := PyAstLean.pyInt (← PyAstLean.pyInputIO "")
  for _ in PyAstLean.pyRange t do
    let mut __py_unpack1 := map int ((PyAstLean.pyStringSplit (← PyAstLean.pyInputIO "")))
    let mut n := PyAstLean.pyListGetItem __py_unpack1 (0 : Int)
    let mut d := PyAstLean.pyListGetItem __py_unpack1 (1 : Int)
    let mut a :=
      List.map (fun x => PyAstLean.pyInt x)
        ((do
            let __py_input0 ← PyAstLean.pyInputIO ""
            return PyAstLean.pyStringSplit __py_input0) :
          IO _)
    let mut g := Libraries.math.pyMathGcd n d
    let mut ands := [(1 : Int)] *ₚ g
    for i in PyAstLean.pyRange n do
      ands :=
        PyAstLean.pySetItem ands (i %ₚ g)
          (PyAstLean.pyBitAnd (PyAstLean.pyListGetItem ands (i %ₚ g)) (PyAstLean.pyListGetItem a i))
    if decide ((1 : Int) ∈ ands) then
      let _ ← PyAstLean.pyPrintIO [PyAstLean.PyPrintArg.mk (PyAstLean.PyPrintable.pyStringify (-(1 : Int)))]
      continue
    else
      let _ := ()
    let mut most := (0 : Int)
    for k in PyAstLean.pyRange g do
      let mut curr := k
      let mut last0 := -(1 : Int)
      let mut i := (0 : Int)
      let mut steps := Std.HashMap.ofList []
      let mut seen := Bool.false
      while !decide (curr ∈ steps) do
        if seen && curr == k && PyAstLean.pyListGetItem a curr == (0 : Int) && PyAstLean.pyLen steps == (0 : Int) then
          break
        else
          let _ := ()
        if PyAstLean.pyListGetItem a curr == (0 : Int) then
          last0 := i
        else
          if last0 != -(1 : Int) then
            steps := PyAstLean.pySetItem steps curr (i -ₚ last0)
          else
            let _ := ()
        curr := curr +ₚ d
        curr := curr %ₚ n
        seen := Bool.true
        i := i +ₚ (1 : Int)
      for _pair in PyAstLean.pyItems steps do
        let _ := Prod.fst _pair
        let v := Prod.snd _pair
        most := PyAstLean.pyMax [most, v]
    let _ ← PyAstLean.pyPrintIO [PyAstLean.PyPrintArg.mk (PyAstLean.PyPrintable.pyStringify most)]
  pure ()
