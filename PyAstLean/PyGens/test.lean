import PyAstLean.PyGens
import PyAstLean.PyGens.Basic
namespace PyAstLean

def l :=
  List.map
    (fun x => (x ^ₚ (2 : Int))) [List.filter (fun x => List.all [] (fun ifCond => ifCond x)) (pyRange (10 : Int))]
