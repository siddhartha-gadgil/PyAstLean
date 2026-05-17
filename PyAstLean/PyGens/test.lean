-- This file is for testing the outputs

import PyAstLean.PyGens
import PyAstLean.PyGens.Basic
namespace PyAstLean

def lmbda_expr := fun x ↦ x +ₚ (1 : Int)

def lmbda_with_condition := fun x ↦ if x %ₚ (2 : Int) == (0 : Int) then x +ₚ (1 : Int) else x -ₚ (1 : Int)

def lmbda_with_array :=
  let a := [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]
  let b := fun x ↦ if decide (x ∈ a) then some (x *ₚ x) else none
  let c := b
  c

def lmbda_with_string :=
  let s := "hello"
  fun char ↦ PyAstLean.pyContains (s +ₚ " world")
  char

def nested_lmbda := fun () ↦ fun x ↦ x *ₚ x

def lmbda_with_function_call :=
  let add_one := fun x ↦ x +ₚ (1 : Int)
  fun x ↦ add_one x

def lmbda_ds := fun x ↦ [x, x *ₚ (2 : Int), x *ₚ (3 : Int)]

def lmbda_with_nested_conditions := fun x ↦
  if x %ₚ (2 : Int) == (0 : Int) && x %ₚ (3 : Int) == (0 : Int) || x %ₚ (5 : Int) == (0 : Int) then x +ₚ (1 : Int)
  else x -ₚ (1 : Int)

def lmbda_with_tuple_unpacking := fun {α β} [ToString α] [ToString β] (pair : α × β) ↦
  String.append (String.append (String.append "" (ToString.toString (Prod.fst pair))) ":")
    (ToString.toString (Prod.snd pair))

def lmbda_with_side_effects :=
  Id.run
    (do
      let mut result := []
      for x in PyAstLean.pyRange (5 : Int)do
        result := result ++ [x *ₚ x]
      return (fun (y : Unit) ↦ result))

def lmbda_with_generator_expression := fun () ↦
  List.map (fun x => x *ₚ x) (List.map (fun i => i) (PyAstLean.pyRange (5 : Int)))
