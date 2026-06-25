import PastaLean
import Libraries

open PastaLean
open Libraries

set_option linter.all false

-- Assert statements: inline (inside a function) and top-level (outside any function).
@[simp, grind]
def GREETING :=
  "hi"

-- top-level assert — outside any function
theorem assert_holds : ((PastaLean.pyLen GREETING == (2 : Int)) = true) := by 
  rfl

@[simp, grind .]
def checked_add := fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      -- inline asserts inside a function body
      have ht : ((a == a) = true) := by
        grind
      have ht_1 : (decide (a +ₚ b ≥ a +ₚ b) = true) := by
        grind
      let __py_ret := a +ₚ b
      return __py_ret)

def checked_add'rn := fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      -- inline asserts inside a function body
      have ht : ((a == a) = true) := by
        grind
      have ht_1 : (decide (a +ₚ b ≥ a +ₚ b) = true) := by
        grind
      let __py_ret := a +ₚ b
      return __py_ret)
