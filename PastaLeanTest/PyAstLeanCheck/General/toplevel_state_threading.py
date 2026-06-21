# PastaLeanCHECK START
# TARGET: command
# CHECK: def main' :=
# CHECK: "hi"
# CHECK: def x₀ :=
# CHECK: (0 : Int)
# CHECK: def __py_for_. :=
# CHECK: List.foldl
# CHECK: fun _state i =>
# CHECK: Id.run
# CHECK: let mut x := _state
# CHECK: x := x +ₚ i
# CHECK: return x
# CHECK: x₀ (PastaLean.pyRange (5 : Int))
# CHECK: def x :=
# CHECK: __py_for_.
# CHECK: def AX₀ :=
# CHECK: def BX₀ :=
# CHECK: def __py_if_. :=
# CHECK: let mut AX := AX₀
# CHECK: let mut BX := BX₀
# CHECK: if AX > BX then
# CHECK: AX := Prod.fst __unpack_pair
# CHECK: BX := Prod.snd __unpack_pair
# CHECK: return (AX, BX)
# CHECK: def AX :=
# CHECK: Prod.fst __py_if_.
# CHECK: def BX :=
# CHECK: Prod.snd __py_if_.
# CHECK: def total₀ :=
# CHECK: def i₀ :=
# CHECK: def __py_while_. :=
# CHECK: let mut i := i₀
# CHECK: let mut total := total₀
# CHECK: while i < (5 : Int) do
# CHECK: total := total +ₚ i
# CHECK: i := i +ₚ (1 : Int)
# CHECK: return (i, total)
# CHECK: def i :=
# CHECK: Prod.fst __py_while_.
# CHECK: def total :=
# CHECK: Prod.snd __py_while_.
# PastaLeanCHECK END

# Bare top-level `for`/`if`/`while` are not executable in Lean, so we thread the names
# each block mutates as state: the block becomes a value returning the updated names,
# which are then re-exported as fresh `def`s. Names assigned once before a block are
# versioned (`x₀`) so the clean name (`x`) holds the block's result, and each result def
# is named after a short position-based hash so distinct blocks never collide.
#
# A standalone `def main()` (with no `__main__` guard) is renamed to `main'` in Lean, since
# Lean reserves the top-level name `main` for the program entry point (which must have type
# `IO (UInt32 | Unit | PUnit)`). Here it is just a normal helper, so it yields the name.

def main():
    return "hi"

# for: single-variable fold
x = 0
for i in range(5):
    x += i

# if: swap two globals (native tuple unpacking lowers through Prod.fst/snd)
AX = 3
BX = 2
if AX > BX:
    AX, BX = BX, AX

# while: thread two globals through one Id.run block
total = 0
i = 0
while i < 5:
    total += i
    i += 1
