import PyAstLeanTest.PyAstLeanCheck


/-
PyAstLeanCheck (PALC) (pronounced - "pal" + "ack" like PAL Acknowledge) is the testing framework for PyAstLean. It is used to check that the generated Lean code matches the expected output. This is based on the FileCheck utility from LLVM, but with some differences to make it more suitable for our use case.
-/
def main (args : List String) : IO UInt32 :=
  PyAstLeanTest.runPALCMain args
