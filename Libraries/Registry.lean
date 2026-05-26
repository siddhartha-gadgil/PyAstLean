import Lean
import Libraries.math.Mapping
import Libraries.numpy.Mapping

namespace Libraries

/--
Registry mapping imported Python library members to Lean runtime functions/constants.

This plays the same role for imported libraries that `PyAstLean.Attributes` plays for
Python methods: codegen consults this table once an AST node has been recognized as
coming from a specific imported module.
-/
def pythonLibraryMap? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "math" => math.pythonMathMemberMap? member
  | "numpy" => numpy.pythonNumpyMemberMap? member
  | _ => none

end Libraries
