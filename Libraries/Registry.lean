import Lean
import Libraries.functools.Mapping
import Libraries.math.Mapping
import Libraries.numpy.Mapping
import Libraries.scipy.Mapping
import Libraries.pandas.Mapping

namespace Libraries

/--
Registry mapping imported Python library members to Lean runtime functions/constants.

This plays the same role for imported libraries that `PyAstLean.Attributes` plays for
Python methods: codegen consults this table once an AST node has been recognized as
coming from a specific imported module.
-/
def pythonLibraryMap? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "functools" => functools.pythonFunctoolsMemberMap? member
  | "math" => math.pythonMathMemberMap? member
  | "numpy" => numpy.pythonNumpyMemberMap? member
  | "scipy" => scipy.pythonScipyMemberMap? member
  | "pandas" => pandas.pythonPandasMemberMap? member
  | _ => none

end Libraries
