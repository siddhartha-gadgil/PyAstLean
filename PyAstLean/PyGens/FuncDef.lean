import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

/-!
  Translates a Python function definition to a Lean function definition. For now, this is a very basic implementation that only handles simple function definitions with no parameters and a single return statement. The main function is `funcDefSyntax`, which takes a JSON object representing a Python function definition and returns the corresponding Lean syntax.
-/

/-!
## Function definitions

A sample Python AST:

```python
Module(body=[FunctionDef(name='f', args=arguments(posonlyargs=[], args=[arg(arg='n')], kwonlyargs=[], kw_defaults=[], defaults=[]), body=[Assign(targets=[Name(id='m', ctx=Store())], value=BinOp(left=Name(id='n', ctx=Load()), op=Add(), right=Constant(value=1))), Return(value=Name(id='m', ctx=Load()))], decorator_list=[], type_params=[])], type_ignores=[])
```

For the definition:

```python
def f(n):
    m = n + 1
    return m
```
-/

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(def $nameIdent := $valueStx)
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        if ← hasVar nameIdent.getId then
            `(doElem| $nameIdent:ident := $valueStx)
        else
            -- IO.eprintln s!"Variable `{nameIdent.getId}` not found in context, treating as new variable declaration; variables: {(← get).varNames.toList}"  -- Debugging output
            let stx ← `(doElem| let mut $nameIdent:ident := $valueStx)
            addVar nameIdent.getId
            -- IO.eprintln s!"Added variable `{nameIdent.getId}` to context, check: {← hasVar nameIdent.getId}"  -- Debugging output
            return stx
    | _, _ => throwError s!"Unsupported syntax category for Assign node"

@[pygen "Return"]
def returnSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(doElem| return $valueStx)
    | _, _ => throwError s!"Unsupported syntax category for Return node"

@[pygen "While"]
def whileSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok test := json.getObjVal? "test" | throwError
          s!"While node does not have a 'test' field or it is not a JSON value: {json}"
        let testStx ← getCode test `term
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"While node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"While node does not have an 'orelse' field or it is not a JSON array: {json}"
        unless orelseElems.isEmpty do
          throwError "Python while-else blocks are not supported."
        let mut bodyStxArray := #[]
        for elem in bodyElems do
            let elemStx ← getCode elem `doElem
            bodyStxArray := bodyStxArray.push elemStx
        `(doElem| while $testStx do
            $[$bodyStxArray:doElem]*)
    | _, _ => throwError s!"Unsupported syntax category for While node"

/--
Reformat a list of Json to an object with `node_type` the `node_type` of the original list's first element with "Head_" prefixed, and `args` the original list. This is needed to handle the case where the body of a function definition is a list of statements, which is represented as a JSON array in the input, but we want to treat it as a single JSON object with a specific `node_type` in our code generation. We use this to try to generate *pure* code, i.e., not Monadic code.
-/
def splitList : List Json -> PygenM Json
| [] => throwError "Cannot split an empty list"
| (first :: rest) => do
    let .ok nodeType := first.getObjValAs? String "node_type" | throwError
      s!"First element of list does not have a 'node_type' field or it is not a string: {first}"
    let newNodeType := "Head_" ++ nodeType
    let newJson := first.mergeObj (Json.mkObj [("node_type", newNodeType), ("rest", toJson rest)])
    return newJson

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let .ok args := json.getObjVal? "args" | throwError
          s!"FuncDef node does not have an 'args' field or it is not a JSON value: {json}"
        let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
          s!"FuncDef args does not have an 'args' field or it is not a JSON value: {args}"
        let mut argStrs := #[]
        for arg in argsArray do
          let .ok argName := arg.getObjValAs? String "arg" | throwError
            s!"FuncDef argument does not have an 'arg' field or it is not a string: {arg}"
          argStrs := argStrs.push argName
        let argIdents := argStrs.map (fun argName => mkIdent argName.toName)
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"FuncDef node does not have a 'body' field or it is not a JSON value: {json}"
        let mut bodyStxArray := #[]
        try
          -- Attempt to generate pure code by treating the body as a single unit and generating syntax for it directly, which will allow us to generate non-monadic code if the body is simple enough (e.g., a single return statement). If this fails, we will fall back to generating monadic code by generating syntax for each element of the body separately.
          let spl ← splitList bodyElems.toList
          let bodyStx ← withoutCheck do
              getCode spl `term
          let t ← `(def $nameIdent := fun $argIdents* ↦ $bodyStx)
          return t
        catch e =>
          IO.eprintln s!"Could not generate pure function: {← e.toMessageData.toString}"
        for elem in bodyElems do
            let elemStx ← withoutCheck do
                getCode elem `doElem
            bodyStxArray := bodyStxArray.push elemStx
            -- IO.eprintln s!"Generated syntax for function body element"  -- Debugging output
            -- IO.eprintln s!"Variables: {(← get).varNames.toList}"  -- Debugging output
        let idRunIdent := mkIdent ``Id.run
        if argIdents.isEmpty then
          `(def $nameIdent := $idRunIdent do
              $[$bodyStxArray:doElem]*)
        else
          let cmd ← `(def $nameIdent := fun $argIdents* ↦ $idRunIdent do
              $[$bodyStxArray:doElem]*)
          -- IO.eprintln s!"Generated (monadic) syntax for FunctionDef node: \n{← PrettyPrinter.ppCommand cmd}" -- Debugging output
          return cmd
    | kind, _ => throwError s!"Unsupported syntax category `{kind}` for FuncDef node"

@[pygen "Head_Assign"]
def assignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assign node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
            getCode splitRest `term
        `(let $nameIdent := $valueStx
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_Assign node"

@[pygen "Head_Return"]
def returnHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ←
          withoutCheck do
          getCode value `term
        return valueStx
    | _, _ => throwError s!"Unsupported syntax category for Head_Return node"

def f := fun n =>
      let x := n -ₚ 1
      let y := x *ₚ 2
      x +ₚ y

def f' := fun n =>
    Id.run do
      let mut x := n -ₚ 1
      let y := x *ₚ 2
      x := y -ₚ 1
      return x +ₚ y

def sumToNWithRec (n: Nat) : Nat :=
  let rec sumToN (n: Nat) :=
    match n with
    | 0 => 0
    | m + 1 =>  sumToN m + (m + 1)
  sumToN n

def sumToNWithRec' (n: Nat)  := Id.run do
    let mut sum := 0
    let mut i := 0
    while i < n do
      sum := sum + (i + 1)
      i := i + 1
    return sum

-- #check sumToNWithRec'
-- #check Id.run
-- #print Id.run
-- #print Id
