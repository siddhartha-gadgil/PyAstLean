import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
open Lean Meta Elab Term Qq Std

namespace PyAstLean

open Lean.Parser.Term

/-!
  Translates a Python function definition to a Lean function definition. For now, this is a very basic implementation that only handles simple function definitions with no parameters and a single return statement. The main function is `funcDefSyntax`, which takes a JSON object representing a Python function definition and returns the corresponding Lean syntax.
-/

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok idStr := target.getObjValAs? String "id" | throwError
          s!"Assign target does not have an 'id' field or it is not a string: {target}"
        let nameIdent := mkIdent idStr.toName
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(def $nameIdent : _ := $valueStx)
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok idStr := target.getObjValAs? String "id" | throwError
          s!"Assign target does not have an 'id' field or it is not a string: {target}"
        let nameIdent := mkIdent idStr.toName
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(doElem| let $nameIdent := $valueStx)
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
        let bodyStxArray ← bodyElems.mapM (fun elem =>
            withoutCheck do
                getCode elem `doElem)
        let idRunIdent := mkIdent ``Id.run
        if argIdents.isEmpty then
          `(def $nameIdent := $idRunIdent do
              $[$bodyStxArray:doElem]*)
        else
          let cmd ← `(def $nameIdent := fun $argIdents* => $idRunIdent do
              $[$bodyStxArray:doElem]*)
          IO.eprintln s!"Generated syntax for FunctionDef node: \n{← PrettyPrinter.ppCommand cmd}" -- Debugging output
          return cmd
    | kind, _ => throwError s!"Unsupported syntax category `{kind}` for FuncDef node"

def f := fun n =>
      let x := n +ₚ 1
      let y := x *ₚ 2
      x +ₚ y
