import Lean
import PyAstLean
open Lean Meta Elab Term Qq Std
open PyAstLean

unsafe def main(args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args[0]? with
  | some jsStr =>
    let env ←
    importModules (loadExts := true) #[
    {module := `PyAstLean},
    {module := `Mathlib}] {}
    let ctx: Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}}
    match Json.parse jsStr with
    | .ok jsonTask =>
      let .ok task := jsonTask.getObjValAs? String "task" | IO.throwServerError "Invalid JSON: missing 'task' field or it is not a string"
      IO.eprintln s!"Received task: {task}"  -- Debugging output
      match task with
      | "translate" =>
        let target := args[1]?.getD "term"
        let .ok json := jsonTask.getObjValAs? Json "ast" | IO.throwServerError "Invalid JSON: missing 'ast' field or it is not a JSON value"
        let code? ← getCodeIO json target.toName ctx env
        match code? with
        | .ok code =>
          let jsCode := Json.mkObj [("result", Json.bool true), ("lean_expression", code.pretty)]
          IO.println jsCode
        | .error err =>
          let jsCode := Json.mkObj [("result", Json.bool false), ("error", Json.str err)]
          IO.println jsCode
      | _ => IO.throwServerError s!"Unknown task: {task}"
    | .error err => IO.throwServerError s!"Error parsing JSON: {err}"
  | none => IO.throwServerError "No JSON input provided"
