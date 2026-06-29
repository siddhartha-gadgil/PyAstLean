import Lean
import PastaLean
open Lean Meta Elab Term Qq Std
open PastaLean

def backendModules : Array Import := #[
  { module := `PastaLean },
  { module := `Mathlib },
  -- `Libraries` is imported so the `proveFile` pass can elaborate generated programs that
  -- `open Libraries` (numpy/scipy shims) without a second cold import of Mathlib.
  { module := `Libraries }
]

unsafe def initBackend : IO (Core.Context × Environment) := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) backendModules {}
  let ctx : Core.Context := {
    fileName := "<py2lean>"
    fileMap := default
  }
  pure (ctx, env)

def errorResponse (message : String) : Json :=
  Json.mkObj [("result", Json.bool false), ("error", Json.str message)]

def sanitizeLeanOutput (code : String) : String :=
  code.replace "✝" ""

def successResponse (target : String) (code : Format) : Json :=
  Json.mkObj [("result", Json.bool true), ("lean_" ++ target, Json.str <| sanitizeLeanOutput code.pretty)]

def ensureTarget (jsonTask : Json) (target : String) : Json :=
  match jsonTask.getObjVal? "target" with
  | .ok _ => jsonTask
  | .error _ => (Json.mkObj [("target", Json.str target)]).mergeObj jsonTask

def runTranslateTask (jsonTask : Json) (ctx : Core.Context) (env : Environment) : IO Json := do
  let target := jsonTask.getObjValAs? String "target" |>.toOption.getD "term"
  let checkCode := jsonTask.getObjValAs? Bool "check" |>.toOption.getD true
  -- Per-request numeric mode (default exact = ℚ). Set before codegen so the literal/annotation
  -- sites lower `float` to `ℚ` or `Float` accordingly.
  let mode := jsonTask.getObjValAs? String "numericMode" |>.toOption.getD "exact"
  PastaLean.numericModeRef.set (if mode == "approx" then .approx else .exact)
  -- Run-twin suffixing (`--mode both`): when emitting the runnable twin, `runSuffix` is `'rn` and
  -- `userNames` lists the user's functions/classes whose references should also be suffixed.
  PastaLean.runSuffixRef.set (jsonTask.getObjValAs? String "runSuffix" |>.toOption.getD "")
  PastaLean.userNamesRef.set ((jsonTask.getObjValAs? (Array String) "userNames" |>.toOption.getD #[]).toList)
  let .ok json := jsonTask.getObjValAs? Json "ast"
    | return errorResponse "Invalid JSON: missing 'ast' field or it is not a JSON value"
  let code? ← getCodeIO json target.toName ctx env checkCode
  pure <| match code? with
    | .ok code => successResponse target code
    | .error err => errorResponse err

/-- Drop `import …` lines from generated Lean text. The backend has already imported everything at
boot, so the `proveFile` pass elaborates only the *commands* (opens, set_options, defs, theorems). -/
def stripImports (code : String) : String :=
  String.intercalate "\n" <|
    (code.splitOn "\n").filter (fun l => ¬ l.trimAscii.startsWith "import ")

/-- Elaborate an already-generated program (with `:= by taste?` proof obligations) into the warm
boot `env`, letting the `taste?` tactic search each assert and record its winning tactic string into
`PastaLean.tasteWinnersRef`. Returns the winners in elaboration order (one per `taste?`), so the
Python driver can splice each back over the matching `taste?` token. No Mathlib re-import. -/
def runProveFileTask (jsonTask : Json) (env : Environment) : IO Json := do
  let .ok code := jsonTask.getObjValAs? String "code"
    | return errorResponse "proveFile: missing 'code' field or it is not a string"
  PastaLean.tasteWinnersRef.set #[]
  let src := stripImports code
  -- `stripImports` drops the leading `import …` lines, so byte offsets recorded against `src` are
  -- shifted left by exactly those removed prefix bytes. Add them back so each winner's `pos` is an
  -- offset into the *original* `code` the Python splicer walks.
  let shift := code.toUTF8.size - src.toUTF8.size
  let inputCtx := Parser.mkInputContext src "<proveFile>"
  let cmdState := Command.mkState env {} {}
  let frontendState ← Lean.Elab.IO.processCommands inputCtx {} cmdState
  let winners ← PastaLean.tasteWinnersRef.get
  let hasErrors := frontendState.commandState.messages.hasErrors
  pure <| Json.mkObj [
    ("result", Json.bool true),
    ("winners", Json.arr (winners.map (fun (off, p) =>
      Json.mkObj [("pos", toJson (off + shift)), ("proof", Json.str p)]))),
    ("hasErrors", Json.bool hasErrors)
  ]

def handleTaskJson (jsonTask : Json) (ctx : Core.Context) (env : Environment) : IO Json := do
  let .ok task := jsonTask.getObjValAs? String "task"
    | return errorResponse "Invalid JSON: missing 'task' field or it is not a string"
  match task with
  | "translate" => runTranslateTask jsonTask ctx env
  | "proveFile" => runProveFileTask jsonTask env
  | _ => pure <| errorResponse s!"Unknown task: {task}"

def handleTaskString (payload : String) (ctx : Core.Context) (env : Environment) : IO Json := do
  match Json.parse payload with
  | .ok jsonTask => handleTaskJson jsonTask ctx env
  | .error err => pure <| errorResponse s!"Error parsing JSON: {err}"

partial def readLine (stdin : IO.FS.Stream) : IO String := do
  let mut bytes := ByteArray.empty
  while true do
    let chunk ← stdin.read 1
    if chunk.isEmpty then
      break
    if chunk[0]! == '\n'.toUInt8 then
      break
    bytes := bytes.append chunk
  return String.fromUTF8? bytes |>.getD ""

partial def runServerLoop (stdin stdout : IO.FS.Stream) (ctx : Core.Context) (env : Environment) : IO UInt32 := do
  let rawLine ← readLine stdin
  if rawLine.isEmpty then
    return 0
  let line := rawLine.trimAscii.toString
  if line.isEmpty then
    runServerLoop stdin stdout ctx env
  else
    let response ← handleTaskString line ctx env
    stdout.putStr <| Lean.Json.compress response ++ "\n"
    stdout.flush
    runServerLoop stdin stdout ctx env

def runSingleTask (payload : String) (defaultTarget : String) (ctx : Core.Context)
    (env : Environment) : IO UInt32 := do
  let stdout ← IO.getStdout
  match Json.parse payload with
  | .ok jsonTask =>
      let response ← handleTaskJson (ensureTarget jsonTask defaultTarget) ctx env
      stdout.putStr <| Lean.Json.compress response ++ "\n"
      stdout.flush
      return 0
  | .error err =>
      IO.eprintln s!"Error parsing JSON: {err}"
      return 1

unsafe def main(args : List String) : IO UInt32 := do
  let (ctx, env) ← initBackend
  match args with
  | "--server" :: _ =>
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      runServerLoop stdin stdout ctx env
  | jsStr :: rest =>
      runSingleTask jsStr (rest.headD "term") ctx env
  | [] =>
      IO.eprintln "No JSON input provided"
      return 1
