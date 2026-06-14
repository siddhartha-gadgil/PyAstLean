import Lean
import PyAstLeanTest.MiniRegex

open Lean
open PyAstLeanTest.MiniRegex

namespace PyAstLeanTest

structure CheckSpec where
  target : String := "term"
  exitCode : UInt32 := 0
  check : Array String := #[]
  checkErr : Array String := #[]
  checkNot : Array String := #[]
  checkErrNot : Array String := #[]
  checkExact : Option String := none
  checkErrExact : Option String := none

def valueAfter? (_prefix line : String) : Option String :=
  if line.startsWith _prefix then
    some <| (line.drop _prefix.length).toString.trimAscii.toString
  else
    none

def normalizeLine (rawLine : String) : String :=
  let line := rawLine.trimAscii.toString
  if line.startsWith "#" then
    (line.drop 1).toString.trimAscii.toString
  else
    line

def parseDirective (pyPath : System.FilePath) (lineNo : Nat) (line : String) (spec : CheckSpec) :
    Except String CheckSpec := do
  if let some v := valueAfter? "TARGET:" line then
    return { spec with target := v }
  else if let some v := valueAfter? "EXIT:" line then
    let some n := v.toNat? | throw s!"{pyPath}:{lineNo}: invalid EXIT value: {v}"
    return { spec with exitCode := UInt32.ofNat n }
  else if let some v := valueAfter? "CHECK-ERR-NOT:" line then
    return { spec with checkErrNot := spec.checkErrNot.push v }
  else if let some v := valueAfter? "CHECK-NOT:" line then
    return { spec with checkNot := spec.checkNot.push v }
  else if let some v := valueAfter? "CHECK-ERR-EXACT:" line then
    return { spec with checkErrExact := some v }
  else if let some v := valueAfter? "CHECK-EXACT:" line then
    return { spec with checkExact := some v }
  else if let some v := valueAfter? "CHECK-ERR:" line then
    return { spec with checkErr := spec.checkErr.push v }
  else if let some v := valueAfter? "CHECK:" line then
    return { spec with check := spec.check.push v }
  else
    throw s!"{pyPath}:{lineNo}: unknown directive: {line}"

def parseSpecFromPython (pyPath : System.FilePath) (source : String) : Except String CheckSpec := do
  let mut spec : CheckSpec := {}
  let mut lineNo := 0
  let mut inBlock := false
  let mut sawStart := false
  let mut sawEnd := false
  for rawLine in source.splitOn "\n" do
    lineNo := lineNo + 1
    let line := normalizeLine rawLine
    if line == "PYASTLEANCHECK START" then
      if inBlock then
        throw s!"{pyPath}:{lineNo}: nested PYASTLEANCHECK START is not allowed."
      if sawStart then
        throw s!"{pyPath}:{lineNo}: multiple PYASTLEANCHECK blocks are not supported."
      inBlock := true
      sawStart := true
      continue
    if line == "PYASTLEANCHECK END" then
      if !inBlock then
        throw s!"{pyPath}:{lineNo}: PYASTLEANCHECK END without START."
      inBlock := false
      sawEnd := true
      continue
    if !inBlock || line.isEmpty then
      continue
    spec ← parseDirective pyPath lineNo line spec
  if inBlock then
    throw s!"{pyPath}: missing PYASTLEANCHECK END."
  if !sawStart then
    throw s!"{pyPath}: missing PYASTLEANCHECK START block."
  if !sawEnd then
    throw s!"{pyPath}: missing PYASTLEANCHECK END."
  if spec.check.isEmpty && spec.checkErr.isEmpty && spec.checkExact.isNone && spec.checkErrExact.isNone then
    throw s!"{pyPath}: no CHECK directives found inside PYASTLEANCHECK block."
  return spec

abbrev CaptureEnv := Std.HashMap String String
abbrev CaptureDefs := Array (String × Nat)

def tokenRegex : Regex :=
  Regex.parse! r"\[\[([A-Za-z_][A-Za-z0-9_]*)(?::(.*?))?\]\]"

def normalizeLESymbols (s : String) : String :=
  (s.replace "\\<=" "≤").replace "<=" "≤"

def isRegexMeta (c : Char) : Bool :=
  c == '\\' || c == '^' || c == '$' || c == '.' || c == '|' || c == '?' || c == '*' ||
  c == '+' || c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}'

def escapeRegexChar (c : Char) : String :=
  if isRegexMeta c then "\\" ++ String.singleton c else String.singleton c

def escapeRegexLiteral (s : String) : String :=
  String.join <| s.toList.map escapeRegexChar

def whitespaceRegex : String :=
  "[ \t\r\n]+"

def isPatternWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

partial def literalToRegexAux : List Char → String
  | '\\' :: '.' :: rest => "\\." ++ literalToRegexAux rest
  | '.' :: rest => ".+" ++ literalToRegexAux rest
  | c :: rest =>
      if isPatternWhitespace c then
        whitespaceRegex ++ literalToRegexAux (rest.dropWhile isPatternWhitespace)
      else
        escapeRegexChar c ++ literalToRegexAux rest
  | [] => ""

def literalToRegex (s : String) : String :=
  literalToRegexAux s.toList

def parseTokenText? (tok : String) : Option (String × Option String) := do
  let groups ← tokenRegex.capture tok
  let name ← groups.get 1
  let rx := groups.get 2
  some (name, rx)

def consumeFirstSuffix? (text pattern : String) : Option (String × String) :=
  if pattern.isEmpty then
    none
  else
    match text.splitOn pattern with
    | before :: after =>
      if after.isEmpty then
        none
      else
        some (before, String.intercalate pattern after)
    | [] => none

def compilePattern (name : String) (pattern : String) (env : CaptureEnv) :
    Except String (String × CaptureDefs) := do
  let pattern := normalizeLESymbols pattern
  let tokens := tokenRegex.findAll pattern
  let mut regex := ""
  let mut rem := pattern
  let mut captureDefs : CaptureDefs := #[]
  let mut groupIdx := 1
  for tok in tokens do
    let some (literal, suffix) := consumeFirstSuffix? rem tok
      | throw s!"[{name}] internal error: token desync while compiling pattern."
    regex := regex ++ literalToRegex literal
    let some parsed := parseTokenText? tok
      | throw s!"[{name}] internal error: malformed token text: {tok}"
    let capName := parsed.1
    match parsed.2 with
    | some rxSlice =>
      if env.contains capName then
        throw s!"[{name}] pattern redefines [[{capName}:...]] after it was already captured."
      if captureDefs.any (fun p => p.1 == capName) then
        throw s!"[{name}] pattern captures [[{capName}:...]] more than once."
      regex := regex ++ "(" ++ rxSlice ++ ")"
      captureDefs := captureDefs.push (capName, groupIdx)
      groupIdx := groupIdx + 1
    | none =>
      let some v := env.get? capName
        | throw s!"[{name}] pattern references unknown [[{capName}]] before capture."
      regex := regex ++ escapeRegexLiteral v
    rem := suffix
  regex := regex ++ literalToRegex rem
  return (regex, captureDefs)

def previewText (text : String) (limit : Nat := 800) : String :=
  let trimmed := text.trimAscii.toString
  if trimmed.isEmpty then
    "<empty>"
  else if trimmed.length <= limit then
    trimmed
  else
    trimmed.take limit |>.toString ++ "\n... <truncated>"

def runOrdered (name : String) (text : String) (checks : Array String) :
    Except String Unit := do
  let mut rem := normalizeLESymbols text
  let mut env : CaptureEnv := {}
  for idx in [0:checks.size] do
    let check := checks[idx]!
    let (regexSrc, captureDefs) ← compilePattern name check env
    let regex ←
      match Regex.parse regexSrc with
      | .ok r => pure r
      | .error e => throw s!"[{name}] invalid CHECK regex at index {idx + 1}: {repr e}\nPattern: {check}"
    let some caps := regex.capture rem
      | throw s!"[{name}] CHECK #{idx + 1} failed.\nExpected:\n{check}\n\nGot remaining output:\n{previewText rem}"
    let some whole := caps.get 0
      | throw s!"[{name}] internal error: missing whole-match capture."
    let wholeTxt := whole
    if wholeTxt.isEmpty then
      throw s!"[{name}] CHECK #{idx + 1} matched an empty string; this is not allowed."
    for (capName, groupId) in captureDefs do
      match caps.get groupId with
      | some s =>
        if !env.contains capName then
          env := env.insert capName s
      | none => pure ()
    let some (_, suffix) := consumeFirstSuffix? rem wholeTxt
      | throw s!"[{name}] internal error: could not advance after CHECK #{idx + 1}."
    rem := suffix

def runAbsent (name : String) (text : String) (checks : Array String) (env : CaptureEnv) :
    Except String Unit := do
  let text := normalizeLESymbols text
  for idx in [0:checks.size] do
    let check := checks[idx]!
    let (regexSrc, _) ← compilePattern name check env
    let regex ←
      match Regex.parse regexSrc with
      | .ok r => pure r
      | .error e => throw s!"[{name}] invalid CHECK-NOT regex at index {idx + 1}: {repr e}\nPattern: {check}"
    if regex.test text then
      throw s!"[{name}] CHECK-NOT #{idx + 1} failed.\nForbidden pattern:\n{check}\n\nGot output:\n{previewText text}"

def runExact (name : String) (actual : String) (expected? : Option String) : Except String Unit := do
  match expected? with
  | none => pure ()
  | some expected =>
    let actualNorm := (normalizeLESymbols actual).trimAscii.toString
    let expectedNorm := (normalizeLESymbols expected).trimAscii.toString
    unless actualNorm == expectedNorm do
      throw s!"[{name}] exact match failed.\nExpected:\n{expected}\n\nActual:\n{actual}"

def runMatcher (name : String) (text : String) (check : Array String) (checkNot : Array String)
    (exact : Option String) : Except String Unit := do
  runOrdered name text check
  let mut env : CaptureEnv := {}
  -- Build the environment from CHECK lines so CHECK-NOT can reference prior captures.
  let mut rem := normalizeLESymbols text
  for checkLine in check do
    let (regexSrc, captureDefs) ← compilePattern name checkLine env
    let regex ←
      match Regex.parse regexSrc with
      | .ok r => pure r
      | .error e => throw s!"[{name}] invalid CHECK regex: {repr e}\nPattern: {checkLine}"
    let some caps := regex.capture rem
      | throw s!"[{name}] missing ordered fragment:\n{checkLine}"
    let some whole := caps.get 0
      | throw s!"[{name}] internal error: missing whole-match capture."
    let wholeTxt := whole
    if wholeTxt.isEmpty then
      throw s!"[{name}] CHECK matched an empty string; this is not allowed."
    for (capName, groupId) in captureDefs do
      match caps.get groupId with
      | some s =>
        if !env.contains capName then
          env := env.insert capName s
      | none => pure ()
    let some (_, suffix) := consumeFirstSuffix? rem wholeTxt
      | throw s!"[{name}] internal error: could not advance after CHECK."
    rem := suffix
  runAbsent name text checkNot env
  runExact name text exact

/-- Wrap generated Lean output in a minimal module so PALC can elaborate it.

`--target command` output is already a complete module (it carries its own
`import PyAstLean` / `import Libraries` / `open` preamble), so it is emitted verbatim — adding
another `import … namespace …` wrapper would push those generated `import`s below the top of
the file, which Lean rejects. Only the bare-expression `term` target needs wrapping. -/
def wrappedGeneratedLean (target generated : String) : String :=
  if target == "command" then
    generated.trimAscii.toString ++ "\n"
  else
    String.intercalate "\n"
      [ "import PyAstLean"
      , "open PyAstLean"
      , "namespace PALCGenerated"
      , ""
      , s!"#check {generated.trimAscii.toString}\n"
      , "end PALCGenerated"
      ]

/-- Compile the generated Lean code in a scratch module so passing PALC cases also elaborate. -/
def compileGeneratedLean (pyPath : System.FilePath) (target generated : String) :
    IO (Except String Unit) := do
  let stamp ← IO.monoMsNow
  let tmpPath := System.FilePath.mk s!"/tmp/pyastlean_palc_{stamp}.lean"
  let wrapped := wrappedGeneratedLean target generated
  IO.FS.writeFile tmpPath wrapped
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", tmpPath.toString]
  }
  try
    IO.FS.removeFile tmpPath
  catch _ =>
    pure ()
  if out.exitCode == 0 then
    return .ok ()
  else
    return .error
      s!"{pyPath}: generated Lean failed to compile.\nGENERATED:\n{wrapped}\n\nSTDERR:\n{out.stderr}\nSTDOUT:\n{out.stdout}"

def runOneCase (pyPath : System.FilePath) : IO (Except String Unit) := do
  let pyPathStr := pyPath.toString
  if !pyPathStr.endsWith ".py" then
    return .error s!"Not a python file: {pyPathStr}"
  let source ← IO.FS.readFile pyPath
  let spec ←
    match parseSpecFromPython pyPath source with
    | .ok s => pure s
    | .error err => return .error err
  let out ← IO.Process.output {
    cmd := "python3"
    -- `--strict` keeps golden tests deterministic: the best-effort fallback is the CLI default,
    -- but PALC must exercise real (strict) translation, incl. expected-failure cases.
    args := #[ "src/py2lean.py", pyPathStr, "--target", spec.target, "--strict" ]
  }
  if out.exitCode != spec.exitCode then
    return .error s!"{pyPathStr}: expected exit {spec.exitCode}, got {out.exitCode}\nSTDOUT:\n{out.stdout}\nSTDERR:\n{out.stderr}"
  let stdoutResult := runMatcher pyPathStr out.stdout spec.check spec.checkNot spec.checkExact
  match stdoutResult with
  | .error err => return .error err
  | .ok _ =>
    let stderrResult := runMatcher s!"{pyPathStr} (stderr)" out.stderr spec.checkErr spec.checkErrNot spec.checkErrExact
    match stderrResult with
    | .error err => return .error err
    | .ok _ =>
      if spec.exitCode == 0 then
        if spec.target == "term" then
          return .ok ()
        else
          compileGeneratedLean pyPath spec.target out.stdout
      else
        return .ok ()

def defaultCasesDir : System.FilePath :=
  System.FilePath.mk "PyAstLeanTest/PyAstLeanCheck/Cases"

def resolveCaseArg (arg : String) : IO (Except String System.FilePath) := do
  let direct := System.FilePath.mk arg
  if ← direct.pathExists then
    return .ok direct
  let underCases := defaultCasesDir / arg
  if ← underCases.pathExists then
    return .ok underCases
  let withPy :=
    if arg.endsWith ".py" then
      underCases
    else
      defaultCasesDir / s!"{arg}.py"
  if ← withPy.pathExists then
    return .ok withPy
  return .error s!"No such test case: {arg}"

def listCaseFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let out ← IO.Process.output {
    cmd := "bash"
    args := #[
      "-lc",
      s!"find {dir} -type f -name '*.py' | sort"
    ]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Failed to list test files:\n{out.stderr}"
  return (out.stdout.splitOn "\n").foldl (init := #[]) (fun acc line =>
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then acc else acc.push (System.FilePath.mk trimmed))

def runCases (cases : Array System.FilePath) : IO Unit := do
  if cases.isEmpty then
    IO.println "PyLeanCheck: no test cases found."
  let mut failures : Array String := #[]
  let mut totalTime := 0
  for casePath in cases do
    -- Timer
    let startTime ← IO.monoMsNow
    let caseOut ← runOneCase casePath
    let endTime ← IO.monoMsNow
    let duration := endTime - startTime
    totalTime := totalTime + duration
    match caseOut with
    | .ok _ =>
      IO.println s!"[PALC] PASS {casePath} ({duration} ms)"
    | .error err =>
      failures := failures.push s!"[PALC] FAIL {err} ({duration} ms)"
  if failures.isEmpty then
    IO.println s!"[PALC] {cases.size} / {cases.size} cases passed."
    IO.println s!"[PALC] Total time: {totalTime} ms"
  else
    IO.println s!"[PALC] {failures.size} / {cases.size} cases failed."
    IO.println s!"[PALC] Total time: {totalTime} ms"
    throw <| IO.userError (String.intercalate "\n\n" failures.toList)

def runPALCSuite : IO Unit := do
  let cases ← listCaseFiles defaultCasesDir
  runCases cases

def printUsage : IO Unit := do
  IO.println "PyAstLeanCheck (PALC) - Testing framework for Python to Lean translation"
  IO.println "Usage:"
  IO.println "  lake exe palc"
  IO.println "  lake exe palc <case>"
  IO.println "  lake exe palc <case1> <case2> ..."
  IO.println ""

def runPALCMain (args : List String) : IO UInt32 := do
  if args.any (fun arg => arg == "-h" || arg == "--help") then
    printUsage
    return 0
  if args.isEmpty then
    runPALCSuite
    return 0
  let mut cases : Array System.FilePath := #[]
  for arg in args do
    match ← resolveCaseArg arg with
    | .ok path => cases := cases.push path
    | .error err =>
        IO.eprintln err
        return 1
  runCases cases
  return 0

end PyAstLeanTest
