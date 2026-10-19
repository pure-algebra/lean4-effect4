import Tools.View.Live
import Tools.WireText
import Tools.View.Tokens
import Effect4.Store.Domain.ProgramWire

/-!
# The live driver: one session request a line in, its patch rows out

    lake env lean --run tools/Drivers/Live.lean [FLAGS] < requests.jsonl
    lake env lean --run tools/Drivers/Live.lean [FLAGS] build NAME

It holds one tool state and its retained picture (`Tools.View.Live`). It reads one request
envelope a line, as `tools/Drivers/Workspace.lean` reads them (`Tools.WireText`), from its standard input or from the
build of a corpus program (`Build.requests`, with `build NAME`). For each request it writes the
answer, one JSON object, to its standard error, and the patch rows to its standard output, ending
with `E`. A blank line is skipped, and a line that does not read is answered with its refusal.

`tools/view/play --live` reads the rows from a pipe, applies them to a retained store
(`tools/view/scene.h`) and paints each frame:

    lake env lean --run tools/Drivers/Live.lean build pFork | tools/view/play --live

The flags: `--look LOOK`, a look by its name in `tools/view/looks/` or its token file (default:
the dark look); `--check DIR`, which
also writes each step's patch as `DIR/NNN.patch` and the whole stream of the same page as
`DIR/NNN.draw`, so `tools/view/scene_test` can compare the store's stream with Lean's, byte for
byte.
-/

open Tools.View Tools.View.Live

/-- The settings of a run: the look's file, if any, and the folder of the check, if any. -/
structure Flags where
  look : Option String := none
  check : Option System.FilePath := none

/-- Read the flags before the command. -/
def flagsOf : List String → Flags × List String
  | "--look" :: l :: rest =>
    let (f, rest) := flagsOf rest
    ({ f with look := some l }, rest)
  | "--check" :: d :: rest =>
    let (f, rest) := flagsOf rest
    ({ f with check := some d }, rest)
  | rest => ({}, rest)

/-- A frame's number, in three digits. -/
def frameName (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- The look a `--look` names: the dark look by default or by name, a file of `tools/view/looks/`
by its name, or a token file by its path, read over the dark look. -/
def lookOf : Option String → IO Look
  | none | some "dark" => pure {}
  | some l => do
    let path : System.FilePath := if l.endsWith ".json" then l else s!"tools/view/looks/{l}.tokens.json"
    let name := (path.fileName.getD "look").replace ".tokens.json" ""
    match Tokens.parseLook {} name (← IO.FS.readFile path) with
    | .ok L => pure L
    | .error why => throw (IO.userError s!"live: the look {path} is refused at {why}")

/-- Answer one request: write its answer to standard error and its patch rows to standard output,
and, with a check folder, the patch and the whole stream of the page. -/
def answer (s : Settings) (check : Option System.FilePath) (st : State) (r : Effect4.Tool.Request) :
    IO State := do
  let (st', ans, rows) := step s "live" st r
  (← IO.getStderr).putStrLn (Tools.WireText.replyLine ans)
  if !rows.isEmpty then
    let out ← IO.getStdout
    for row in rows do out.putStrLn row
    out.flush
    if let some dir := check then
      IO.FS.writeFile (dir / s!"{frameName st'.frame}.patch") ("\n".intercalate rows ++ "\n")
      IO.FS.writeFile (dir / s!"{frameName st'.frame}.draw") ("\n".intercalate (wholeStream s st') ++ "\n")
  pure st'

def main (args : List String) : IO UInt32 := do
  let (flags, args) := flagsOf args
  let s : Settings := { look := ← lookOf flags.look }
  if let some dir := flags.check then IO.FS.createDirAll dir
  match args with
  | ["build", name] =>
    match List.lookup name Effect4.Program.Wire.Corpus.all >>= Build.requests with
    | none =>
      IO.eprintln s!"live: no corpus program {name} with a build; the programs are {Effect4.Program.Wire.Corpus.all.map (·.1)}"
      return 2
    | some reqs =>
      let mut st : State := {}
      for r in reqs do st ← answer s flags.check st r
      return 0
  | [] =>
    let stdin ← IO.getStdin
    let mut st : State := {}
    repeat do
      let line ← stdin.getLine
      if line.isEmpty then break
      let text := line.trimAscii.toString
      if text.isEmpty then continue
      match Tools.WireText.readRequest text with
      | .ok r => st ← answer s flags.check st r
      | .error why =>
        (← IO.getStderr).putStrLn (Lean.Json.mkObj [("refused", .str why)]).compress
    return 0
  | _ =>
    IO.eprintln "usage: live [--look FILE] [--check DIR] [build NAME]   (requests one a line on standard input)"
    return 2
