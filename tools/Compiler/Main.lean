import Compiler.Native
import Compiler.Run
import Compiler.Inspect
import Compiler.InspectDocument
import Compiler.Report
import Effect4.Api.Session
import Compiler.Elaborated

/-!
# Compiler.Main — the compiler's entry point

`Compiler.main app args` is the compiler's command line over one application
(`docs/research/2026-10-20-compiler-entry/README.md`, C2 slice 1). A project's executable calls it
by static import, as decision E1 asks: the value of a declaration loaded by name cannot be
evaluated without `unsafe`. The commands are the folds of §2, and nothing else:

    check [--out FILE.obj]
    open FILE.obj
    emit [--target ts|ocaml] [--check] [--out DIR] [--emit=module,surface,canonical,certificate,manifest]
    describe [--target ts|ocaml] [--out DIR] [--emit=…] [--pretty]
    inspect --what types|rows|surface|graph|manifest [the options of describe]
    inspect --what relations|boundary|calls|layers|handlers [--form md|json|svg|tsv] [--session SERVICE] [--out DIR]
    run [--text | --typed] [--script FILE] [--budget N]

**Every command returns a report** (`Compiler.Report`, the report note
`docs/research/2026-10-21-cli-report/README.md`) and prints nothing itself: the folds it ran, its
measures, the artifacts it wrote with their digests, the readings it gives and its refusals. The
printing is one place, `Report.print`, in the format the flags choose. The flags are read before
the command, from anywhere on the line, so no command's own reader sees them:

| Flag | Meaning |
| --- | --- |
| `--format tty\|plain\|json\|md`, `--format=F` | the format; `tty` when the standard output is a terminal and `NO_COLOR` is unset, else `plain` |
| `--quiet` | the refusals' words alone, on the error stream; nothing on success |
| `--json` | an alias of `--format json`, kept for one release; it was each command's own JSON output |
| `--help`, `--version` | the usage, or the version, as a reading; exit `0` |
| `--` | ends the flags; the rest of the line is the command's as given |
| `--group NAME` | `lake exe effect4`: the source, one of the tree's groups (`mainOver`) |

The streams (decisions row 444 (7)): `tty` and `plain` are for a person and go to the error
stream; `json` and `md` are the requested result and go to the standard output, a failed report
included. The exit code is `0`, `1` on a refusal, `2` on a usage error. A flag that reads wrong
keeps the format and the quiet read before it.

- `open FILE.obj` reads and admits a saved object, then gives its certificate as a reading.
  It needs no group, application source, prelude or host.
- `check` builds the application's service module (`Compiler.check`) and gives its certificate as
  a reading: as text, each service's key with the Lean names that declare it, with the same
  certificate as JSON beside it. A refusal is one located refusal, in its words.
  `--out FILE.obj` writes the admitted object, an artifact of the report; a refusal leaves that
  file unchanged.
- `emit` writes the checked emission into one folder (`Compiler.emitTs`), by default
  `.lake/effect4/<name>/<target>/`, each file an artifact of the report. `--emit` selects the
  kinds; the default is all of them. `--target ts` is the default. `--target ocaml` lowers the
  named roots through `lcnfgen`. `--check` compiles the native module, and never runs it.
- `describe` gives the manifest that `emit` with the same options would write, and writes
  nothing: as one line, or indented under `--pretty` (`prettyText`).
- `inspect` gives the object's address table, rows, graph, surface, or emission manifest
  (`Compiler.Inspect`) as a reading, its text with its JSON beside it.
  The relation readings give Markdown or JSON, or write SVG and TSV files under `--out DIR`, each
  an artifact of the report. `--session SERVICE` reads the session object made by `Built.session`.
  A multi-program JSON reading requires `--out DIR`, with one document per file.
  SVG and TSV replace the selected programs' files of that form in the output folder.
- `run` runs each request of a script on the Lean machine over the application's host, and gives
  one reading a request (`Compiler.Run`): a readable line (`--text`, the default) or the exit
  encoded at its own type (`--typed`), with the result's value tree as JSON beside it. The host
  and the default script are what the project passes to `Compiler.main`; `--script FILE` reads a
  JSON array of requests instead. `--budget N` plays every row at `N` steps of fuel. An application
  with no host refuses `run`, as a usage error.

`Compiler.mainOver groups args` is the same command line over named sources, one chosen by
`--group NAME` (`lake exe effect4`, `Compiler.Exe`, C2 slice 2). A source is one application, or a
group of programs, each admitted at the group's application (`Source`). Over a group, `check` and
`inspect` give each program's answer under its name, and `emit` writes one folder with one
manifest (`Compiler.emitGroup`).

**The inputs** (`readInputs`, `Compiler.Inputs`): the pins and the prelude are read from the library's checkout,
which the project's `lake-manifest.json` locates (`libraryRoot`). The executable's Lean module
closure is data it was built with (`Compiler.Elaborated`, the default of `main`'s `elaborated`), and
each module's source is read where `lake exe` puts it, on `LEAN_SRC_PATH` (`sourceOf`). So the
command runs from the project's root through `lake exe`. The exit code is the report's
(`Report.exit`): `0` on success, `1` on a refusal, and `2` on a usage error, which names the
command and its options (`usageOf`). A `run` whose request the build refuses gives the located
refusal as `check` does, runs the rest, and exits with `1`.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Program.Authoring
open Report (Log Event Format Written)

/-- A command's options, in words. -/
def usageOf : String → String
  | "check" => "check [--out FILE.obj]"
  | "open" => "open FILE.obj"
  | "emit" => "emit [--target ts|ocaml] [--check] [--out DIR] [--emit=KIND,…]"
  | "describe" => "describe [--target ts|ocaml] [--out DIR] [--emit=KIND,…] [--pretty]"
  | "inspect" => "inspect --what " ++ "|".intercalate (What.all.map What.name) ++
      " [--form md|json|svg|tsv] [--session SERVICE] [--out DIR]" ++
      " [--target ts|ocaml] [--emit=KIND,…]"
  | "run" => "run [--text | --typed] [--script FILE] [--budget N]"
  | _ => ""

/-- The kinds that `--emit` names and the available targets, in words. -/
def kindsText : String :=
  "a KIND is one of " ++ ", ".intercalate (Kind.selectable.map Kind.name) ++
    "; ts is the default target; ocaml lowers the declared roots"

/-- The report's flags, in words. -/
def flagsText : String := "[--format tty|plain|json|md] [--quiet] [--json] [--help] [--version] [--]"

/-- The command line, in words. -/
def usage : String :=
  "usage: " ++ " | ".intercalate (["check", "open", "emit", "describe", "inspect", "run"].map usageOf) ++
    "; each with " ++ flagsText ++ "; " ++ kindsText

/-! ## The report's flags -/

/-- **The report's flags**: the format, when one is named, `--quiet`, and the two requests that
end the line with exit `0`, `--help` and `--version`. -/
structure Flags where
  format : Option Format := none
  quiet : Bool := false
  help : Bool := false
  version : Bool := false
  deriving DecidableEq, Repr

/-- The format a word names, or why not. -/
def formatOf (word : String) : Except String Format :=
  match Format.parse word with
  | some format => .ok format
  | none => .error s!"--format {word} names no format; choose tty, plain, json or md"

/-- Read the report's flags from anywhere on the command line, and give the line without them:
`--format F`, `--format=F`, `--json` (the alias of `--format json`), `--quiet`, `--help`,
`--version`; `--` ends the flags and leaves the rest as given. A flag that reads wrong gives the
flags read so far, so the format and `--quiet` chosen before it still hold, and why. -/
def takeFlags : List String → Flags → Flags × Except String (List String)
  | [], f => (f, .ok [])
  | "--" :: rest, f => (f, .ok rest)
  | "--format" :: word :: rest, f =>
    match formatOf word with
    | .ok format => takeFlags rest { f with format := some format }
    | .error why => (f, .error why)
  | ["--format"], f => (f, .error "--format needs tty, plain, json or md")
  | "--json" :: rest, f => takeFlags rest { f with format := some .json }
  | "--quiet" :: rest, f => takeFlags rest { f with quiet := true }
  | "--help" :: rest, f => takeFlags rest { f with help := true }
  | "--version" :: rest, f => takeFlags rest { f with version := true }
  | a :: rest, f =>
    if a.startsWith "--format=" then
      match formatOf (a.drop 9).toString with
      | .ok format => takeFlags rest { f with format := some format }
      | .error why => (f, .error why)
    else
      match takeFlags rest f with
      | (f, .ok others) => (f, .ok (a :: others))
      | (f, .error why) => (f, .error why)

/-- What `--version` gives: the Effect profile the compiler prints for, and the Lean it is built with. -/
def versionText : String := s!"effect4 {rc112.name} lean {Lean.versionString}"

/-- The format when none is named: `tty` at a terminal with `NO_COLOR` unset, else `plain`. -/
def defaultFormat : IO Format := do
  if (← IO.getEnv "NO_COLOR").isSome then return .plain
  return if ← (← IO.getStdout).isTty then .tty else .plain

/-- **A usage error**: the command, why, and the command's options (`usageOf`); exit code `2`. -/
def usageError (log : Log) (command why : String) : IO Unit := do
  let kinds := if ["emit", "describe", "inspect"].contains command then s!"; {kindsText}" else ""
  log.event (.usage command s!"{why}; usage: {usageOf command}{kinds}")

/-- The optional single-object output file of `check`. -/
structure CheckOptions where
  out : Option String := none
  deriving DecidableEq

/-- Parse check options before checking or writing any program. -/
def CheckOptions.read : List String → CheckOptions → Except String CheckOptions
  | [], o => .ok o
  | "--out" :: file :: rest, o =>
    if file.startsWith "--" then .error "--out needs a file"
    else if o.out.isSome then .error "--out names one file only"
    else CheckOptions.read rest { o with out := some file }
  | ["--out"], _ => .error "--out needs a file"
  | arg :: _, _ => .error s!"{arg} is no option"

/-! ## The measures -/

/-- **A built program's measures**: its definitions, its rows, and the nodes and calls of its
relations (`Graphs.read`). -/
def measuresOf (b : Api.Built) : List (String × Nat) :=
  let relations := Graphs.read b
  [("definitions", b.program.defsOf.length), ("rows", b.table.length),
   ("nodes", relations.nodes.length), ("calls", relations.calls.length)]

/-- The measures of several built programs, summed by word. -/
def measuresOfAll (bs : List Api.Built) : List (String × Nat) :=
  match bs with
  | [] => []
  | b :: rest => (measuresOf b).map fun (word, n) =>
    (word, n + ((rest.map measuresOf).map fun ms => (ms.lookup word).getD 0).sum)

/-- Load a saved object without an application, then give its certificate as a reading. -/
def openCommand (log : Log) (args : List String) : IO Unit := do
  let file ← match args with
    | [file] =>
      if file.startsWith "--" then return (← usageError log "open" "name one object file")
      else pure file
    | _ => return (← usageError log "open" "name one object file")
  let loaded ← log.folding s!"reading the object {file}" do
    try
      let bytes ← IO.FS.readBinFile file
      match Object.load bytes.data.toList with
      | .ok b =>
        for (word, n) in measuresOf b do log.event (.measure word n)
        pure (some b)
      | .error why => log.event (.refusal "open" (jsonText (tree why))); pure none
    catch error => log.event (.refusal "open" s!"{file}: {error}"); pure none
  if let some b := loaded then
    log.event (.reading "certificate" (jsonText (certificate b)) (some (jsonText (certificate b))))

/-- The options of `emit` and `describe`: the target, the output folder, the kinds, and whether
`describe` indents the manifest. -/
structure Options where
  target : Option String := none
  out : Option String := none
  kinds : List Kind := Kind.selectable
  kindsGiven : Bool := false
  pretty : Bool := false
  nativeCheck : Bool := false

/-- Read the options of `emit` and `describe`, or name the argument that is none. -/
def Options.read : List String → Options → Except String Options
  | [], o => .ok o
  | "--target" :: t :: rest, o => Options.read rest { o with target := some t }
  | "--out" :: d :: rest, o => Options.read rest { o with out := some d }
  | "--check" :: rest, o => Options.read rest { o with nativeCheck := true }
  | "--pretty" :: rest, o => Options.read rest { o with pretty := true }
  | a :: rest, o =>
    if a.startsWith "--emit=" then
      match Kind.parse (a.drop 7).toString with
      | some kinds => Options.read rest { o with kinds, kindsGiven := true }
      | none => .error s!"{a} names no kind"
    else .error s!"{a} is no option"

/-- **What a command runs over**: one application, with the host and the script that `run` takes
when the project passes them; or a named group of programs, each admitted at the group's
application (`checkProgram`), the empty one by default, as the wire corpus is. -/
inductive Source where
  | application (app : Application NativeOp) (hosted : Option Hosted := none)
      (script : List Request := []) (lowered : Lowered := {})
  | programs (name : String) (programs : List (String × NativeEff)) (app : SigApp := {})

/-- A source's name: the application's, or the group's. It names the default output folder. -/
def Source.name : Source → String
  | .application app _ _ _ => app.name
  | .programs name _ _ => name

/-- The words of the fold that builds a source: the program's name, or the group's. -/
def Source.folding : Source → String
  | .application app _ _ _ => s!"folding the program {app.name}"
  | .programs name _ _ => s!"folding the group {name}"

/-- **What `run` runs over**: an application with its host and the script the project passes; or,
in words, why the source has no host. -/
def Source.hosted? : Source → Except String (Application NativeOp × Hosted × List Request)
  | .application app (some h) script _ => .ok (app, h, script)
  | .application app none _ _ =>
    .error s!"the application {app.name} has no host; a project passes one to Compiler.main (hosted := …)"
  | .programs name _ _ =>
    .error s!"the group {name} is programs with no host to answer a row; run takes an application and its host"

/-- **The source's programs, built**: the application's service module under its name
(`check`), or each program of the group under its own, at the group's application
(`checkProgram`); each built, or the build's refusal. -/
def builtOf : Source → List (String × Except CheckRefusal Api.Built)
  | .application app _ _ _ => [(app.name, check app)]
  | .programs _ programs app => programs.map fun (name, program) => (name, checkProgram program app)

/-- A build's refusal in words, as the report records it: a group's program by its name. -/
def refusalText (source : Source) (name : String) (why : CheckRefusal) : String :=
  match source with
  | .application .. => why.text
  | .programs .. => s!"the program {name}: " ++ why.text

/-- **The source built and measured**, inside the fold `Source.folding`: a group's programs
counted, the built programs' measures summed (`measuresOfAll`), and each refusal recorded. -/
def measured (log : Log) (source : Source) : IO (List (String × Except CheckRefusal Api.Built)) :=
  log.folding source.folding do
    let built := builtOf source
    if let .programs .. := source then log.event (.measure "programs" built.length)
    for (word, n) in measuresOfAll (built.filterMap fun (_, r) => r.toOption) do
      log.event (.measure word n)
    for (name, r) in built do
      if let .error why := r then log.event (.refusal "check" (refusalText source name why))
    return built

/-- Whether a build refused. -/
def anyRefused (built : List (String × Except CheckRefusal Api.Built)) : Bool :=
  built.any fun (_, r) => r.toOption.isNone

/-- `check`: the certificate as a reading, or the refusal. Over a group, each program's, under its
name; the command refuses when one program refuses. The text names the declarations of each
service's key (`Elaborated.namesOf`); the JSON beside it is the certificate's public JSON. -/
def checkCommand (log : Log) (source : Source) (elaborated : Elaborated) (out : Option String := none) :
    IO Unit := do
  if out.isSome then
    match source with
    | .programs _ programs _ =>
      unless programs.length == 1 do
        return (← usageError log "check" "--out needs exactly one program")
    | .application .. => pure ()
  let built ← measured log source
  if let some file := out then
    let path := System.FilePath.mk file
    let root := (path.parent.map (·.toString)).getD "."
    for (_, result) in built do
      if let .ok b := result then
        log.setOut root
        let bytes : ByteArray := ⟨(Object.ofBuilt b).bytes.toArray⟩
        let _ ← log.write "check" root (Written.of .program .object .object (path.fileName.getD file) bytes) bytes
  for (name, result) in built do
    match result, source with
    | .error _, _ => pure ()
    | .ok b, .application app _ _ _ =>
      let title := s!"{app.name}: checked; the service {serviceName app}"
      log.event (.reading "certificate" ("\n".intercalate (certificateLines title b elaborated.namesOf))
        (some (jsonText (certificate b))))
    | .ok b, .programs .. =>
      log.event (.reading s!"certificate of {name}"
        ("\n".intercalate (certificateLines s!"{name}: checked" b elaborated.namesOf))
        (some (jsonText (.obj [("program", .str name), ("certificate", certificate b)]))))

/-- What an emission is asked for (`Spec`): the prelude's folder and the inputs read from the
library's checkout and the source folders. -/
def readSpec (name : String) (command : List String) (kinds : List Kind) (elaborated : Elaborated) :
    IO Spec := do
  let root ← libraryRoot
  let prelude ← Prelude.folder (root / Prelude.source)
  let inputs ← readInputs root elaborated.modules
  return { name, command, kinds, prelude, inputs }

/-- **A source's emission**, recorded under `command`: an application checked before the library is
read, then emitted (`emitTs`); a group emitted program by program at its application (`emitGroup`).
A refusal, and an input that does not read, is text. -/
def emissionOf (source : Source) (command : List String) (kinds : List Kind)
    (elaborated : Elaborated) : IO (Except String Emission) := do
  try
    match source with
    | .application app _ _ _ =>
      match check app with
      | .error why => return .error why.text
      | .ok b => return (emitTs (← readSpec app.name command kinds elaborated) b).mapError (·.text)
    | .programs name programs app =>
      return (emitGroup (← readSpec name command kinds elaborated) programs app).mapError (·.text)
  catch e => return .error (toString e)

/-- **What an emission's command does with it**: `emit` writes its files; `describe` gives its
manifest, as one line or indented under `--pretty`; `inspect --what manifest` gives it indented. -/
inductive Output where
  | write
  | describe
  | inspect
  deriving DecidableEq

/-- The command an output belongs to. -/
def Output.name : Output → String
  | .write => "emit"
  | .describe => "describe"
  | .inspect => "inspect"

/-- `emit`, `describe` and `inspect --what manifest`: the emission of the options `rest`, recorded
under `command`; written, each file an artifact, or its manifest given as a reading. `ts` is the
target when none is named. -/
def emitCommand (log : Log) (source : Source) (elaborated : Elaborated) (output : Output)
    (command rest : List String) : IO Unit := do
  let name := output.name
  let o ← match Options.read rest {} with
    | .ok o => pure o
    | .error why => return (← usageError log name why)
  match output, o.pretty with
  | .write, true | .inspect, true =>
    return (← usageError log name "--pretty is describe's; inspect gives the manifest indented by default")
  | _, _ => pure ()
  let target := o.target.getD "ts"
  unless target == "ts" || target == "ocaml" do
    return (← usageError log name s!"--target {target} is no target here; choose ts or ocaml")
  if o.nativeCheck && (target != "ocaml" || output != .write) then
    return (← usageError log name "--check belongs to emit --target ocaml")
  if target == "ocaml" && o.kindsGiven && o.kinds.contains .surface then
    return (← usageError log name "ocaml emits no surface; choose module, canonical, certificate or manifest")
  let out := System.FilePath.mk (o.out.getD s!".lake/effect4/{source.name}/{target}")
  if target == "ocaml" then
    match source with
    | .programs .. =>
      return (← usageError log name "the native target needs an application with named lowered roots")
    | .application _ _ _ lowered =>
      match lowered.validate with
      | .error why => return (← usageError log name why)
      | .ok () => pure ()
    unless Lowered.validName source.name do
      return (← usageError log name "the native application name must start with an ASCII letter and contain only ASCII letters, digits and underscores")
  let built ← measured log source
  if anyRefused built then return
  let result ← log.folding (if target == "ocaml" then "lowering for ocaml" else s!"printing for {target}") do
    let result ← match target, source with
      | "ocaml", .application app _ _ lowered =>
        match check app with
        | .error why => pure (.error why.text)
        | .ok b =>
          try
            pure (.ok (← Native.emit source.name b lowered elaborated.modules command o.kinds o.nativeCheck out))
          catch e => pure (.error (toString e))
      | _, _ => emissionOf source command o.kinds elaborated
    match result with
    | .error why => log.event (.refusal name why); pure none
    | .ok e =>
      if output == .write then log.event (.measure "files" (e.files o.kinds).length)
      pure (some e)
  let some e := result | return
  match output with
  | .write =>
    log.setOut out.toString
    for a in e.files o.kinds do
      unless ← log.write name out (Written.ofEmitted target a) a.bytes do return
  | .describe =>
    log.event (.reading "manifest" (if o.pretty then prettyText e.manifest else jsonText e.manifest)
      (some (jsonText e.manifest)))
  | .inspect => log.event (.reading "manifest" (prettyText e.manifest) (some (jsonText e.manifest)))

/-- **`run` over a host**: the script, the project's or the one that `--script FILE` names, each
request with its module (`modulesOf`); then each request on the Lean machine (`served`), one
reading each, its line in the mode and the result's value tree as JSON. A refused build is the
build's located refusal, as `check` gives it, recorded inside the running step, so the step stands
hollow when any request was refused; the later requests still run. A usage error runs nothing. -/
def runHosted (log : Log) (app : Application NativeOp) (h : Hosted) (passed : List Request)
    (o : RunOptions) : IO Unit := do
  let script ← match o.script with
    | none => pure passed
    | some file =>
      unless ← System.FilePath.pathExists file do
        return (← log.event (.usage "run" s!"--script {file}: no such file"))
      match ← EIO.toBaseIO (readJson file) with
      | .error e => return (← log.event (.usage "run" (toString e)))
      | .ok t =>
        match scriptOf t with
        | .ok requests => pure requests
        | .error why => return (← log.event (.usage "run" s!"{file}: {why}"))
  let requests ← match modulesOf app script with
    | .ok requests => pure requests
    | .error why => return (← log.event (.usage "run" why))
  let outcomes ← log.folding "running on the Lean machine" do
    log.event (.measure "requests" requests.length)
    let outcomes := served h o.budget requests h.initial
    for outcome in outcomes do
      if let .error why := outcome then log.event (.refusal "run" why.text)
    pure outcomes
  for outcome in outcomes do
    if let .ok served := outcome then
      log.event (.reading (requestText served.request) (served.line h o.mode)
        (some (served.line h .json)))

/-- **`run`**: the options read (`RunOptions.read`), then the source's host (`Source.hosted?`); a
source with no host refuses, as a usage error. -/
def runCommand (log : Log) (source : Source) (rest : List String) : IO Unit := do
  match RunOptions.read rest {}, source.hosted? with
  | .error why, _ => usageError log "run" why
  | .ok _, .error why => log.event (.usage "run" why)
  | .ok o, .ok (app, h, passed) => runHosted log app h passed o

/-- The arguments of the `emit` that a `describe` describes: its first `describe` read as `emit`,
and no `--pretty`, which changes only how the manifest is printed. -/
def asEmit : List String → List String
  | [] => []
  | "describe" :: rest => "emit" :: rest.filter (· != "--pretty")
  | a :: rest => a :: asEmit rest

/-- The options of `inspect`: the reading that `--what` names, then the arguments left, which
`--what manifest` reads as `describe`'s. -/
def readInspect : List String → Option What → List String → Except String (What × List String)
  | [], some what, left => .ok (what, left)
  | [], none, _ => .error "--what names the reading"
  | "--what" :: word :: rest, _, left =>
    match What.parse word with
    | some what => readInspect rest (some what) left
    | none => .error s!"--what {word} names no reading"
  | a :: rest, what, left => readInspect rest what (left ++ [a])

/-- The arguments without `--what W`, which chooses only what `inspect` gives. -/
def withoutReading : List String → List String
  | "--what" :: _ :: rest => withoutReading rest
  | a :: rest => a :: withoutReading rest
  | [] => []

/-- The arguments of the `emit` that `inspect --what manifest` describes: its first `inspect` read
as `emit`, without the reading's options (`withoutReading`). -/
def inspectAsEmit : List String → List String
  | [] => []
  | "inspect" :: rest => "emit" :: withoutReading rest
  | a :: rest => a :: inspectAsEmit rest

/-- The document forms and an optional session object, derived by the public session constructor. -/
structure InspectOptions where
  form : InspectDocument.Form := .md
  explicitForm : Bool := false
  out : Option String := none
  session : Option String := none
  deriving BEq, Repr

/-- Read document options before constructing a session or writing any artifact. -/
def InspectOptions.read : List String → InspectOptions → Except String InspectOptions
  | [], o => .ok o
  | "--form" :: word :: rest, o =>
    if o.explicitForm then .error "choose one form with --form"
    else match InspectDocument.Form.parse word with
      | some form => InspectOptions.read rest { o with form, explicitForm := true }
      | none => .error s!"--form {word} names no form; choose md, json, svg or tsv"
  | "--out" :: dir :: rest, o =>
    if dir.startsWith "--" || dir.isEmpty then .error "--out needs a directory"
    else if o.out.isSome then .error "--out names one directory only"
    else InspectOptions.read rest { o with out := some dir }
  | "--session" :: service :: rest, o =>
    if service.startsWith "--" || service.isEmpty then .error "--session needs a service name"
    else if o.session.isSome then .error "--session names one service only"
    else InspectOptions.read rest { o with session := some service }
  | ["--form"], _ => .error "--form needs md, json, svg or tsv"
  | ["--out"], _ => .error "--out needs a directory"
  | ["--session"], _ => .error "--session needs a service name"
  | word :: _, _ => .error s!"{word} is no document option"

/-- The selected inspection object. Session construction keeps its existing located refusal. -/
def inspectBuilt (b : Api.Built) (service : Option String) : Except String Api.Built :=
  match service with
  | none => .ok b
  | some service => (b.session service).mapError fun why => jsonText (tree why)

/-- The report's kind of a document file: a Markdown or JSON document, an SVG figure, a TSV table. -/
def documentKind : InspectDocument.Form → Report.Kind
  | .md | .json => .document
  | .svg => .figure
  | .tsv => .table

/-- **Every document of an inspection, rendered** before anything is written: each program's
selected object (`inspectBuilt`) and its files in the form (`InspectDocument.files`); or the first
refusal, by its program. -/
def inspectPlan (programs : List (String × Api.Built)) (session : Option String)
    (form : InspectDocument.Form) (what : String) : Except String (List (String × String)) :=
  programs.foldlM (fun outputs (name, original) => do
    let b ← (inspectBuilt original session).mapError (s!"{name}: " ++ ·)
    let files ← (InspectDocument.files form name (Graphs.document b what)).mapError (s!"{name}: " ++ ·)
    return outputs ++ files) []

/-- **What a publication does to a folder**: the files it writes, and the files it removes: the
programs' prior files of a multi-file form (`InspectDocument.owns`) that it does not write again. -/
structure Publication where
  writes : List (String × String)
  removals : List String
  deriving DecidableEq, Repr

/-- The publication of rendered outputs into a folder whose files are `existing`. -/
def publicationOf (form : InspectDocument.Form) (names : List String) (existing : List String)
    (outputs : List (String × String)) : Publication :=
  { writes := outputs
    removals := if form == .svg || form == .tsv then
      existing.filter fun file =>
        names.any (fun name => InspectDocument.owns form name file) && !(outputs.any (·.1 == file))
    else [] }

/-- A publication applied to a folder as data: the files by name, the removals gone, the writes in
place. A refused plan is applied to nothing, so the folder stays as it was. -/
def Publication.apply (p : Publication) (folder : List (String × String)) : List (String × String) :=
  (folder.filter fun (file, _) => !p.removals.contains file && !p.writes.any (·.1 == file)) ++ p.writes

/-- Render every document before writing. SVG and TSV require a folder for their separate files.
The selected form replaces this program's prior generated files, including an empty selection.
Without `--out`, each document is a reading; with it, the publication (`publicationOf`) is
computed from the folder as it is, then each file is written and recorded (`Log.write`), then the
stale files are removed. A refusal before the publication touches no file. -/
def inspectDocuments (log : Log) (source : Source) (what : What) (left : List String) : IO Unit := do
  let o ← match InspectOptions.read left {} with
    | .ok o => pure o
    | .error why => return (← usageError log "inspect" why)
  if o.out.isNone && (o.form == .svg || o.form == .tsv) then
    return (← usageError log "inspect" s!"--form {o.form.name} needs --out DIR")
  let programs ← measured log source
  if o.out.isNone && o.form == .json && programs.length > 1 then
    return (← usageError log "inspect" "JSON for several programs needs --out DIR, one document per file")
  if anyRefused programs then return
  let built := programs.filterMap fun (name, result) => result.toOption.map (name, ·)
  let outputs ← log.folding s!"reading the {what.name} as {o.form.name}" do
    match inspectPlan built o.session o.form what.name with
    | .error why => log.event (.refusal "inspect" why); pure none
    | .ok outputs => log.event (.measure "files" outputs.length); pure (some outputs)
  let some outputs := outputs | return
  unless (outputs.map Prod.fst).eraseDups.length == outputs.length do
    return (← usageError log "inspect" "programs repeat an output file name")
  match o.out with
  | none =>
    for (name, content) in outputs do
      log.event (.reading s!"{name} as {o.form.name}" content
        (if o.form == .json then some content else none))
  | some directory =>
    try
      let folder := System.FilePath.mk directory
      IO.FS.createDirAll folder
      let existing ← (← folder.readDir).toList.filterMapM fun entry => do
        return if ← entry.path.isDir then none else some entry.fileName
      let publication := publicationOf o.form (built.map (·.1)) existing outputs
      log.setOut directory
      for (name, content) in publication.writes do
        unless ← log.write "inspect" folder
            (Written.of .program (.print o.form.name) (documentKind o.form) name content.toUTF8)
            content.toUTF8 do
          return
      for file in publication.removals do IO.FS.removeFile (folder / file)
    catch error => log.event (.refusal "inspect" (toString error))

/-- **`inspect`**: the reading that `--what` names (`Compiler.Inspect`), of the application's built
program or of each program of a group, under its name: its text, with its JSON beside it.
`--what manifest` gives what `describe` gives, indented. A program that the build refuses is
recorded as `check` records it, and the command exits with `1`. -/
def inspectCommand (log : Log) (source : Source) (elaborated : Elaborated) (args rest : List String) :
    IO Unit := do
  match readInspect rest none [] with
  | .error why => usageError log "inspect" why
  | .ok (.manifest, left) => emitCommand log source elaborated .inspect (inspectAsEmit args) left
  | .ok (what, left) =>
    if what.isDocument then return (← inspectDocuments log source what left)
    unless left.isEmpty do
      return (← usageError log "inspect" s!"{" ".intercalate left} is no option of --what {what.name}")
    let built ← measured log source
    for (name, result) in built do
      match result with
      | .error _ => pure ()
      | .ok b =>
        match reading b what, source with
        | .error why, _ => log.event (.refusal "inspect" s!"{name}: {why}")
        | .ok r, .application .. => log.event (.reading what.name r.text (some (jsonText r.json)))
        | .ok r, .programs .. =>
          log.event (.reading s!"{what.name} of {name}" r.text
            (some (jsonText (.obj [("program", .str name), (what.name, r.json)]))))

/-- **The command over a source, into its log**: `check`, `open`, `emit`, `describe`, `inspect` or
`run`. `given` are the arguments without the report's flags, which a header and the manifest
record; `rest` are the ones the command reads. -/
def dispatch (log : Log) (source : Source) (elaborated : Elaborated) (given rest : List String) :
    IO Unit :=
  match rest with
  | "check" :: options =>
    match CheckOptions.read options {} with
    | .ok o => checkCommand log source elaborated o.out
    | .error why => usageError log "check" why
  | "open" :: options => openCommand log options
  | "emit" :: options => emitCommand log source elaborated .write given options
  | "describe" :: options => emitCommand log source elaborated .describe (asEmit given) options
  | "inspect" :: options => inspectCommand log source elaborated given options
  | "run" :: options => runCommand log source options
  | [] => log.event (.usage "" usage)
  | c :: _ => log.event (.usage "" s!"{c} is no command; {usage}")

/-- The group that the first `--group NAME` names, and the arguments without those two. -/
def takeGroup : List String → Option String × List String
  | [] => (none, [])
  | "--group" :: name :: rest => (some name, rest)
  | a :: rest => match takeGroup rest with
    | (group, others) => (group, a :: others)

/-- The command's name on a line: its first word after `--group NAME`. -/
def commandOf (rest : List String) : String := (takeGroup rest).2.head?.getD ""

/-- **A command line shown**: its report's flags read (`takeFlags`), the format resolved
(`defaultFormat`), the body run into a log and shown (`Report.print`). A flag that reads wrong is
a usage error, shown in the format and the quiet read before it. `--help` gives the usage and
`--version` the version as readings, with exit `0`. -/
def reported (args : List String) (body : Log → List String → IO Unit) : IO UInt32 := do
  let (flags, rest) := takeFlags args {}
  let format ← match flags.format with
    | some f => pure f
    | none => defaultFormat
  let command := match rest with
    | .ok given => commandOf given
    | .error _ => ""
  Report.print format flags.quiet command args fun log =>
    match rest with
    | .error why => log.event (.usage "" why)
    | .ok given =>
      if flags.help then log.event (.reading "usage" usage none)
      else if flags.version then log.event (.reading "version" versionText none)
      else body log given

/-- **The command line over a source**: the report's flags, then `dispatch`. `args` are the
arguments as given, which the report's title shows; `rest` are the ones the command reads. -/
def run (source : Source) (elaborated : Elaborated) (args rest : List String) : IO UInt32 :=
  reported args fun log given =>
    let rest := ((takeFlags rest {}).2.toOption).getD rest
    dispatch log source elaborated given rest

/-- **The compiler's entry point** over one application: `check`, `emit`, `describe`, `inspect` or
`run`. `run` takes the application's host and the script of requests that the project passes.
`elaborated` is what the calling module's elaboration knows of the executable (`elaborated%`, the
default): its Lean module closure and the declared names of its keys. -/
def main (app : Application NativeOp) (args : List String) (hosted : Option Hosted := none)
    (script : List Request := []) (lowered : Lowered := {})
    (elaborated : Elaborated := by exact elaborated%) : IO UInt32 :=
  run (.application app hosted script lowered) elaborated args args

/-- **The compiler over named sources** (`lake exe effect4`): `main`'s command line.
`open` needs no source; other commands use the source that `--group NAME` chooses. -/
def mainOver (groups : List Source) (args : List String)
    (elaborated : Elaborated := by exact elaborated%) : IO UInt32 :=
  reported args fun log given => do
    if let "open" :: options := given then return (← openCommand log options)
    let names := ", ".intercalate (groups.map (·.name))
    match takeGroup given with
    | (some name, rest) =>
      match groups.find? (·.name == name) with
      | some source => dispatch log source elaborated given rest
      | none => log.event (.usage "" s!"no group is named {name}; the groups are {names}")
    | (none, _) => log.event (.usage "" s!"--group NAME chooses one of {names}; {usage}")

end Compiler
