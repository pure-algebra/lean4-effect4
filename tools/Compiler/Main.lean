import Compiler.Native
import Compiler.Run
import Compiler.Inspect
import Compiler.Elaborated

/-!
# Compiler.Main — the compiler's entry point

`Compiler.main app args` is the compiler's command line over one application
(`docs/research/2026-10-20-compiler-entry/README.md`, C2 slice 1). A project's executable calls it
by static import, as decision E1 asks: the value of a declaration loaded by name cannot be
evaluated without `unsafe`. The commands are the folds of §2, and nothing else:

    check [--json] [--out FILE.obj]
    open FILE.obj
    emit [--target ts|ocaml] [--check] [--out DIR] [--emit=module,surface,canonical,certificate,manifest]
    describe [--target ts|ocaml] [--out DIR] [--emit=…] [--pretty]
    inspect --what types|rows|surface|graph|manifest [--json] [the options of describe]
    run [--text | --typed | --json] [--script FILE] [--budget N]

- `open FILE.obj` reads and admits a saved object, then prints its certificate as JSON.
  It needs no group, application source, prelude or host.
- `check` builds the application's service module (`Compiler.check`) and prints its certificate:
  as text, each service's key with the Lean names that declare it, or as one line of JSON under
  `--json`. A refusal is one located refusal, printed the same two ways.
  `--out FILE.obj` writes the admitted object; a refusal leaves that file unchanged.
- `emit` writes the checked emission into one folder (`Compiler.emitTs`), by default
  `.lake/effect4/<name>/<target>/`. `--emit` selects the kinds; the default is all of them.
  `--target ts` is the default. `--target ocaml` lowers the named roots through `lcnfgen`.
  `--check` compiles the native module, and never runs it.
- `describe` prints the manifest that `emit` with the same options would write, and writes
  nothing: as one line, or indented under `--pretty` (`prettyText`).
- `inspect` prints the object's address table, rows, graph, surface, or emission manifest (`Compiler.Inspect`).
  It prints text, or one line of JSON under `--json`.
- `run` runs each request of a script on the Lean machine over the application's host, and prints
  one line a request (`Compiler.Run`): a readable line (`--text`, the default), the exit encoded at
  its own type (`--typed`), or the result's value tree as JSON (`--json`). The host and the default
  script are what the project passes to `Compiler.main`; `--script FILE` reads a JSON array of
  requests instead. `--budget N` plays every row at `N` steps of fuel. An application with no host
  refuses `run`, as a usage error.

`Compiler.mainOver groups args` is the same command line over named sources, one chosen by
`--group NAME` (`lake exe effect4`, `Compiler.Exe`, C2 slice 2). A source is one application, or a
group of programs, each admitted at the group's application (`Source`). Over a group, `check` and
`inspect` print each program's answer under its name, and `emit` writes one folder with one
manifest (`Compiler.emitGroup`).

**The inputs** (`readInputs`, `Compiler.Inputs`): the pins and the prelude are read from the library's checkout,
which the project's `lake-manifest.json` locates (`libraryRoot`). The executable's Lean module
closure is data it was built with (`Compiler.Elaborated`, the default of `main`'s `elaborated`), and
each module's source is read where `lake exe` puts it, on `LEAN_SRC_PATH` (`sourceOf`). So the
command runs from the project's root through `lake exe`. The exit code is `0` on success, `1` on a
refusal, and `2` on a usage error, which names the command and its options (`usageOf`). A `run`
whose request the build refuses prints the located refusal as `check` does, runs the rest, and
exits with `1`.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- A command's options, in words. -/
def usageOf : String → String
  | "check" => "check [--json] [--out FILE.obj]"
  | "open" => "open FILE.obj"
  | "emit" => "emit [--target ts|ocaml] [--check] [--out DIR] [--emit=KIND,…]"
  | "describe" => "describe [--target ts|ocaml] [--out DIR] [--emit=KIND,…] [--pretty]"
  | "inspect" => "inspect --what " ++ "|".intercalate (What.all.map What.name) ++
      " [--json] [--target ts|ocaml] [--out DIR] [--emit=KIND,…]"
  | "run" => "run [--text | --typed | --json] [--script FILE] [--budget N]"
  | _ => ""

/-- The kinds that `--emit` names and the available targets, in words. -/
def kindsText : String :=
  "a KIND is one of " ++ ", ".intercalate (Kind.selectable.map Kind.name) ++
    "; ts is the default target; ocaml lowers the declared roots"

/-- The command line, in words. -/
def usage : String :=
  "usage: " ++ " | ".intercalate (["check", "open", "emit", "describe", "inspect", "run"].map usageOf) ++
    "; " ++ kindsText

/-- **A usage error**: the command, why, and the command's options (`usageOf`); exit code `2`. -/
def usageError (command why : String) : IO UInt32 := do
  let kinds := if ["emit", "describe", "inspect"].contains command then s!"; {kindsText}" else ""
  IO.eprintln s!"{command}: {why}; usage: {usageOf command}{kinds}"
  return 2

/-- The certificate's presentation and optional single-object output file. -/
structure CheckOptions where
  json : Bool := false
  out : Option String := none
  deriving DecidableEq

/-- Parse check options before checking or writing any program. -/
def CheckOptions.read : List String → CheckOptions → Except String CheckOptions
  | [], o => .ok o
  | "--json" :: rest, o => CheckOptions.read rest { o with json := true }
  | "--out" :: file :: rest, o =>
    if file.startsWith "--" then .error "--out needs a file"
    else if o.out.isSome then .error "--out names one file only"
    else CheckOptions.read rest { o with out := some file }
  | ["--out"], _ => .error "--out needs a file"
  | arg :: _, _ => .error s!"{arg} is no option"

/-- Load a saved object without an application, then print its generated certificate. -/
def openCommand (args : List String) : IO UInt32 := do
  let file ← match args with
    | [file] =>
      if file.startsWith "--" then return (← usageError "open" "name one object file")
      else pure file
    | _ => return (← usageError "open" "name one object file")
  try
    let bytes ← IO.FS.readBinFile file
    match Object.load bytes.data.toList with
    | .ok b => IO.println (jsonText (certificate b)); return 0
    | .error why => IO.eprintln ("open: " ++ jsonText (tree why)); return 1
  catch error => IO.eprintln s!"open: {file}: {error}"; return 1

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

/-- A build's refusal, as `check` prints it: one line of JSON under `json`, else text on the error
stream; a group's program by its name. -/
def printRefusal (source : Source) (name : String) (why : CheckRefusal) (json : Bool) : IO Unit :=
  match source, json with
  | .application .., true => IO.println (jsonText why.json)
  | .application .., false => IO.eprintln ("check: " ++ why.text)
  | .programs .., true => IO.println (jsonText (.obj [("program", .str name), ("refused", tree why.why)]))
  | .programs .., false => IO.eprintln (s!"check: the program {name}: " ++ why.text)

/-- `check`: the certificate, or the refusal. Over a group, each program's, under its name; the
command refuses when one program refuses. The text names the declarations of each service's key
(`Elaborated.namesOf`). -/
def checkCommand (source : Source) (elaborated : Elaborated) (json : Bool)
    (out : Option String := none) : IO UInt32 := do
  if out.isSome then
    match source with
    | .programs _ programs _ =>
      unless programs.length == 1 do
        return (← usageError "check" "--out needs exactly one program")
    | .application .. => pure ()
  let mut refused := false
  for (name, built) in builtOf source do
    if let some file := out then
      if let .ok b := built then
        try
          IO.FS.writeBinFile file ⟨(Object.ofBuilt b).bytes.toArray⟩
        catch error => IO.eprintln s!"check: {file}: {error}"; return 1
    match built, source with
    | .error why, _ => refused := true; printRefusal source name why json
    | .ok b, .application app _ _ _ =>
      if json then IO.println (jsonText (certificate b))
      else
        let title := s!"{app.name}: checked; the service {serviceName app}"
        for line in certificateLines title b elaborated.namesOf do IO.println line
    | .ok b, .programs .. =>
      if json then IO.println (jsonText (.obj [("program", .str name), ("certificate", certificate b)]))
      else for line in certificateLines s!"{name}: checked" b elaborated.namesOf do IO.println line
  return if refused then 1 else 0

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

/-- **What an emission's command does with it**: `emit` writes its files; `describe` prints its
manifest, as one line or indented under `--pretty`; `inspect --what manifest` prints it indented,
or as one line under `--json`. -/
inductive Output where
  | write
  | describe
  | inspect (json : Bool)
  deriving DecidableEq

/-- The command an output belongs to. -/
def Output.name : Output → String
  | .write => "emit"
  | .describe => "describe"
  | .inspect _ => "inspect"

/-- `emit`, `describe` and `inspect --what manifest`: the emission of the options `rest`, recorded
under `command`; written, or its manifest printed. `ts` is the target when none is named. -/
def emitCommand (source : Source) (elaborated : Elaborated) (output : Output) (command rest : List String) :
    IO UInt32 := do
  let name := output.name
  let o ← match Options.read rest {} with
    | .ok o => pure o
    | .error why => return (← usageError name why)
  match output, o.pretty with
  | .write, true | .inspect _, true =>
    return (← usageError name "--pretty is describe's; inspect prints the manifest indented by default")
  | _, _ => pure ()
  let target := o.target.getD "ts"
  unless target == "ts" || target == "ocaml" do
    return (← usageError name s!"--target {target} is no target here; choose ts or ocaml")
  if o.nativeCheck && (target != "ocaml" || output != .write) then
    return (← usageError name "--check belongs to emit --target ocaml")
  if target == "ocaml" && o.kindsGiven && o.kinds.contains .surface then
    return (← usageError name "ocaml emits no surface; choose module, canonical, certificate or manifest")
  let out := System.FilePath.mk (o.out.getD s!".lake/effect4/{source.name}/{target}")
  if target == "ocaml" then
    match source with
    | .programs .. =>
      return (← usageError name "the native target needs an application with named lowered roots")
    | .application _ _ _ lowered =>
      match lowered.validate with
      | .error why => return (← usageError name why)
      | .ok () => pure ()
    unless Lowered.validName source.name do
      return (← usageError name "the native application name must start with an ASCII letter and contain only ASCII letters, digits and underscores")
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
  | .error why => IO.eprintln (s!"{name}: " ++ why); return 1
  | .ok e =>
    match output with
    | .write =>
      let files := e.files o.kinds
      Prelude.write out (files.map fun a => (a.path, a.bytes))
      IO.println (s!"emit: {files.length} files to {out}: " ++
        ", ".intercalate (Kind.all.filterMap fun k =>
          let n := (files.filter (·.kind == k)).length
          if n == 0 then none else some s!"{k.name} {n}"))
    | .describe => IO.println (if o.pretty then prettyText e.manifest else jsonText e.manifest)
    | .inspect json => IO.println (if json then jsonText e.manifest else prettyText e.manifest)
    return 0

/-- **`run` over a host**: the script, the project's or the one that `--script FILE` names, each
request with its module (`modulesOf`); then each request on the Lean machine (`runFrom`), one line
each. A refused build is printed as `check` prints it: as one line of JSON under `--json`, else as
text on the error stream. A usage error runs nothing. -/
def runHosted (app : Application NativeOp) (h : Hosted) (passed : List Request) (o : RunOptions) :
    IO UInt32 := do
  let script ← match o.script with
    | none => pure passed
    | some file =>
      unless ← System.FilePath.pathExists file do
        IO.eprintln s!"run: --script {file}: no such file"; return 2
      match ← EIO.toBaseIO (readJson file) with
      | .error e => IO.eprintln s!"run: {e}"; return 2
      | .ok t =>
        match scriptOf t with
        | .ok requests => pure requests
        | .error why => IO.eprintln s!"run: {file}: {why}"; return 2
  let requests ← match modulesOf app script with
    | .ok requests => pure requests
    | .error why => IO.eprintln s!"run: {why}"; return 2
  let mut refused := false
  for outcome in runFrom h o.mode o.budget requests h.initial do
    match outcome with
    | .ok line => IO.println line
    | .error why =>
      refused := true
      match o.mode with
      | .json => IO.println (jsonText why.json)
      | _ => IO.eprintln ("run: " ++ why.text)
  return if refused then 1 else 0

/-- **`run`**: the options read (`RunOptions.read`), then the source's host (`Source.hosted?`); a
source with no host refuses, as a usage error. -/
def runCommand (source : Source) (rest : List String) : IO UInt32 := do
  match RunOptions.read rest {}, source.hosted? with
  | .error why, _ => usageError "run" why
  | .ok _, .error why => IO.eprintln s!"run: {why}"; return 2
  | .ok o, .ok (app, h, passed) => runHosted app h passed o

/-- The arguments of the `emit` that a `describe` describes: its first `describe` read as `emit`,
and no `--pretty`, which changes only how the manifest is printed. -/
def asEmit : List String → List String
  | [] => []
  | "describe" :: rest => "emit" :: rest.filter (· != "--pretty")
  | a :: rest => a :: asEmit rest

/-- The options of `inspect`: the reading that `--what` names, and whether it is printed as JSON;
then the arguments left, which `--what manifest` reads as `describe`'s. -/
def readInspect : List String → Option What → Bool → List String →
    Except String (What × Bool × List String)
  | [], some what, json, left => .ok (what, json, left)
  | [], none, _, _ => .error "--what names the reading"
  | "--what" :: word :: rest, _, json, left =>
    match What.parse word with
    | some what => readInspect rest (some what) json left
    | none => .error s!"--what {word} names no reading"
  | "--json" :: rest, what, _, left => readInspect rest what true left
  | a :: rest, what, json, left => readInspect rest what json (left ++ [a])

/-- The arguments without `--what W` and `--json`, which choose only what `inspect` prints and
how. -/
def withoutReading : List String → List String
  | "--what" :: _ :: rest => withoutReading rest
  | "--json" :: rest => withoutReading rest
  | a :: rest => a :: withoutReading rest
  | [] => []

/-- The arguments of the `emit` that `inspect --what manifest` describes: its first `inspect` read
as `emit`, without the reading's options (`withoutReading`). -/
def inspectAsEmit : List String → List String
  | [] => []
  | "inspect" :: rest => "emit" :: withoutReading rest
  | a :: rest => a :: inspectAsEmit rest

/-- **`inspect`**: the reading that `--what` names (`Compiler.Inspect`), of the application's built
program or of each program of a group, under its name; as text, or under `--json` as one line.
`--what manifest` prints what `describe` prints, indented as text. A program that the build refuses
is printed as `check` prints it, and the command exits with `1`. -/
def inspectCommand (source : Source) (elaborated : Elaborated) (args rest : List String) :
    IO UInt32 := do
  match readInspect rest none false [] with
  | .error why => usageError "inspect" why
  | .ok (.manifest, json, left) => emitCommand source elaborated (.inspect json) (inspectAsEmit args) left
  | .ok (what, json, left) =>
    unless left.isEmpty do
      return (← usageError "inspect" s!"{" ".intercalate left} is no option of --what {what.name}")
    let mut failed := false
    for (name, built) in builtOf source do
      match built with
      | .error why => failed := true; printRefusal source name why json
      | .ok b =>
        match reading b what, source, json with
        | .error why, _, _ => failed := true; IO.eprintln s!"inspect: {name}: {why}"
        | .ok r, .application .., true => IO.println (jsonText r.json)
        | .ok r, .application .., false => IO.println r.text
        | .ok r, .programs .., true => IO.println (jsonText (.obj [("program", .str name), (what.name, r.json)]))
        | .ok r, .programs .., false => IO.println s!"{name}:\n{r.text}"
    return if failed then 1 else 0

/-- **The command line over a source**: `check`, `open`, `emit`, `describe`, `inspect` or `run`. `args` are
the arguments as given, which a header and the manifest record; `rest` are the ones the command
reads. -/
def run (source : Source) (elaborated : Elaborated) (args rest : List String) : IO UInt32 :=
  match rest with
  | "check" :: options =>
    match CheckOptions.read options {} with
    | .ok o => checkCommand source elaborated o.json o.out
    | .error why => usageError "check" why
  | "open" :: options => openCommand options
  | "emit" :: options => emitCommand source elaborated .write args options
  | "describe" :: options => emitCommand source elaborated .describe (asEmit args) options
  | "inspect" :: options => inspectCommand source elaborated args options
  | "run" :: options => runCommand source options
  | [] => do IO.eprintln usage; return 2
  | c :: _ => do IO.eprintln s!"{c} is no command; {usage}"; return 2

/-- **The compiler's entry point** over one application: `check`, `emit`, `describe`, `inspect` or
`run`. `run` takes the application's host and the script of requests that the project passes.
`elaborated` is what the calling module's elaboration knows of the executable (`elaborated%`, the
default): its Lean module closure and the declared names of its keys. -/
def main (app : Application NativeOp) (args : List String) (hosted : Option Hosted := none)
    (script : List Request := []) (lowered : Lowered := {})
    (elaborated : Elaborated := by exact elaborated%) : IO UInt32 :=
  run (.application app hosted script lowered) elaborated args args

/-- The group that the first `--group NAME` names, and the arguments without those two. -/
def takeGroup : List String → Option String × List String
  | [] => (none, [])
  | "--group" :: name :: rest => (some name, rest)
  | a :: rest => match takeGroup rest with
    | (group, others) => (group, a :: others)

/-- **The compiler over named sources** (`lake exe effect4`): `main`'s command line.
`open` needs no source; other commands use the source that `--group NAME` chooses. -/
def mainOver (groups : List Source) (args : List String)
    (elaborated : Elaborated := by exact elaborated%) : IO UInt32 := do
  if let "open" :: options := args then return (← openCommand options)
  let names := ", ".intercalate (groups.map (·.name))
  match takeGroup args with
  | (some name, rest) =>
    match groups.find? (·.name == name) with
    | some source => run source elaborated args rest
    | none => IO.eprintln s!"no group is named {name}; the groups are {names}"; return 2
  | (none, _) => IO.eprintln s!"--group NAME chooses one of {names}; {usage}"; return 2

end Compiler
