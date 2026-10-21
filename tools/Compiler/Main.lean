import Compiler.Emit
import Compiler.Run
import Compiler.Inspect
import Compiler.Elaborated

/-!
# Compiler.Main — the compiler's entry point

`Compiler.main app args` is the compiler's command line over one application
(`docs/research/2026-10-20-compiler-entry/README.md`, C2 slice 1). A project's executable calls it
by static import, as decision E1 asks: the value of a declaration loaded by name cannot be
evaluated without `unsafe`. The commands are the folds of §2, and nothing else:

    check [--json]
    emit [--target ts] [--out DIR] [--emit=module,surface,canonical,certificate,manifest]
    describe [--target ts] [--out DIR] [--emit=…] [--pretty]
    inspect --what types|rows|surface|graph|manifest [--json] [the options of describe]
    run [--text | --typed | --json] [--script FILE] [--budget N]

- `check` builds the application's service module (`Compiler.check`) and prints its certificate:
  as text, each service's key with the Lean names that declare it, or as one line of JSON under
  `--json`. A refusal is one located refusal, printed the same two ways.
- `emit` writes the checked emission into one folder (`Compiler.emitTs`), by default
  `.lake/effect4/<name>/ts/`. `--emit` selects the kinds; the default is all of them. `ts` is the
  one target, so `--target ts` is the default.
- `describe` prints the manifest that `emit` with the same options would write, and writes
  nothing: as one line, or indented under `--pretty` (`prettyText`).
- `inspect` prints one reading of the built program (`Compiler.Inspect`): one query of the tool
  protocol, the surface, or the manifest that `describe` prints. As text, or as one line of JSON
  under `--json`.
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

**The inputs** (`readInputs`): the pins and the prelude are read from the library's checkout,
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
  | "check" => "check [--json]"
  | "emit" => "emit [--target ts] [--out DIR] [--emit=KIND,…]"
  | "describe" => "describe [--target ts] [--out DIR] [--emit=KIND,…] [--pretty]"
  | "inspect" => "inspect --what " ++ "|".intercalate (What.all.map What.name) ++
      " [--json] [--target ts] [--out DIR] [--emit=KIND,…]"
  | "run" => "run [--text | --typed | --json] [--script FILE] [--budget N]"
  | _ => ""

/-- The kinds that `--emit` names, and the one target, in words. -/
def kindsText : String :=
  "a KIND is one of " ++ ", ".intercalate (Kind.selectable.map Kind.name) ++
    "; ts is the one target, and the default"

/-- The command line, in words. -/
def usage : String :=
  "usage: " ++ " | ".intercalate (["check", "emit", "describe", "inspect", "run"].map usageOf) ++
    "; " ++ kindsText

/-- **A usage error**: the command, why, and the command's options (`usageOf`); exit code `2`. -/
def usageError (command why : String) : IO UInt32 := do
  let kinds := if ["emit", "describe", "inspect"].contains command then s!"; {kindsText}" else ""
  IO.eprintln s!"{command}: {why}; usage: {usageOf command}{kinds}"
  return 2

/-- The options of `emit` and `describe`: the target, the output folder, the kinds, and whether
`describe` indents the manifest. -/
structure Options where
  target : Option String := none
  out : Option String := none
  kinds : List Kind := Kind.selectable
  pretty : Bool := false

/-- Read the options of `emit` and `describe`, or name the argument that is none. -/
def Options.read : List String → Options → Except String Options
  | [], o => .ok o
  | "--target" :: t :: rest, o => Options.read rest { o with target := some t }
  | "--out" :: d :: rest, o => Options.read rest { o with out := some d }
  | "--pretty" :: rest, o => Options.read rest { o with pretty := true }
  | a :: rest, o =>
    if a.startsWith "--emit=" then
      match Kind.parse (a.drop 7).toString with
      | some kinds => Options.read rest { o with kinds }
      | none => .error s!"{a} names no kind"
    else .error s!"{a} is no option"

/-- A JSON file of the library's checkout, read by the profile's text reader (`NatJson.parse`). -/
def readJson (path : System.FilePath) : IO NatJson := do
  match NatJson.parse ((← IO.FS.readBinFile path).data.toList.map UInt8.toNat) with
  | .ok t => pure t
  | .error why => throw (IO.userError s!"{path}: {NatJson.refusalText why}")

/-- Whether a JSON value is the string `s`. -/
def isStr (s : String) : Option NatJson → Bool
  | some (.str v) => v == s
  | _ => false

/-- **The library's checkout**: the folder where the project's `lake-manifest.json` puts the
package `effect4`, at its path or under the packages folder; the current folder when the project
is that package. -/
def libraryRoot : IO System.FilePath := do
  let manifest ← readJson "lake-manifest.json"
  if isStr "effect4" (manifest.at? [.key "name"]) then return "."
  let packages := match manifest.at? [.key "packages"] with
    | some (.arr ps) => ps
    | _ => []
  let some package := packages.find? fun p => isStr "effect4" (p.at? [.key "name"])
    | throw (IO.userError "lake-manifest.json names no package effect4")
  match package.at? [.key "type"], package.at? [.key "dir"] with
  | some (.str "path"), some (.str dir) => return dir
  | _, _ =>
    match manifest.at? [.key "packagesDir"] with
    | some (.str dir) => return System.FilePath.mk dir / "effect4"
    | _ => return System.FilePath.mk ".lake" / "packages" / "effect4"

/-- **The folders that hold Lean sources**: `LEAN_SRC_PATH`, which `lake exe` sets from the
workspace, the project's, the library's and its packages' source folders, as Lake reads them from
`lake-manifest.json` and their lakefiles; each once. Refused when it is not set. -/
def sourceFolders : IO (List System.FilePath) := do
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return (System.SearchPath.parse path).eraseDups
  | none => throw (IO.userError
      "LEAN_SRC_PATH is not set: run the command through lake exe, which sets it from the workspace")

/-- **The source of a Lean module**: its file in exactly one of the folders (`sourceFolders`), by
its real path. Refused when no folder holds it, or when two hold different files: the manifest
would then name a source the build may not have read. -/
def sourceOf (folders : List System.FilePath) (module : String) : IO System.FilePath := do
  let mut found : List System.FilePath := []
  for folder in folders do
    let file := Lean.modToFilePath folder module.toName "lean"
    if ← file.pathExists then
      let real ← IO.FS.realPath file
      unless found.contains real do found := found ++ [real]
  match found with
  | [file] => return file
  | [] => throw (IO.userError s!"no folder of LEAN_SRC_PATH holds the source of {module}")
  | files => throw (IO.userError
      s!"{module} has {files.length} sources on LEAN_SRC_PATH: {", ".intercalate (files.map toString)}")

/-- **The newest commit of the library's checkout that changed one of `paths`** (relative to its
root); `none` when Git answers none. -/
def provenance (root : System.FilePath) (paths : List String) : IO (Option String) := do
  try
    let git ← IO.Process.output
      { cmd := "git", args := #["-C", root.toString, "log", "-1", "--format=%H", "--"] ++ paths.toArray }
    let commit := git.stdout.trimAscii.copy
    pure (if git.exitCode == 0 && !commit.isEmpty then some commit else none)
  catch _ => pure none

/-- **The inputs**, from the library's checkout and the source folders: its `lean-toolchain`; each
version that its TypeScript package pins (`ts/eff/package.json`), tsgo's among them; each module of
the executable's closure (`modules`, `Compiler.Elaborated`) with the SHA-256 of its source
(`sourceOf`); and as provenance, the newest commit of the checkout that changed a file the emission
reads there: a source of the closure, the prelude's folder, the pins or the toolchain pin. -/
def readInputs (root : System.FilePath) (modules : List String) : IO Inputs := do
  let lean := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.copy
  let package ← readJson (root / "ts" / "eff" / "package.json")
  let pinned (field : String) : List (String × String) := match package.at? [.key field] with
    | some (.obj entries) => entries.filterMap fun
      | (name, .str version) => some (name, version)
      | _ => none
    | _ => []
  let pins := pinned "dependencies" ++ pinned "devDependencies"
  if (pins.lookup tsgoPackage).isNone then
    throw (IO.userError s!"the library's ts/eff/package.json pins no {tsgoPackage}")
  let folders ← sourceFolders
  let sources ← modules.mapM fun m => do pure (m, ← sourceOf folders m)
  let hashed ← sources.mapM fun (m, file) => do
    pure (m, Store.sha256 (← IO.FS.readBinFile file).data.toList)
  let checkout := (← IO.FS.realPath root).toString ++ "/"
  let own := sources.filterMap fun (_, file) =>
    if file.toString.startsWith checkout then some (file.toString.drop checkout.length).toString
    else none
  let library ← provenance root (own ++ ["ts/prelude", "ts/eff/package.json", "lean-toolchain"])
  return { lean, library, pins, modules := hashed }

/-- **What a command runs over**: one application, with the host and the script that `run` takes
when the project passes them; or a named group of programs, each admitted at the group's
application (`checkProgram`), the empty one by default, as the wire corpus is. -/
inductive Source where
  | application (app : Application NativeOp) (hosted : Option Hosted := none)
      (script : List Request := [])
  | programs (name : String) (programs : List (String × NativeEff)) (app : SigApp := {})

/-- A source's name: the application's, or the group's. It names the default output folder. -/
def Source.name : Source → String
  | .application app _ _ => app.name
  | .programs name _ _ => name

/-- **What `run` runs over**: an application with its host and the script the project passes; or,
in words, why the source has no host. -/
def Source.hosted? : Source → Except String (Application NativeOp × Hosted × List Request)
  | .application app (some h) script => .ok (app, h, script)
  | .application app none _ =>
    .error s!"the application {app.name} has no host; a project passes one to Compiler.main (hosted := …)"
  | .programs name _ _ =>
    .error s!"the group {name} is programs with no host to answer a row; run takes an application and its host"

/-- **The source's programs, built**: the application's service module under its name
(`check`), or each program of the group under its own, at the group's application
(`checkProgram`); each built, or the build's refusal. -/
def builtOf : Source → List (String × Except CheckRefusal Api.Built)
  | .application app _ _ => [(app.name, check app)]
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
def checkCommand (source : Source) (elaborated : Elaborated) (json : Bool) : IO UInt32 := do
  let mut refused := false
  for (name, built) in builtOf source do
    match built, source with
    | .error why, _ => refused := true; printRefusal source name why json
    | .ok b, .application app _ _ =>
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
    | .application app _ _ =>
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
  if let some t := o.target then
    unless t == "ts" do return (← usageError name s!"--target {t} is no target here, only ts")
  match ← emissionOf source command o.kinds elaborated with
  | .error why => IO.eprintln (s!"{name}: " ++ why); return 1
  | .ok e =>
    match output with
    | .write =>
      let out := System.FilePath.mk (o.out.getD s!".lake/effect4/{source.name}/ts")
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
        match reading name b what, source, json with
        | .error why, _, _ => failed := true; IO.eprintln s!"inspect: {name}: {why}"
        | .ok r, .application .., true => IO.println (jsonText r.json)
        | .ok r, .application .., false => IO.println r.text
        | .ok r, .programs .., true => IO.println (jsonText (.obj [("program", .str name), (what.name, r.json)]))
        | .ok r, .programs .., false => IO.println s!"{name}:\n{r.text}"
    return if failed then 1 else 0

/-- **The command line over a source**: `check`, `emit`, `describe`, `inspect` or `run`. `args` are
the arguments as given, which a header and the manifest record; `rest` are the ones the command
reads. -/
def run (source : Source) (elaborated : Elaborated) (args rest : List String) : IO UInt32 :=
  match rest with
  | ["check"] => checkCommand source elaborated false
  | ["check", "--json"] => checkCommand source elaborated true
  | "check" :: options => usageError "check" s!"{" ".intercalate options} is no option"
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
    (script : List Request := []) (elaborated : Elaborated := by exact elaborated%) : IO UInt32 :=
  run (.application app hosted script) elaborated args args

/-- The group that the first `--group NAME` names, and the arguments without those two. -/
def takeGroup : List String → Option String × List String
  | [] => (none, [])
  | "--group" :: name :: rest => (some name, rest)
  | a :: rest => match takeGroup rest with
    | (group, others) => (group, a :: others)

/-- **The compiler over named sources** (`lake exe effect4`): `main`'s command line, with
`--group NAME` choosing the source of that name. -/
def mainOver (groups : List Source) (args : List String)
    (elaborated : Elaborated := by exact elaborated%) : IO UInt32 := do
  let names := ", ".intercalate (groups.map (·.name))
  match takeGroup args with
  | (some name, rest) =>
    match groups.find? (·.name == name) with
    | some source => run source elaborated args rest
    | none => IO.eprintln s!"no group is named {name}; the groups are {names}"; return 2
  | (none, _) => IO.eprintln s!"--group NAME chooses one of {names}; {usage}"; return 2

end Compiler
