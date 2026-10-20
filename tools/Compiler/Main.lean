import Compiler.Emit

/-!
# Compiler.Main — the compiler's entry point

`Compiler.main app args` is the compiler's command line over one application
(`docs/research/2026-10-20-compiler-entry/README.md`, C2 slice 1). A project's executable calls it
by static import, as decision E1 asks: the value of a declaration loaded by name cannot be
evaluated without `unsafe`. The commands are the folds of §2, and nothing else:

    check [--json]
    emit --target ts [--out DIR] [--emit=module,surface,canonical,certificate,manifest]
    describe --target ts [--out DIR] [--emit=…]

- `check` builds the application's service module (`Compiler.check`) and prints its certificate:
  as text, or as one line of JSON under `--json`. A refusal is one located refusal, printed the
  same two ways.
- `emit` writes the checked emission into one folder (`Compiler.emitTs`), by default
  `.lake/effect4/<name>/ts/`. `--emit` selects the kinds; the default is all of them.
- `describe` prints the manifest that `emit` with the same options would write, and writes nothing.

`Compiler.mainOver groups args` is the same command line over named sources, one chosen by
`--group NAME` (`lake exe effect4`, `Compiler.Exe`, C2 slice 2). A source is one application, or a
group of programs, each admitted at the empty application (`Source`). Over a group, `check` prints
each program's certificate under its name, and `emit` writes one folder with one manifest
(`Compiler.emitGroup`).

The pins and the prelude are read from the library's checkout, which the project's
`lake-manifest.json` locates (`libraryRoot`). So the command runs from the project's root, as
`lake exe` does. The exit code is `0` on success, `1` on a refusal, and `2` on a usage error.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- The command line, in words. -/
def usage : String :=
  "usage: check [--json] | emit --target ts [--out DIR] [--emit=KIND,…] | describe --target ts " ++
    "[--out DIR] [--emit=KIND,…]; a KIND is one of " ++ ", ".intercalate (Kind.selectable.map Kind.name)

/-- The options of `emit` and `describe`: the target, the output folder and the kinds. -/
structure Options where
  target : Option String := none
  out : Option String := none
  kinds : List Kind := Kind.selectable

/-- Read the options of `emit` and `describe`, or name the argument that is none. -/
def Options.read : List String → Options → Except String Options
  | [], o => .ok o
  | "--target" :: t :: rest, o => Options.read rest { o with target := some t }
  | "--out" :: d :: rest, o => Options.read rest { o with out := some d }
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

/-- **The pins**, from the library's checkout: its `lean-toolchain`, its Git commit, and Effect's
and tsgo's versions in its TypeScript package (`ts/eff/package.json`). -/
def readInputs (root : System.FilePath) : IO Inputs := do
  let lean := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.copy
  let package ← readJson (root / "ts" / "eff" / "package.json")
  let pin (path : List JsonStep) : IO String := match package.at? path with
    | some (.str v) => pure v
    | _ => throw (IO.userError "the library's ts/eff/package.json pins no version there")
  let effect ← pin [.key "dependencies", .key "effect"]
  let tsgo ← pin [.key "devDependencies", .key "@typescript/native-preview"]
  let library ← try
      let git ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "rev-parse", "HEAD"] }
      pure (if git.exitCode == 0 then some git.stdout.trimAscii.copy else none)
    catch _ => pure none
  return { lean, library, effect, tsgo }

/-- **What a command runs over**: one application, or a named group of programs, each admitted at
the empty application (`checkProgram`), as the wire corpus is. -/
inductive Source where
  | application (app : Application NativeOp)
  | programs (name : String) (programs : List (String × NativeEff))

/-- A source's name: the application's, or the group's. It names the default output folder. -/
def Source.name : Source → String
  | .application app => app.name
  | .programs name _ => name

/-- `check`: the certificate, or the refusal. Over a group, each program's, under its name; the
command refuses when one program refuses. -/
def checkCommand (source : Source) (json : Bool) : IO UInt32 := do
  match source with
  | .application app =>
    match check app with
    | .ok b =>
      if json then IO.println (jsonText (certificate b))
      else for line in certificateLines s!"{app.name}: checked; the service {serviceName app}" b do
        IO.println line
      return 0
    | .error why =>
      if json then IO.println (jsonText why.json) else IO.eprintln ("check: " ++ why.text)
      return 1
  | .programs _ programs =>
    let mut refused := false
    for (name, program) in programs do
      match checkProgram program with
      | .ok b =>
        if json then IO.println (jsonText (.obj [("program", .str name), ("certificate", certificate b)]))
        else for line in certificateLines s!"{name}: checked" b do IO.println line
      | .error why =>
        refused := true
        if json then IO.println (jsonText (.obj [("program", .str name), ("refused", tree why.why)]))
        else IO.eprintln (s!"check: the program {name}: " ++ why.text)
    return if refused then 1 else 0

/-- What an emission is asked for (`Spec`), its prelude's closure and its pins read from the
library's checkout. -/
def readSpec (name : String) (command : List String) (kinds : List Kind) : IO Spec := do
  let root ← libraryRoot
  let prelude ← Prelude.closure (root / Prelude.source)
  let inputs ← readInputs root
  return { name, command, kinds, prelude, inputs }

/-- **A source's emission**, recorded under `command`: an application checked before the library is
read, then emitted (`emitTs`); a group emitted program by program (`emitGroup`). A refusal is
text. -/
def emissionOf (source : Source) (command : List String) (kinds : List Kind) :
    IO (Except String Emission) := do
  match source with
  | .application app =>
    match check app with
    | .error why => return .error why.text
    | .ok b => return (emitTs (← readSpec app.name command kinds) b).mapError (·.text)
  | .programs name programs =>
    return (emitGroup (← readSpec name command kinds) programs).mapError (·.text)

/-- `emit` and `describe`: the emission of the options `rest`, recorded under `command`; written
when `write`, else its manifest printed. -/
def emitCommand (source : Source) (command rest : List String) (write : Bool) : IO UInt32 := do
  let o ← match Options.read rest {} with
    | .ok o => pure o
    | .error why => IO.eprintln s!"{why}; {usage}"; return 2
  unless o.target == some "ts" do
    IO.eprintln s!"--target ts is the one target of this slice; {usage}"
    return 2
  match ← emissionOf source command o.kinds with
  | .error why => IO.eprintln ("emit: " ++ why); return 1
  | .ok e =>
    if write then
      let out := System.FilePath.mk (o.out.getD s!".lake/effect4/{source.name}/ts")
      let files := e.files o.kinds
      Prelude.write out (files.map fun a => (a.path, a.bytes))
      IO.println (s!"emit: {files.length} files to {out}: " ++
        ", ".intercalate (Kind.selectable.filterMap fun k =>
          let n := (files.filter (·.kind.selector == k)).length
          if n == 0 then none else some s!"{k.name} {n}"))
    else IO.println (jsonText e.manifest)
    return 0

/-- The arguments of the `emit` that a `describe` describes: its first `describe` read as `emit`. -/
def asEmit : List String → List String
  | [] => []
  | "describe" :: rest => "emit" :: rest
  | a :: rest => a :: asEmit rest

/-- **The command line over a source**: `check`, `emit` or `describe`. `args` are the arguments as
given, which a header and the manifest record; `rest` are the ones the command reads. -/
def run (source : Source) (args rest : List String) : IO UInt32 :=
  match rest with
  | ["check"] => checkCommand source false
  | ["check", "--json"] => checkCommand source true
  | "emit" :: options => emitCommand source args options true
  | "describe" :: options => emitCommand source (asEmit args) options false
  | _ => do IO.eprintln usage; return 2

/-- **The compiler's entry point** over one application: `check`, `emit` or `describe`. -/
def main (app : Application NativeOp) (args : List String) : IO UInt32 :=
  run (.application app) args args

/-- The group that the first `--group NAME` names, and the arguments without those two. -/
def takeGroup : List String → Option String × List String
  | [] => (none, [])
  | "--group" :: name :: rest => (some name, rest)
  | a :: rest => match takeGroup rest with
    | (group, others) => (group, a :: others)

/-- **The compiler over named sources** (`lake exe effect4`): `main`'s command line, with
`--group NAME` choosing the source of that name. -/
def mainOver (groups : List Source) (args : List String) : IO UInt32 := do
  let names := ", ".intercalate (groups.map (·.name))
  match takeGroup args with
  | (some name, rest) =>
    match groups.find? (·.name == name) with
    | some source => run source args rest
    | none => IO.eprintln s!"no group is named {name}; the groups are {names}"; return 2
  | (none, _) => IO.eprintln s!"--group NAME chooses one of {names}; {usage}"; return 2

end Compiler
