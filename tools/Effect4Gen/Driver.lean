import Lean

/-!
# Effect4Gen.Driver — the portable orchestration of the derived-code generator

Owner: the driver that reads `tools/Effect4Gen/manifest.json` and runs
`tools/Effect4Gen/Main.lean` once per group, then the projection guard
`tools/Effect4Gen/Check.lean` over what it emitted.

    lake env lean --run tools/Effect4Gen/Driver.lean
    lake env lean --run tools/Effect4Gen/Driver.lean --group Program --check
    lake env lean --run tools/Effect4Gen/Driver.lean --verify --check

The manifest is data read by this portable driver. A new group is one entry in
that file and no change to orchestration; Machine, Tape and Log remain owed at X2.

## What it does per group, and what that has to be

One invocation per manifest group:

    lake env lean -M 4096 --run tools/Effect4Gen/Main.lean --group <Name>
      --imports <Imports> --out <Out> [--append <Guards>] [--kind <k>]... <Types...>

with the group's fields in the manifest's order, the output file's bytes compared before
and after, and one line per group saying `new`, `CHANGED` or `same`. `--check` then
type-checks each emitted file, counts its `#print axioms` receipts, refuses any that
reaches `sorryAx` or `Classical.choice`, and runs the projection guard over all of them.
`--verify` turns a change into a non-zero exit and also asks `git diff --exit-code`
whether an emitted file differs from the committed one.

The manifest retains its legacy backslash argument spelling. The driver stages
those paths where needed by the host filesystem. Main prints forward-slash
paths in the reproduction header, so the recorded command is portable even
when a checker redirects the actual output to a temporary file.

## What it does not do

No timeout is implemented inside this driver. Phase 0 step 0.5 supplies the
per-invocation timeout in the bash entry point. Until then, run under the lane
lock and memory cap required by the dispatch. The driver does not own a second
process-management implementation.

This is a tool (`IO`); it is not part of any audited library.
-/

open Lean

namespace Effect4Gen.Driver

/-- One manifest group: the fields of the old in-script manifest, by the same names and
in the same order. -/
structure Group where
  name : String
  imports : String
  /-- The `--out` argument, in the manifest's spelling. -/
  out : String
  /-- The `--append` argument, or the empty string when the group appends no guards. -/
  guards : String
  kinds : Array String
  types : Array String
  deriving Inhabited

def getStr (j : Json) (key : String) : Except String String := do
  let v ← j.getObjVal? key
  Json.getStr? v

/-- A missing key reads as the empty string, so a group that appends no guards may either
write `""` or omit the field. -/
def getStrD (j : Json) (key : String) : Except String String :=
  match j.getObjVal? key with
  | .ok v => Json.getStr? v
  | .error _ => .ok ""

def getStrArr (j : Json) (key : String) : Except String (Array String) := do
  let v ← j.getObjVal? key
  let arr ← v.getArr?
  arr.mapM Json.getStr?

def parseGroup (j : Json) : Except String Group := do
  let name ← getStr j "Name"
  let imports ← getStr j "Imports"
  let out ← getStr j "Out"
  let guards ← getStrD j "Guards"
  let kinds ← getStrArr j "Kinds"
  let types ← getStrArr j "Types"
  return { name, imports, out, guards, kinds, types }

def parseManifest (text : String) : Except String (Array Group) := do
  let j ← Json.parse text
  let groups ← j.getObjVal? "groups"
  let arr ← groups.getArr?
  arr.mapM parseGroup

/-- The manifest spelling as this host's filesystem reads it. On Windows both `/` and `\`
separate, so the spelling is already a path; elsewhere `\` is an ordinary character in a
file name and the path has to be respelled. -/
def hostPath (s : String) : String :=
  if System.Platform.isWindows then s else s.replace "\\" "/"

/-- Does this host need the manifest spelling translated before the filesystem sees it? -/
def needsStaging (s : String) : Bool := hostPath s != s

/-- A manifest string as a path value. Every filesystem call below goes through this and
`hostPath`, so no `String`/`FilePath` coercion is left to chance. -/
def filePath (s : String) : System.FilePath := System.FilePath.mk s

def exists? (path : String) : IO Bool := System.FilePath.pathExists (filePath path)

/-- The emitted file's text, for the before/after comparison. -/
def readIfPresent (path : String) : IO (Option String) := do
  if ← exists? path then
    return some (← IO.FS.readFile (filePath path))
  else
    return none

def copyFile (source target : String) : IO Unit := do
  IO.FS.writeBinFile (filePath target) (← IO.FS.readBinFile (filePath source))

def removeIfPresent (path : String) : IO Unit := do
  if ← exists? path then IO.FS.removeFile (filePath path)

/-- Non-overlapping occurrences of `needle` in `text`, by the split it induces. -/
def countOccurrences (text needle : String) : Nat :=
  if needle.isEmpty then 0 else (text.splitOn needle).length - 1

structure Result where
  code : Nat
  out : String
  err : String

def runLake (args : Array String) : IO Result := do
  let child ← IO.Process.output { cmd := "lake", args := args }
  return { code := child.exitCode.toNat, out := child.stdout, err := child.stderr }

/-- The generator's argument list for one group: the old `Invoke-Lean`'s, in its order. -/
def generateArgs (tool : String) (g : Group) (appendGuards : Bool) : Array String :=
  let base := #["env", "lean", "-M", "4096", "--run", tool,
    "--group", g.name, "--imports", g.imports, "--out", g.out]
  let base := if appendGuards then base ++ #["--append", g.guards] else base
  let base := g.kinds.foldl (fun acc k => acc ++ #["--kind", k]) base
  base ++ g.types

structure Config where
  group : Option String := none
  check : Bool := false
  verify : Bool := false
  manifest : String := "tools/Effect4Gen/manifest.json"
  help : Bool := false

partial def parseArgs : List String → Config → Except String Config
  | [], c => .ok c
  | "--group" :: g :: rest, c => parseArgs rest { c with group := some g }
  | "--manifest" :: p :: rest, c => parseArgs rest { c with manifest := p }
  | "--check" :: rest, c => parseArgs rest { c with check := true }
  | "--verify" :: rest, c => parseArgs rest { c with verify := true }
  | "--help" :: rest, c => parseArgs rest { c with help := true }
  | "-h" :: rest, c => parseArgs rest { c with help := true }
  | a :: _, _ => .error s!"unknown argument {a}; try --help"

def usage : String :=
  "lake env lean --run tools/Effect4Gen/Driver.lean [--group NAME] [--check] [--verify] " ++
    "[--manifest PATH]"

def joined (xs : Array String) : String := String.intercalate ", " xs.toList

end Effect4Gen.Driver

open Effect4Gen.Driver in
def main (argv : List String) : IO Unit := do
  let config ← match parseArgs argv {} with
    | .ok c => pure c
    | .error e => throw (IO.userError e)
  if config.help then
    IO.println usage
    return
  let tool := "tools/Effect4Gen/Main.lean"
  let guardTool := "tools/Effect4Gen/Check.lean"
  let manifestText ← IO.FS.readFile (filePath config.manifest)
  let groups ← match parseManifest manifestText with
    | .ok gs => pure gs
    | .error e => throw (IO.userError (config.manifest ++ ": " ++ e))
  if let some name := config.group then
    unless groups.any (fun g => g.name == name) do
      throw (IO.userError ("no group named " ++ name ++ " in " ++ config.manifest))

  let mut changed : Array String := #[]
  let mut failed : Array String := #[]
  let mut files : Array String := #[]

  for g in groups do
    let mut skip := false
    if let some name := config.group then
      if g.name != name then skip := true
    if skip then continue
    let outHost := hostPath g.out
    files := files.push outHost
    if let some parent := (System.FilePath.mk outHost).parent then
      IO.FS.createDirAll parent
    let before ← readIfPresent outHost
    -- The generator opens its guard fragment by the manifest spelling. Where that is not
    -- a path on this host, stage a copy under the literal name, so the argument the
    -- emitted header records and the file the generator reads stay the same string.
    let guardsHost := hostPath g.guards
    let appendGuards := g.guards != "" && (← exists? guardsHost)
    let stagedGuards := appendGuards && needsStaging g.guards
    if stagedGuards then copyFile guardsHost g.guards
    let r ← runLake (generateArgs tool g appendGuards)
    if stagedGuards then removeIfPresent g.guards
    -- Likewise the output: the generator wrote it under the literal name, so move it.
    if needsStaging g.out && (← exists? g.out) then
      copyFile g.out outHost
      removeIfPresent g.out
    if r.code != 0 then
      IO.println ("FAILED  " ++ g.name ++ ": the generator exited " ++ toString r.code)
      unless r.out.isEmpty do IO.println r.out
      unless r.err.isEmpty do IO.println r.err
      failed := failed.push g.name
      continue
    let after ← readIfPresent outHost
    match before, after with
    | _, none =>
      IO.println ("FAILED  " ++ g.name ++ ": the generator left no output at " ++ outHost)
      failed := failed.push g.name
    | none, some _ =>
      IO.println ("new     " ++ g.name ++ " -> " ++ g.out)
      changed := changed.push g.name
    | some b, some a =>
      if b == a then
        IO.println ("same    " ++ g.name ++ " -> " ++ g.out)
      else
        IO.println ("CHANGED " ++ g.name ++ " -> " ++ g.out)
        changed := changed.push g.name

  if config.check then
    for file in files do
      if ← exists? file then
        let r ← runLake #["env", "lean", "-M", "4096", file]
        let receipts := countOccurrences r.out "depends on axioms"
          + countOccurrences r.out "does not depend on any axioms"
        let bad := countOccurrences r.out "sorryAx" + countOccurrences r.out "Classical.choice"
        if bad > 0 then
          IO.println ("FAILED  " ++ file ++ ": " ++ toString bad ++
            " receipts reach sorryAx or Classical.choice")
          failed := failed.push file
        if r.code != 0 then
          IO.println ("FAILED  " ++ file ++ ": lean exited " ++ toString r.code)
          unless r.out.isEmpty do IO.println r.out
          unless r.err.isEmpty do IO.println r.err
          failed := failed.push file
        else
          IO.println ("green   " ++ file ++ " (" ++ toString receipts ++ " receipts)")
    let mut present : Array String := #[]
    for file in files do
      if ← exists? file then present := present.push file
    if !present.isEmpty then
      let r ← runLake (#["env", "lean", "-M", "4096", "--run", guardTool] ++ present)
      if r.code != 0 then
        IO.println "FAILED  the projection guard refused"
        unless r.out.isEmpty do IO.println r.out
        unless r.err.isEmpty do IO.println r.err
        failed := failed.push "projection guard"
      else
        let ok := countOccurrences r.out "\nok " + (if r.out.startsWith "ok " then 1 else 0)
        IO.println ("green   the projection guard agrees (" ++ toString ok ++ " shapes)")

  IO.println ""
  IO.println ("changed: " ++ (if changed.isEmpty then "nothing" else joined changed))
  if !failed.isEmpty then
    IO.println ("failed:  " ++ joined failed)
    IO.Process.exit 1
  if config.verify then
    if !changed.isEmpty then
      IO.println "refusing: a generated file changed; commit the regenerated files"
      IO.Process.exit 1
    let mut present : Array String := #[]
    for file in files do
      if ← exists? file then present := present.push file
    if !present.isEmpty then
      let git ← IO.Process.output { cmd := "git", args := #["diff", "--exit-code", "--"] ++ present }
      if git.exitCode != 0 then
        IO.println "refusing: a derived file differs from the committed one"
        unless git.stdout.isEmpty do IO.println git.stdout
        IO.Process.exit 1
