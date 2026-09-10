import Lean
import Lake.Build.Trace

/-!
Shared provenance for committed projections. Each direct import's Lake `depHash`
already includes its transitive imports. Sort by module name and hash those values,
the producer source, and its explicitly named run-time inputs. Build the imports
before calling this function; an absent trace is an error, never an empty input.
Lake's diagnostic paths and logs are excluded: they identify a local build directory,
not an input. Revision is informational; checks compare every other byte.
-/

namespace Tools.GeneratedStamp

private def sha256 (text : String) : IO String := do
  let out ← try
    IO.Process.output { cmd := "sha256sum" } (some text)
  catch _ =>
    IO.Process.output { cmd := "shasum", args := #["-a", "256"] } (some text)
  unless out.exitCode == 0 do throw (IO.userError out.stderr)
  let digest := (out.stdout.splitOn " ").head!
  unless digest.length == 64 do throw (IO.userError "invalid SHA-256 output")
  return digest

private def importsOf (text : String) : IO (List String) := do
  let (imports, _, messages) ← Lean.Elab.parseImports text
  if messages.hasErrors then throw (IO.userError "cannot parse stamp import header")
  return imports.toList.map (fun i => i.module.toString)

private def toolchainModule (name : String) : Bool :=
  ["Lean", "Init", "Std", "Lake"].any fun root => name == root || name.startsWith (root ++ ".")

private def sourceOfTrace (trace : Lean.Json) : Except String (String × String) := do
  for entry in ← trace.getObjValAs? (Array Lean.Json) "inputs" do
    let parts ← entry.getArr?
    if let some first := parts[0]? then
      if let .ok name := first.getStr? then
        if name.endsWith ".lean" then return (name, ← parts[1]!.getStr?)
  throw "Lake trace has no source input"

/-- One stamp implementation for source headers and data sidecars. Import traces
are keyed with their current source bytes, so an edit is visible before a rebuild.
The caller must build imports before generation. `modules` adds dynamic imports. -/
def line (source : String) (modules : List String := [])
    (files : List String := []) : IO String := do
  Lean.initSearchPath (← Lean.findSysroot)
  let text ← IO.FS.readFile source
  let direct ← if source.endsWith ".lean" then importsOf text else pure []
  let mut pending := direct ++ modules
  let mut seen : List String := []
  let mut rows : List String := []
  for _ in [:8192] do
    let name :: rest := pending | break
    pending := rest
    if toolchainModule name || seen.contains name then continue
    seen := name :: seen
    let path := (← Lean.findOLean name.toName).withExtension "trace"
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    let hash ← IO.ofExcept (json.getObjValAs? String "depHash")
    let (recordedPath, recordedHash) ← IO.ofExcept (sourceOfTrace json)
    let resolved ← IO.Process.run { cmd := "python3", args := #["scripts/lib/generated_inputs.py",
      "--source-of", name, "--artifact", path.toString] }
    let current : System.FilePath := resolved.trimAscii.toString
    unless recordedPath.replace "\\" "/" |>.endsWith (name.replace "." "/" ++ ".lean") do
      throw (IO.userError s!"trace source does not identify {name}: {recordedPath}")
    unless (← Lake.computeTextFileHash current).hex == recordedHash do
      throw (IO.userError s!"stale compiled input for {name}; build its current source before generation")
    let moduleSource ← IO.FS.readFile current
    rows := s!"trace {name} {hash} source={← sha256 moduleSource}\n" :: rows
    pending := pending ++ (← importsOf moduleSource)
  unless pending.isEmpty do throw (IO.userError "stamp import closure exceeds 8192 entries")
  rows := rows.mergeSort (· ≤ ·)
  let paths : List String := (source :: files).map fun p => p.replace "\\" "/"
  for path in paths.eraseDups.mergeSort (· ≤ ·) do
    rows := rows ++ [s!"file {path} {← sha256 (← IO.FS.readFile path)}\n"]
  let inputs ← sha256 (String.join rows)
  let rev ← IO.Process.run { cmd := "git", args := #["describe", "--always", "--dirty"] }
  return s!"cut-from: rev={rev.trimAscii.toString} toolchain={Lean.versionString} inputs={inputs}"

/-- A data artifact's bytes remain untouched. Its producer writes adjacent metadata. -/
def sidecar (path : System.FilePath) (stamp : String) : IO Unit :=
  IO.FS.writeFile (path.toString ++ ".cut-from") (stamp ++ "\n")

end Tools.GeneratedStamp
