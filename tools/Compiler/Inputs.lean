import Compiler.Emit

/-!
# Compiler.Inputs — locate the library and read an emission's sources and pins

The compiler's commands share these readers. `sourceOf` refuses ambiguous sources, and
`readInputs` hashes the executable's source closure. `Test.Codegen.CompilerEmit` reads the
result's pure address calculation. These IO operations establish no program behaviour.
-/

namespace Compiler

open Effect4 Effect4.Program

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

end Compiler
