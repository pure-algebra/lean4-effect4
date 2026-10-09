import Lean
import Tools.ArchitectureRoles

/-!
# Tools.Exposure — the import gate of decisions row 332, in report mode

A user of the library imports only entry modules and the module library
(`docs/research/2026-10-08-library-shape.md`). This module reads the import header of every Lean
file under the user roots (`Tools.Architecture.userRoots`, the acceptance programs), with the
compiler's own header parser, and classifies each import of the tree by its exposure
(`Tools.Architecture.exposures`). `#exposure_report` prints the imports a user may not make, with
their exposure, and a count by exposure. `#exposure_gate`, at the foot of `Test/All.lean`, refuses
the same imports (cutover slice C4): the acceptance programs import entry modules, a composed
module's own files and the batteries' support only. An import outside the tree (Lean, Std, the
pinned packages) is not the gate's business.
-/

namespace Tools.Exposure
open Lean Elab Command
open Tools.Architecture (Exposure exposureOf userRoots)

/-- The source path of a module of the tree, or `none` outside it. -/
def pathOf (m : Name) : Option String :=
  let parts := m.components.map (·.toString (escape := false))
  match parts with
  | "Effect4" :: _ | "OCaml5" :: _ => some ("src/" ++ "/".intercalate parts ++ ".lean")
  | "Test" :: _ => some ("/".intercalate parts ++ ".lean")
  | "Tools" :: _ | "ProofGraph" :: _ | "Conform" :: _ | "Drivers" :: _ | "Effect4Gen" :: _
  | "TestSupport" :: _ => some ("tools/" ++ "/".intercalate parts ++ ".lean")
  | _ => none

/-- One import of a user's file that the gate would refuse. -/
structure Finding where
  file : String
  imported : Name
  exposure : String
  deriving Inhabited

/-- Every Lean file under a directory, sorted. -/
def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  if !(← root.pathExists) then return #[]
  let all ← root.walkDir
  return (all.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)

/-- The findings over `roots` (the user roots by default), and the count of tree imports by
exposure. -/
def scan (roots : List String := userRoots) : IO (Array Finding × Std.HashMap String Nat) := do
  let mut findings := #[]
  let mut counts : Std.HashMap String Nat := {}
  for root in roots do
    for f in ← leanFiles root do
      let (imports, _, _) ← Lean.Elab.parseImports (← IO.FS.readFile f) (some f.toString)
      for i in imports do
        let some p := pathOf i.module | continue
        let e := (exposureOf p).map (·.word) |>.getD "undeclared"
        counts := counts.insert e (counts.getD e 0 + 1)
        let ok := (exposureOf p).map (·.userImportable) |>.getD false
        unless ok do findings := findings.push { file := f.toString, imported := i.module, exposure := e }
  return (findings, counts)

/-- `#exposure_report`: the imports of the user roots that row 332's gate would refuse. -/
syntax (name := exposureReport) "#exposure_report" : command

@[command_elab exposureReport] def elabExposureReport : CommandElab := fun _ => do
  let (findings, counts) ← scan
  let distinct := findings.foldl (fun acc f => if acc.contains f.imported then acc else acc.push f.imported) #[]
  let mut out := s!"user roots {userRoots}: {findings.size} imports a user may not make, " ++
    s!"{distinct.size} distinct modules"
  for (e, n) in counts.toList.toArray.qsort (fun a b => a.1 < b.1) do out := out ++ s!"\n  {e}: {n}"
  for m in distinct.qsort (·.toString < ·.toString) do
    let users := findings.filter (·.imported == m)
    out := out ++ s!"\n{m} ({users[0]!.exposure}), from {users.size} files"
  logInfo out

/-- `#exposure_gate`: refuse every import of the user roots that row 332's gate does not admit,
naming the file, the module and its exposure. `Test/All.lean` imports every acceptance program,
so an import line that changes elaborates this command again. -/
syntax (name := exposureGate) "#exposure_gate" (ppSpace str)? : command

/-- The gate's check over `roots`. With a path, `#exposure_gate "p"` reads that folder instead of
the user roots: the red control of `Test/Audit/Exposure.lean` reads a fixture. -/
@[command_elab exposureGate] def elabExposureGate : CommandElab := fun stx => do
  let roots := match stx[1].getOptional? with
    | some s => [s.isStrLit?.getD ""]
    | none => userRoots
  let (findings, _) ← scan roots
  unless findings.isEmpty do
    throwError (String.intercalate "\n" (findings.toList.map fun f =>
      s!"exposure gate: {f.file} imports {f.imported}, which is {f.exposure}; a user imports entry modules and a composed module's own files"))

end Tools.Exposure
