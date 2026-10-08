import Test.Program.ModuleDefinitions
import Effect4.Modules.Pool.Ops
import Conform.Core.Report

/-!
Finite exploration of native Effect module compatibility.
The emit command checks three Lean executions and writes their TypeScript declarations.
The report command uses Conform's existing evidence, coverage and outcome definitions.
This file states no new theorem and changes no module profile.
-/

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.ModuleDefinitions

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace ModuleCompatibilityProbe

-- The design note's user-defined module example executes through the same path.
namespace UserGateExample

eff_module Gate where
  tryTake (gate : .refOf Semaphore.cellTy) (count : .nat) : .bool :=
    Semaphore.takeIfAvailable gate count

def gateApi := Gate.make "gate"

def application : Module NativeOp := gateApi.module (eff do
  let gate ← Semaphore.make 2
  gateApi.tryTake gate (nat 1))

def checked := Api.Author.build application

#guard runModule application = some (.success (.bool true))

end UserGateExample

def overRelease : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let taken ← permits.take q (nat 1)
  let free ← permits.release q (nat 3)
  return tuple [taken, free]

def failedAcquisition : Src NativeOp :=
  scope (andThen (Pool.make .nat 1 (fail (nat 77))) (succeed (str "made")))

#guard runModule (permits.module immediate) =
  some (.success (.list [.nat 1, .nat 2, .bool true, .bool false]))
#guard runModule (permits.module overRelease) = some (.success (.list [.nat 1, .nat 2]))
#guard runModule { main := failedAcquisition } = some (.failure (.fail (.tag 77)))

-- The input profile and observation are declared before any external result is read.
def scenarios : List (String × String × Module NativeOp) :=
  [("semaphore-immediate", "Fixed total 2; balanced release; immediate public answers",
      permits.module immediate),
    ("semaphore-over-release", "Release 3 after taking 1; outside the balanced-release premise",
      permits.module overRelease),
    ("pool-acquisition-failure", "Size 1; acquisition fails with 77; observe construction exit",
      { main := failedAcquisition })]

structure Sample where
  id : String
  emitted : Lean.Json
  native : Lean.Json
  deriving Lean.FromJson, Lean.ToJson

structure Results where
  pins : List Conform.Pin
  inputs : List Conform.Input
  samples : Array Sample
  deriving Lean.FromJson

def subject (name : String) : Conform.Subject := ⟨"scenario", ["module-compatibility", name]⟩

def hostCheck : String := "module.native-observation"

def required : Array Conform.CheckId :=
  (scenarios.toArray.map fun (name, _, _) => ⟨hostCheck, subject name⟩) ++
    #[⟨"module.whole-run-simulation", ⟨"claim", ["semaphore-expansion-agrees"]⟩⟩,
      ⟨"module.external-execution", ⟨"connection", ["generated-TypeScript-vs-native-Effect"]⟩⟩]

def report (results : Results) : Conform.Report := Id.run do
  let mut rows := #[]
  for (name, scope, _) in scenarios do
    let found := results.samples.filter (·.id == name)
    let row := match found.toList with
      | [sample] =>
        let detail := Lean.Json.mkObj [("scope", .str scope), ("observation", Lean.toJson sample)]
        if sample.emitted == sample.native then
          Conform.Row.pass hostCheck (subject name) .tested
            "The two finite executions return the same public answer" detail
        else
          Conform.Row.counterexample hostCheck (subject name)
            "The two finite executions return different public answers" detail
      | [] => Conform.Row.unresolved hostCheck (subject name) "The host result is missing"
      | _ => Conform.Row.refused hostCheck (subject name) "Duplicate host results"
    rows := rows.push row
  for sample in results.samples do
    unless scenarios.any (fun (name, _, _) => name == sample.id) do
      rows := rows.push (Conform.Row.refused hostCheck (subject sample.id) "Unexpected host result")
  rows := rows ++ #[
    Conform.Row.unresolved "module.whole-run-simulation"
      ⟨"claim", ["semaphore-expansion-agrees"]⟩
      "The wrapper and walk connection remains open under R10 and decisions row 329",
    Conform.Row.unresolved "module.external-execution"
      ⟨"connection", ["generated-TypeScript-vs-native-Effect"]⟩
      "The finite executions establish no theorem about all target executions"]
  return {
    tool := "module-compatibility-probe"
    pins := results.pins
    inputs := results.inputs
    expected := required.size
    required := required
    rows := rows }

-- Controls exercise the actual existing report boundary, not a second grading format.
#guard !(report { pins := [], inputs := [], samples := #[] }).rows.any
  (fun row => row.outcome == .pass)
#guard (report { pins := [], inputs := [], samples := #[] }).exitCode == 2
#guard !(report { pins := [], inputs := [], samples :=
  #[{ id := "unexpected", emitted := .null, native := .null }] }).complete

#guard (report { pins := [], inputs := [], samples :=
  #[{ id := "semaphore-immediate", emitted := .null, native := .null },
    { id := "semaphore-immediate", emitted := .null, native := .null }] }).rows.any
  (fun row => row.outcome == .refused)

end ModuleCompatibilityProbe

open ModuleCompatibilityProbe

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", directory] =>
    IO.FS.createDirAll directory
    for (name, _, source) in scenarios do
      let .ok built := Api.Author.build source | throw (IO.userError (name ++ ": build refused"))
      let some printed := Api.printModule "main" built.program built.table
        | throw (IO.userError (name ++ ": print refused"))
      IO.FS.writeFile (System.FilePath.mk directory / (name ++ ".ts"))
        (String.join (printed.decls.map (TypeScript.Render.decl TypeScript.house0)))
    IO.println s!"Checked and wrote {scenarios.length} finite compatibility examples"
    return 0
  | ["report", input, output] =>
    let .ok json := Lean.Json.parse (← IO.FS.readFile input)
      | throw (IO.userError "invalid result JSON")
    let .ok results := Lean.fromJson? (α := Results) json
      | throw (IO.userError "invalid result shape")
    (report results).emit (some output)
  | _ => throw (IO.userError "expected emit DIRECTORY or report INPUT OUTPUT")
