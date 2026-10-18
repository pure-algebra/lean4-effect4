import Effect4.Laws.Api.Built
import Effect4.Laws.Api.LiveRecord
import Effect4.Run.View

/-! Finite S4 admission and run controls. The restored-run theorem keeps its full statement.
The tests claim no native translation theorem or host progress. -/
set_option autoImplicit false
namespace Test.Program.RunAdmissionControls
open Effect4 Effect4.Program

def ask : Row :=
  { name := "ask", spelling := "ask", kind := .async,
    registration := .external, request := .unit, answer := .nat, cite := "S4 loop 1" }
def app : SigApp := .ofTable [ask]
def program : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit)) (.succeed (.var 0))
def sketch : Sketch := { program }
def budget : Api.Budget := { fuel := 71, compileFuel := 109 }

def opened : Option Live :=
  (Api.Built.ofSketch app sketch).toOption.map fun built =>
    (Live.open built "demo" budget).feedAll [.start]

-- Loop 1, row 5: the admitted program waits on the application row.
#guard opened.isSome
#guard opened.map (·.run.built.rowNames) = some [("ask", 0)]
#guard opened.map (·.run.budget) = some budget
#guard opened.map (fun live => (live.view.awaiting.map (·.await)).length) = some 1

-- Row 6: an application without a received answer refuses and records one command.
def premature : Option Live := opened.map fun live => (live.feed (.apply (.row "ask"))).1
#guard premature.map (·.run.phases) = some [.progressed, .refused .noCall]
#guard premature.map (·.run.journal.length) = some 2

-- Row 7: receive binds and submits, then application and flush finish the program.
def finished : Option Live := premature.map fun live => live.feedAll
  [.receive (.key ⟨Api.root, 0⟩) (.ofExit (.success (.nat 7))),
   .apply (.key ⟨Api.root, 0⟩), .flush]
#guard finished.map (·.run.exit) = some (some (.success (.nat 7)))
#guard finished.map (·.run.journal.length) = some 6

-- A live hole is a host row: the sketch admits at the application extended by its holes
-- (README.md version 2, §3.3 row 4). At the application alone the same program refuses, which is
-- why a saved run restores through `ofProgram` at the application it recorded.
def liveHole : Sketch :=
  { program := .perform (.external 1) (.lit .unit)
    holes := [{ ask with name := "h0", spelling := "h0" }] }
#guard (admitProgram liveHole.program (app.withHoles liveHole.holes)).isOk
#guard (Api.Built.ofSketch app liveHole).isOk
#guard !(Api.Built.ofProgram app liveHole.program).isOk
#guard (Api.Built.ofSketch app liveHole).toOption.map (·.rowNames) =
  some [("ask", 0), ("h0", 1)]
-- Unused metadata adds no admission rule of its own.
#guard (Api.Built.ofSketch {} { program := .succeed (.lit (.nat 1)), holes := [ask] }).isOk

-- The record retains stored names, empty session names, and both budgets.
def restored : Option Live :=
  (Api.Built.ofSketch app sketch).toOption.bind fun built =>
    let live := Live.open { built with rowNames := [("stored", 9)] } "" budget
    (LiveRecord.save live).restore.toOption
#guard restored.map (·.run.id) = some ""
#guard restored.map (·.run.built.rowNames) = some [("stored", 9)]
#guard restored.map (·.run.budget) = some budget
end Test.Program.RunAdmissionControls
