import Meaning
import Effect4.Laws.Api.SessionMeaning
import Test.Dogfood.Scenario.TodoPaged

/-! Finite evaluations for the placed H8/H9 and frontier questions in README.md.
These controls do not import Goals and use no open statement as evidence. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Test.HostMeaningWidening.Controls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote
open Test.HostMeaningWidening
open Test.Dogfood.Scenario (Move Sel script answer ok failed live held refusals)
open Test.Dogfood.P2HandlerLayers (built?)
open Effect4.Program.Stream (pulledTy chunkVal endVal)

/-- Data replies keep the handle-preparation question outside this loop probe. -/
def errTy : Ty := .prod (.lit "ProbeError") .string
def openRow : RowDef := Row.host "Probe.open" .unit .nat errTy "host meaning probe"
def pullRow : RowDef := Row.host "Probe.pull" .nat (pulledTy .nat .unit) errTy "host meaning probe"
def closeRow : RowDef := Row.host "Probe.close" .nat .unit errTy "host meaning probe"
def source : Effect4.Stream.Source :=
  Effect4.Stream.Source.host .nat .unit openRow pullRow closeRow unit

/-- The existing drain loop, followed by explicit cleanup, without a scope constructor. -/
def collect (close : Bool := true) (forget : Bool := false) : Src NativeOp :=
  bindWith source.opened fun cursor =>
    let body := Effect4.Stream.drain source (.list .nat) Effect4.Modules.nilT cursor
      (fun acc chunk => succeed (if forget then chunk else app "append" [acc, chunk]))
    let guarded := if close then onExitWith body (fun _ => source.close cursor) else body
    bindWith guarded fun last => succeed (app "fst" [last])

def request (main : Src NativeOp) : Module NativeOp :=
  { rows := [openRow, pullRow, closeRow], main }

def played (main : Src NativeOp) (moves : List Move) : Option Run :=
  (built? (request main)).map fun b => Test.Dogfood.Scenario.play (Run.open b "meaning-probe") moves

def opening : List Move := answer (.row "Probe.open") (ok (.nat 7))
def page (xs : List Val) : List Move := answer (.row "Probe.pull") (ok (chunkVal xs))
def ending : List Move := answer (.row "Probe.pull") (ok (endVal .unit))
def closing : List Move := answer (.row "Probe.close") (ok .unit)
def twoPages : List Move := script [[.start], opening, page [.nat 1, .nat 2], page [.nat 3], ending, closing]
def beforeClose : List Move := script [[.start], opening, page [.nat 1, .nat 2], page [.nat 3], ending]
def failedPull : List Move := script [[.start], opening, page [.nat 1],
  answer (.row "Probe.pull") (failed "ProbeError" "pull"), closing]
def failedOpen : List Move := script [[.start], answer (.row "Probe.open") (failed "ProbeError" "open")]
def failedBoth : List Move := script [[.start], opening,
  answer (.row "Probe.pull") (failed "ProbeError" "pull"),
  answer (.row "Probe.close") (failed "ProbeError" "close")]

def stopOf (s : Run) : Option End :=
  match s.exit with
  | some ex => some (.finished ex)
  | none => (s.outstanding.head?).bind fun call =>
    match call.op with
    | .external i => some (.waiting i call.request)
    | _ => none

/-- Compare all stores and the root/frontier observation. The tape must be consumed exactly. -/
def agrees (main : Src NativeOp) (moves : List Move) (k : Nat) : Bool :=
  match played main moves with
  | none => false
  | some s =>
    let seen := observeTree (tapeHost s.built.table)
      (denoteRowsB s.built.table k s.built.program []) Stores.empty (Run.appliedExits s)
    decide (some seen.stop = stopOf s ∧ seen.stores = s.machine.state ∧ seen.host = [])

def coarseAgrees (moves : List Move) (k : Nat) : Bool :=
  match played (collect) moves with
  | none => false
  | some s => decide (coarseRowsB s.built.table k s.built.program [] Stores.empty
      (Run.appliedExits s) = s.exit.map (fun ex => ((ex, s.machine.state), [])))

def requests (moves : List Move) : Option (List (String × Val)) :=
  (played (collect) moves).map fun s => (held s).map fun call => (call.row, call.request)

def ready (moves : List Move) : Bool :=
  match played (collect) moves with
  | none => false
  | some s => Run.funded s && Run.atRest s && Run.hostDriven s &&
    LoopedRows s.built.program && LoopedDataRows s.built.table s.built.program &&
    !(StraightRows s.built.table s.built.program) && (refusals s).isEmpty

#guard (built? (request (collect))).isSome
#guard ready twoPages
#guard ready beforeClose
#guard (played (collect) twoPages).bind (·.exit) = some (.success (.list [.nat 1, .nat 2, .nat 3]))
#guard requests twoPages = some [("Probe.open", .unit), ("Probe.pull", .nat 7),
  ("Probe.pull", .nat 7), ("Probe.pull", .nat 7), ("Probe.close", .nat 7)]
#guard agrees (collect) twoPages 4
#guard agrees (collect) twoPages 7
#guard coarseAgrees twoPages 4
#guard agrees (collect) beforeClose 4
#guard coarseAgrees beforeClose 4
#guard agrees (collect) failedPull 3
#guard agrees (collect) failedOpen 0
#guard agrees (collect) failedBoth 3
#guard (played (collect) beforeClose).bind (·.exit) = none
#guard (played (collect) failedOpen).map (fun s => (held s).map (·.row)) = some ["Probe.open"]

/-- A cut is neither a finished failure nor a request for a host reply. -/
def budgetCut : Bool :=
  match played (collect) twoPages with
  | none => false
  | some s =>
    let seen := observeTree (tapeHost s.built.table)
      (denoteRowsB s.built.table 1 s.built.program []) Stores.empty (Run.appliedExits s)
    decide (seen.stop = .budget ∧ seen.host.length = 3 ∧ seen.stores = Stores.empty)
#guard budgetCut
#guard !(agrees (collect) twoPages 1)

/- A leaky program returns the same elements. Request history still distinguishes it. -/
#guard (played (collect false) beforeClose).bind (·.exit) =
  some (.success (.list [.nat 1, .nat 2, .nat 3]))
#guard (played (collect false) beforeClose).map (fun s => (held s).map (·.row)) =
  some ["Probe.open", "Probe.pull", "Probe.pull", "Probe.pull"]
#guard agrees (collect false) beforeClose 4
#guard (played (collect true true) twoPages).bind (·.exit) = some (.success (.list [.nat 3]))
#guard agrees (collect true true) twoPages 4

/- The real TodoPaged program lies outside this probe's fragment. -/
#guard ((built? (Test.Dogfood.Scenario.TodoPaged.request
  Test.Dogfood.Scenario.TodoPaged.listPaged)).map fun b => LoopedRows b.program) = some false
#guard ((built? (Test.Dogfood.Scenario.TodoPaged.request
  Test.Dogfood.Scenario.TodoPaged.listPaged)).map fun b => LoopedDataRows b.table b.program) = some false

end Test.HostMeaningWidening.Controls
