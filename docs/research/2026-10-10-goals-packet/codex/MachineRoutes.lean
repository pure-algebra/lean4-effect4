import Test.Dogfood.Scenario.Workers
import Effect4.Laws.Program.ControlSteps
import ProofGraph.AxiomAudit

/-! A finite route comparison at Workers' one-job program.
The symbolic command reader uses the actual compiled evaluator on an arbitrary machine.
The resting-stage classifier compares selected host, cut and forced-yield scripts.
No search or whole-program invariant is claimed. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace MachineRoutes

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.Workers

abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev Command := Cmd EffName EffThunk Val Err Defect FiberId Ann

/-- A representative worker write: appending an identity to a log. -/
def workerNote (identity : Nat) : SyncOp :=
  .refUpdate ⟨1⟩ (.app "append" (.cons (.var 0) (.cons (.app "cons" (.cons (.lit (.nat identity)) (.cons (.app "nil" .nil) .nil))) .nil))) []

/-- The arbitrary-machine route handles a representative worker write with symbolic
state, worker, stack, values, budget and command residue. -/
theorem worker_note_step (root : NativeEff) (table : RowTable) (m : Api.Machine)
    (id : FiberId) (f : Fiber) (identity : Nat) (value : Val) (state : Stores)
    (rest : List Command) (found : m.fiber? id = some f)
    (current : f.frame.current = .sync (.op (workerNote identity)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep (workerNote identity) m.state = some (state, value)) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id false) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id false] ++ rest) :=
  ControlSteps.loop_sync_op root table m id f (workerNote identity) state value false rest
    found current interrupt override budget answer

/-- A resting host-stage invariant excludes a fiber in the middle of an entry. -/
def atRest (s : Run) : Bool := s.machine.fibers.all fun f => !f.running

/-- Whether a parked fiber retains the extra continuation of an injected yield. -/
def delayed (s : Run) : Bool := s.machine.fibers.any fun f =>
  f.frame.stack.any fun k => match k with
    | .onSuccessConst _ _ => true
    | _ => false

/-- The selected scripts include ordinary host progression, a cut and an injected yield. -/
def cases : List (String × Api.Budget × List Move) :=
  [ ("parked", budget, parked)
  , ("running-job", budget, script [parked, answer w1 (ok (.nat 1)), [.hold w1]])
  , ("finished", budget, script [parked, answer w1 (ok (.nat 1)), [.hold w1], answer w1 (ok .unit)])
  , ("cancelled", budget, script [parked, [.cancel ⟨0⟩]])
  , ("cut", { budget with fuel := 1 }, [.start])
  , ("forced-yield", budget,
       script [parked, [.row (.control (.yieldVerdict ⟨1⟩ true))], answer w1 (ok (.nat 1))]) ]

#eval show IO Unit from do
  match Api.Author.build (crew 1) with
  | .error _ => throw (IO.userError "Workers crew 1 refuses admission")
  | .ok b =>
    for (label, funds, moves) in cases do
      let s := Test.Dogfood.Scenario.play (Run.open b "workers" funds) moves
      IO.println s!"{label}: rest={atRest s}, delayed={delayed s}, fibers={s.machine.fibers.length}, cleanups={(observe s).cleanups.length}"
      if label == "cut" && atRest s then
        throw (IO.userError "the cut control does not leave an intermediate stage")
      if label == "forced-yield" && !delayed s then
        throw (IO.userError "the forced-yield control does not retain its wrapper")

#axiom_audit Effect4.Laws.Machine.ControlSteps Effect4.Laws.Program.ControlSteps

end MachineRoutes
