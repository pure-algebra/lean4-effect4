import Effect4.Laws.Program.ReleaseCustody.Sequencing
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

/-!
Reader: actual native yield/resume commands at the Workers acquisition identity.
Control: equality at one parked response fails to justify interruption stability.
The control is an artificial stack, not an admitted application history.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.SequencingControl
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

def fin : FinName := .foreign {
  path := Test.Dogfood.Scenario.Programs.crewAcquire 1
  env := []
  fuel := 1
  tape := []
  ctx := emptyCtx}
def frames : List NCode := [.onSuccess (.sync (.op (.scopeAdd 0 fin))) (.afterScopeAdd .unit fin)]
def closed : Val := reifyExitVal (.success .unit)

-- The weaker equality admits this artificial parked response and loses it on interruption.
#guard stackCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) (.success closed) frames ==
  stackCap (Test.Dogfood.Scenario.Programs.crewAcquire 1) frames
#guard stackCap (Test.Dogfood.Scenario.Programs.crewAcquire 1) frames == 1
#guard stackCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) (.failure (.die Defect.badName)) frames == 0

example : Kept (.success closed) frames :=
  .add _ 0 .unit fin [] noAdd_empty (.value closed)

example : ¬ StableFrames frames := by
  intro held
  cases held
  case clean missing => exact missing _ List.mem_cons_self _ _ _ rfl

-- The actual native acquired callback supplies the precise body/callback correlation.
example (b : Api.Built) (point : Point) (ctx : Ctx) (scope : Nat) (value : Val) :
    contAOf b.program (.acquired point ctx scope) value =
      .onSuccess (.sync (.op (.scopeAdd scope (.foreign (point.capture value ctx)))))
        (.afterScopeAdd value (.foreign (point.capture value ctx))) :=
  acquired_registration b.program point ctx scope value

-- The actual yield park retains stability, including injected saved-yield constants.
example (b : Api.Built) (m : NativeMachine) (fiber : Fiber) (yielding : Bool) (priority : Nat)
    (held : Kept (.yieldNowWith priority) fiber.frame.stack) :
    let next := (FiberAction.yieldNow (interpOf b.program b.table) m fiber yielding priority).fiber
    StableFrames next.frame.stack ∧ Kept next.frame.current next.frame.stack :=
  yield_producer b.program b.table m fiber yielding priority held

-- The actual matched resume command consumes its queued credit and actual trace event.
example (b : Api.Built) (m : NativeMachine) (id : FiberId) (token : Nat) (answer : NCode)
    (rest : List Command) (fiber : Fiber) (found : m.fiber? id = some fiber)
    (parked : fiber.parked = .withGuard token) (unique : (m.fibers.map RunFiber.id).Nodup)
    (stable : StableFrames fiber.frame.stack)
    (funded : Funded (Test.Dogfood.Scenario.Programs.crewAcquire 1) m (.resume id token answer :: rest)) :
    Funded (Test.Dogfood.Scenario.Programs.crewAcquire 1)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.resume id token answer) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.resume id token answer) rest).2 :=
  resume_command b.program b.table _ m id token answer rest fiber found parked unique stable funded

end Effect4.Program.ReleaseCustody.SequencingControl

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Sequencing
