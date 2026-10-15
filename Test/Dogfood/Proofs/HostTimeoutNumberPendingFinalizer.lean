import Test.Dogfood.Proofs.HostTimeoutNumberProtected
import Test.Dogfood.Proofs.HostTimeoutNumberCountMachine

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual protected finalizer dispatch retains the whole pending fiber for both Timeout numeric endpoints.
Consumer: the coupled native producer at an actual counted attempt exit.
Reach: the actual selected callback, exact writer graph, entered heap, and existing live fiber.
Limit: installation into the machine, command transport, and initialized history remain separate consumers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPendingFinalizer
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow

/-- An actual installed attempt finalizer retains the full pending-fiber assertion, including immediate-interruption authority. -/
theorem installed (context : CountContext) (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (held : FiberAt machine (.pending context) fiber) (live : fiber.exit = none)
    (heap : At context.entered machine.state) (current : fiber.frame.current = Prim.ofExit exit)
    (chosen : (fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).answer = .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
        (HostTimeoutEvaluation.exitCause exit)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    FiberAt next.machine (.pending context) next.fiber := by
  obtain ⟨input, code, stack⟩ := held.frame.2
  have owned : CodeAt machine.state input (Prim.ofExit exit) := current ▸ code
  have good := HostTimeoutNumberPhaseFinalizer.exit_class machine.state input exit owned
  have fields := HostTimeoutNumberProtected.installed_fields view machine fiber yielding exit input _
    body name flag program good stack held.recorded chosen hook
  have typed := HostTimeoutNumberPhaseFinalizer.installed_hooked view HostTimeoutNumberUniform.Edge
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      HostTimeoutNumberUniform.Edge HostTimeoutNumberPhaseFinalizer.Allowed (HostTimeoutNumberUniform.family view))
    HostTimeoutNumberUniform.hook_mask machine fiber yielding exit input _ body name flag program
    owned stack held.recorded (by cases exit <;> exact chosen) (by cases exit <;> exact hook)
  constructor
  · exact ⟨HostTimeoutNumberSourceWrites.finalizer_frame context view machine fiber yielding exit current held.frame.1, typed⟩
  · intro selected published
    rw [fields.2.1, live] at published
    cases published
  · intro impossible; cases impossible
  · intro cause present
    rw [fields.2.2.1] at present
    exact held.recorded cause present
  · intro cause clean alive idle interruptible
    rw [fields.2.2.2] at interruptible
    cases interruptible
  · intro next same before installed
    cases same
    rw [fields.1] at before
    exact False.elim (HostTimeoutNumberCountMachine.counted_heap_ne context (heap.symm.trans before))

end Test.Dogfood.Proofs.HostTimeoutNumberPendingFinalizer
