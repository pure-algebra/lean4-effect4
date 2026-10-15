import Test.Dogfood.Proofs.HostTimeoutNumberCleanupJoint
import Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Consumer: the actual pending cleanup native branch for both unchanged Timeout endpoints.
The existing configuration ties the attempt's real phase to its predecessor, counted, or cleaned phase.
The uniform path supplies the same writer's owner count.
Together they admit the actual cleanup heap and reuse the existing mask-custody theorem.
This permission supplies no source leaf or initialized history by itself.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberCleanupAuthority
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutNumberPhase

/-- The actual cleanup writer cannot execute in its predecessor or already-cleaned numeric phase. -/
theorem entered (world : HostTimeoutNumberConfiguration.World) (context : CountContext) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
    (interrupted : Bool) (assigned : (fiber.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (heap : At phase machine.state)
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (phase.cleanup own interrupted)) (.attempt context.before context.entered (HostTimeoutNumberCleanupJoint.own context))
      fiber.frame.stack) : At context.entered machine.state := by
  have anchors := (HostTimeoutNumberUniform.anchors machine.state _ _ fiber.frame.stack saved).1
  change phase.count = context.entered.count at anchors
  have fields := Phase.heap_fields phase world.phase (heap.symm.trans held.heap)
  rcases held.pendingPhase fiber.id context assigned with before | counted | ⟨flag, cleaned⟩
  · rw [before] at fields
    have expected : context.entered.count = context.before.count + 1 := rfl
    have contradiction : False := by omega
    exact contradiction.elim
  · have actual := held.heap
    rw [counted] at actual
    exact actual
  · have lengths := congrArg List.length fields.2.1
    rw [cleaned] at lengths
    change phase.cleanups.length = (context.entered.cleanups ++ [_]).length at lengths
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at lengths
    have contextOwn := HostTimeoutNumberCleanupJoint.own context
    have contradiction : False := by omega
    exact contradiction.elim

/-- The same actual cleanup source return is masked and carries no deferred loop-top replacement. -/
theorem permission (world : HostTimeoutNumberConfiguration.World) (context : CountContext) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
    (interrupted : Bool) (assigned : (fiber.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (provided : FiberAt machine (.pending context) fiber)
    (heap : At phase machine.state)
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (phase.cleanup own interrupted)) (.attempt context.before context.entered (HostTimeoutNumberCleanupJoint.own context))
      fiber.frame.stack) :
    At context.entered machine.state ∧ fiber.frame.interruptible = false ∧ fiber.frame.deferredInterrupt = false := by
  have counted := entered world context machine fiber phase own interrupted assigned held heap saved
  have masked := HostTimeoutNumberMaskPermission.later_masked context machine fiber provided counted _ _ saved
    (by change 1 < 3; decide)
  exact ⟨counted, masked, provided.pendingDeferred context rfl masked⟩

end Test.Dogfood.Proofs.HostTimeoutNumberCleanupAuthority
