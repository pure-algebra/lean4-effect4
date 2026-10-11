import Effect4.Laws.Program.ReleaseCustody.Outside
import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Effect4.Laws.Program.ReleaseCustody.Evaluation
import Effect4.Laws.Machine.FiberSumMessages

/-!
Concept: scope-lifetime-finalization, R11.
Question: local evaluator debit feeds Execution.history and the original Workers release bound.
Reach: actual iteration records and actual selected lookups with unique fiber identities.
Limit: assembly consumes evaluator debit; it does not assume or establish that debit universally.
Unlock: settle installs the returned owner exactly once across every outcome.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody
open Effect4 Effect4.Machine Effect4.Program
open Control RuntimeShape

/-- Account for the local returned fiber separately from its old stored owner row. -/
def IterDebit (q : List Nat) (before : NativeMachine) (fiber : RuntimeShape.Fiber)
    (it : Iteration) : Prop :=
  it.machine.trace.countP (ReleaseTrace.releaseAt q) + outsideCredits q fiber.id it.machine +
    fiberCredits q it.fiber + (it.nested.map (commandCredits q)).sum +
    before.trace.countP (ReleaseTrace.registeredAt q) ≤
  before.trace.countP (ReleaseTrace.releaseAt q) + outsideCredits q fiber.id before +
    fiberCredits q fiber + it.machine.trace.countP (ReleaseTrace.registeredAt q)

/-- Actual installation connects the local debit to the whole machine and queued suffix.
Consumer: settle_funded, then the native loop and deliver command clauses. -/
theorem install_funded (q : List Nat) (before : NativeMachine) (fiber : RuntimeShape.Fiber)
    (it : Iteration) (rest : List Control.Command)
    (unique : (before.fibers.map RunFiber.id).Nodup) (found : before.fiber? fiber.id = some fiber)
    (afterUnique : (it.machine.fibers.map RunFiber.id).Nodup)
    (old : RuntimeShape.Fiber) (afterFound : it.machine.fiber? fiber.id = some old)
    (key : it.fiber.id = fiber.id) (debit : IterDebit q before fiber it)
    (funded : Funded q before rest) :
    Funded q (it.machine.update it.fiber) (it.nested ++ rest) := by
  have first := outside_split q before fiber.id fiber unique found
  have last := outside_install q it.machine fiber.id old it.fiber afterUnique afterFound key
  unfold IterDebit at debit
  unfold Funded at funded ⊢
  change it.machine.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (it.machine.update it.fiber) +
      ((it.nested ++ rest).map (commandCredits q)).sum ≤ it.machine.trace.countP (ReleaseTrace.registeredAt q)
  rw [last, List.map_append, List.sum_append]
  omega

/-- Every actual scheduler outcome uses the same single-owner installation debit.
Consumer: whole native loop and deliver command funding in Execution.history. -/
theorem settle_funded (q : List Nat) (before : NativeMachine) (fiber : RuntimeShape.Fiber)
    (it : Iteration) (rest : List Control.Command)
    (unique : (before.fibers.map RunFiber.id).Nodup) (found : before.fiber? fiber.id = some fiber)
    (afterUnique : (it.machine.fibers.map RunFiber.id).Nodup)
    (old : RuntimeShape.Fiber) (afterFound : it.machine.fiber? fiber.id = some old)
    (key : it.fiber.id = fiber.id) (debit : IterDebit q before fiber it)
    (funded : Funded q before rest) :
    Funded q (settle fiber.id rest it).1 (settle fiber.id rest it).2 := by
  have installed := install_funded q before fiber it rest unique found afterUnique old afterFound key debit funded
  have fibers := FiberSum.settle_le (fiberCredits q) (fun _ _ => rfl)
    (Evaluation.interrupt_fiber_le q) (fun _ => rfl) (fun _ => rfl) fiber.id rest it afterUnique
  have fields := FiberSum.settle_fields fiber.id rest it
  have state := congrArg Prod.fst fields
  have races := congrArg (fun fields => fields.2.1) fields
  have trace := congrArg (fun fields => fields.2.2) fields
  have commands := FiberSum.settle_commands_le (commandCredits q)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fiber.id rest it
  unfold Funded machineCredits at installed ⊢
  change ((settle fiber.id rest it).1.fibers.map (fiberCredits q)).sum ≤
    ((it.machine.update it.fiber).fibers.map (fiberCredits q)).sum at fibers
  dsimp only at state races trace
  rw [state, races, trace]
  dsimp only [RunMachine.update] at installed fibers
  omega

end Effect4.Program.ReleaseCustody
