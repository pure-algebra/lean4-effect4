import Effect4.Laws.Program.ReleaseCustody.Outside
import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Effect4.Laws.Program.ReleaseCustody.Evaluation
import Effect4.Laws.Program.PlaceLedgerConnect

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
  have omitted : ControlWeights.omitted RunFiber.id (fiberCredits q) fiber.id =
      outsideFiber q fiber.id := rfl
  have localDebit : (PlaceLedgerConnect.custody q).IterDebit before fiber it := by
    simpa only [PlaceLedger.IterDebit, PlaceLedger.spent, PlaceLedger.issued, PlaceLedger.outside,
      PlaceLedgerConnect.custody, FinalizerCredits.indicator_sum, List.map_nil, List.sum_nil,
      Nat.zero_add, Nat.add_zero, IterDebit, outsideCredits, FiberSum.outside, FiberSum.total,
      omitted, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using debit
  have balanced := (PlaceLedgerConnect.custody q).install_balanced before fiber it rest []
    unique (RunMachine.mem_of_fiber? found)
    (Nat.le_of_eq (FiberSum.install _ it.machine fiber.id old it.fiber afterUnique afterFound key)) localDebit
  exact (PlaceLedgerConnect.custody_funded q _ _).mp
    (balanced.funded _ ((PlaceLedgerConnect.custody_funded q _ _).mpr funded))

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
  apply (PlaceLedgerConnect.custody_funded q _ _).mp
  apply (PlaceLedgerConnect.custody q).settle_funded (fun _ _ => rfl) (Evaluation.interrupt_fiber_le q)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) 0 fiber.id rest it [] afterUnique
  exact (PlaceLedgerConnect.custody_funded q _ _).mpr
    (install_funded q before fiber it rest unique found afterUnique old afterFound key debit funded)

end Effect4.Program.ReleaseCustody
