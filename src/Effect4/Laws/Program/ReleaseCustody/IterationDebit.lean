import Effect4.Laws.Program.ReleaseCustody.Outside
import Effect4.Laws.Program.ReleaseCustody.RuntimeShape

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
  have modified (next : RuntimeShape.Fiber) (sameKey : next.id = fiber.id)
      (sameCredit : fiberCredits q next = fiberCredits q it.fiber) :
      Funded q (it.machine.update next) (it.nested ++ rest) := by
    have credit := outside_install q it.machine fiber.id old next afterUnique afterFound sameKey
    have original := outside_install q it.machine fiber.id old it.fiber afterUnique afterFound key
    unfold Funded at installed ⊢
    change it.machine.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (it.machine.update next) +
      ((it.nested ++ rest).map (commandCredits q)).sum ≤ it.machine.trace.countP (ReleaseTrace.registeredAt q)
    rw [credit, sameCredit, ← original]
    exact installed
  cases outcome : it.outcome <;> simp only [settle, outcome]
  case continue_ | answered | finished =>
    unfold Funded at installed ⊢
    simpa only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      commandCredits, Nat.add_zero] using installed
  case commands => exact installed
  case parked =>
    split
    · have held := modified {it.fiber with parked := .notParked, pending := []} key rfl
      unfold Funded at held ⊢
      simpa only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
        commandCredits, Nat.add_zero] using held
    · exact modified {it.fiber with running := false} key rfl
  case stuck why =>
    have held := modified {it.fiber with running := false} key rfl
    unfold Funded at held ⊢
    change it.machine.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (it.machine.update {it.fiber with running := false}) +
      ((it.nested ++ rest).map (commandCredits q)).sum ≤ it.machine.trace.countP (ReleaseTrace.registeredAt q) at held
    change it.machine.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (it.machine.update {it.fiber with running := false}) +
      (List.map (commandCredits q) []).sum ≤ it.machine.trace.countP (ReleaseTrace.registeredAt q)
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_trans (Nat.le_add_right _ _) held

end Effect4.Program.ReleaseCustody
