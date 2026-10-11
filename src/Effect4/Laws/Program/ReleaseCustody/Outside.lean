import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Machine.FiberSum

/-!
Concept: scope-lifetime-finalization, R11.
Question: evaluator and observer debit serve Execution.history and Workers.Assertions.releases_step.
Reach: actual keyed fiber updates, distinct fiber identities and an actual selected lookup.
Limit: the projection establishes no command or history closure alone.
Unlock: count the installed local fiber once, even when nested interrupts update its stored row.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Control
open Effect4 Effect4.Machine Effect4.Program

/-- Ignore the selected owner's stored row while its local fiber is being evaluated. -/
def outsideFiber (q : List Nat) (owner : FiberId) (fiber : Fiber) : Nat :=
  if fiber.id = owner then 0 else fiberCredits q fiber

def outsideCredits (q : List Nat) (owner : FiberId) (m : NativeMachine) : Nat :=
  (m.state.scopes.entries.map fun e => scopeCredits q e.scope).sum +
    (m.fibers.map (outsideFiber q owner)).sum +
    (m.races.map fun r => (r.programs.map (currentCredits q)).sum).sum

/-- The selected lookup restores exactly the omitted owner's credit. Consumer: settle debit. -/
theorem outside_split (q : List Nat) (m : NativeMachine) (id : FiberId) (old : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? id = some old) :
    outsideCredits q id m + fiberCredits q old = machineCredits q m := by
  have partition := FiberSum.split_found (fiberCredits q) m id old unique found
  simp only [FiberSum.atFiber, found, Option.map_some, Option.getD_some] at partition
  change (m.fibers.map (outsideFiber q id)).sum + fiberCredits q old =
    (m.fibers.map (fiberCredits q)).sum at partition
  unfold outsideCredits machineCredits
  omega

/-- Updating the selected row cannot change the omitted projection. Consumer: evaluator and stale observer installation. -/
theorem outside_update (q : List Nat) (m : NativeMachine) (id : FiberId) (next : Fiber)
    (key : next.id = id) : outsideCredits q id (m.update next) = outsideCredits q id m := by
  exact congrArg (fun total => (m.state.scopes.entries.map fun e => scopeCredits q e.scope).sum +
    total + (m.races.map fun r => (r.programs.map (currentCredits q)).sum).sum)
    (FiberSum.outside_update (fiberCredits q) m id next key)

/-- A non-increasing keyed replacement cannot increase off-owner credits.
Consumer: interrupt updates inside evaluator and observer accounting. -/
theorem outside_update_le (q : List Nat) (m : NativeMachine) (owner : FiberId) (old next : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (key : next.id = old.id) (credit : fiberCredits q next ≤ fiberCredits q old) :
    outsideCredits q owner (m.update next) ≤ outsideCredits q owner m := by
  have bounded := FiberSum.outside_update_le (fiberCredits q) m owner old next unique found key credit
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

/-- Installing the selected local fiber accounts for exactly one row. Consumer: actual settle assembly. -/
theorem outside_install (q : List Nat) (m : NativeMachine) (id : FiberId) (old next : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? id = some old)
    (key : next.id = id) :
    machineCredits q (m.update next) = outsideCredits q id m + fiberCredits q next := by
  have installed := FiberSum.install (fiberCredits q) m id old next unique found key
  change ((m.update next).fibers.map (fiberCredits q)).sum =
    (m.fibers.map (outsideFiber q id)).sum + fiberCredits q next at installed
  unfold machineCredits outsideCredits
  rw [installed]
  dsimp only [RunMachine.update]
  omega

end Effect4.Program.ReleaseCustody.Control
