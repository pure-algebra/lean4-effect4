import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Machine.MaskRuns

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
  have key : old.id = id := RunMachine.id_of_fiber? found
  have split := ControlWeights.omit_sum RunFiber.id (fiberCredits q) old m.fibers unique
    (RunMachine.mem_of_fiber? found)
  have partition : (m.fibers.map (outsideFiber q id)).sum + fiberCredits q old =
      (m.fibers.map (fiberCredits q)).sum := by
    unfold outsideFiber
    simpa only [key] using split
  unfold outsideCredits machineCredits
  omega

/-- Updating the selected row cannot change the omitted projection. Consumer: evaluator and stale observer installation. -/
theorem outside_update (q : List Nat) (m : NativeMachine) (id : FiberId) (next : Fiber)
    (key : next.id = id) : outsideCredits q id (m.update next) = outsideCredits q id m := by
  have equal := ControlWeights.replace_omitted RunFiber.id (fiberCredits q) id next key m.fibers
  unfold outsideCredits RunMachine.update outsideFiber
  unfold ControlWeights.omitted at equal
  rw [equal]

/-- A non-increasing keyed replacement cannot increase off-owner credits.
Consumer: interrupt updates inside evaluator and observer accounting. -/
theorem outside_update_le (q : List Nat) (m : NativeMachine) (owner : FiberId) (old next : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (key : next.id = old.id) (credit : fiberCredits q next ≤ fiberCredits q old) :
    outsideCredits q owner (m.update next) ≤ outsideCredits q owner m := by
  have bounded := ControlWeights.replace_omitted_le RunFiber.id (fiberCredits q) owner old next key credit
    m.fibers unique (RunMachine.mem_of_fiber? found)
  unfold ControlWeights.omitted at bounded
  simp only [outsideCredits, RunMachine.update]
  unfold outsideFiber
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

/-- Installing the selected local fiber accounts for exactly one row. Consumer: actual settle assembly. -/
theorem outside_install (q : List Nat) (m : NativeMachine) (id : FiberId) (old next : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? id = some old)
    (key : next.id = id) :
    machineCredits q (m.update next) = outsideCredits q id m + fiberCredits q next := by
  have changed := update_credits q m old next unique (RunMachine.mem_of_fiber? found)
    (key.trans (RunMachine.id_of_fiber? found).symm)
  have partition := outside_split q m id old unique found
  omega

end Effect4.Program.ReleaseCustody.Control
