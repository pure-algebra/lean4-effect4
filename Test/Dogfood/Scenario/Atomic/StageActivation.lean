import Test.Dogfood.Scenario.Atomic.StageTaskAdmission
import Test.Dogfood.Scenario.Atomic.StageWaits
import Test.Dogfood.Scenario.Atomic.Initialization

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: Atomic's actual source-entry hook in the common allocation history.
The actual root row and exact initializer heap seed the active stage assertion.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Unique root ownership identifies the real initializer row without another history induction. -/
theorem pending_singleton (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (machine : NativeMachine)
    (pending : AnswerSlots.AllocationAdapter.PendingConfiguration (RootCells.atomicAdapter built accepted) fragment machine)
    (guard : Guard.GuardState machine) (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) :
    machine.fibers = [fiber] := by
  have roots := pending.root_rows (RootCells.atomicAdapter built accepted) fragment machine
  have mapped : machine.fibers.map (fun row => row.id) = List.replicate machine.fibers.length ⟨0⟩ :=
    List.map_eq_replicate_iff.mpr roots
  have unique := guard.fiberIds
  rw [mapped] at unique
  have bound := List.nodup_replicate.mp unique
  have positive := List.length_pos_iff_exists_mem.mpr ⟨fiber, member⟩
  have size : machine.fibers.length = 1 := Nat.le_antisymm bound positive
  obtain ⟨row, rows⟩ := List.length_eq_one_iff.mp size
  rw [rows] at member
  have same := List.mem_singleton.mp member
  exact rows.trans (congrArg List.singleton same.symm)

/-- Actual application entry joins the root continuation and all initial machine fields. -/
theorem entry_configuration (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (raceFree : SourceScope.RaceFreeSource built.program)
    (machine : NativeMachine)
    (pending : AnswerSlots.AllocationAdapter.PendingConfiguration (RootCells.atomicAdapter built accepted) fragment machine)
    (guard : Guard.GuardState machine) (source : SourceScope.ConfigurationAt built.program machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (running : fiber.running = true)
    (entry : AnswerSlots.AllocationAdapter.EntryAt (RootCells.atomicAdapter built accepted) fragment machine fiber) :
    Configuration built.program built.table initialWorld machine ∧ Waits machine ∧ AdmittedTasks machine := by
  have roots := pending.root_rows (RootCells.atomicAdapter built accepted) fragment machine
  have singleton := pending_singleton built accepted fragment machine pending guard fiber member
  obtain ⟨heap, frame⟩ := RootGraph.initializer_entry built accepted fragment machine fiber entry
  have identity := roots fiber member
  have cellsBound : machine.state.deferreds.cells.length ≤ 0 := pending.heap.2.2
  have cells := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero cellsBound)
  have deferreds : machine.state.deferreds = ⟨[], []⟩ := by
    cases actual : machine.state.deferreds with
    | mk stored due =>
      have storedEmpty : stored = [] := by
        have fact := cells
        rw [actual] at fact
        exact fact
      have dueEmpty : due = [] := by
        have fact := pending.deferred.1
        rw [actual] at fact
        exact fact
      rw [storedEmpty, dueEmpty]
  refine ⟨⟨heap, fresh_initial, pending.counter, ?_, ?_,
    SourceScope.Opportunities.races_nil built.program machine raceFree source, deferreds⟩, ?_,
    AdmittedTasks.of_pending machine roots pending.replies⟩
  · intro row inside
    rw [singleton] at inside
    have same := List.mem_singleton.mp inside
    subst row
    exact .inl (.root identity frame)
  · intro row inside
    constructor
    · intro owner request same
      have impossible : owner + 1 = 0 := congrArg FiberId.value (same.symm.trans (roots row inside))
      exact False.elim (Nat.noConfusion impossible)
    · intro owner request same
      have impossible : owner + 1 = 0 := congrArg FiberId.value (same.symm.trans (roots row inside))
      exact False.elim (Nat.noConfusion impossible)
    · exact fun _ => pending.childless row inside
    · intro observer observed
      rw [pending.unobserved row inside] at observed
      cases observed
  · intro row inside parked
    have idle := guard.parkedIdle row inside parked
    rw [singleton] at inside
    have same := List.mem_singleton.mp inside
    subst row
    exact False.elim (Bool.noConfusion (idle.symm.trans running))

end Test.Dogfood.Scenario.Atomic.StageConfiguration
