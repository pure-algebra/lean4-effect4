import Test.Dogfood.Proofs.QueueWorkersCountSource
import Test.Dogfood.Proofs.QueueWorkersReadonly
import Effect4.Laws.Program.NativeRefInvariant

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at delayed admitted counter-reference replies.
The actual source update keeps the counter Nat-valued without assuming job conservation.
The initialized allocation and whole-history consumers remain explicit.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersCountCell
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- The counter is either unallocated or contains a Nat value. -/
def Holds (heap : RefHeap) : Prop := ∀ value, refPeek heap ⟨4⟩ = some value → ∃ count, value = .nat count

/-- Every actual operation outside the counter's footprint retains its value class. -/
theorem outside (operation : SyncOp) (before after : Stores) (answer : Val)
    (actual : syncOpStep operation before = some (after, answer))
    (unrelated : operation.refFootprint answer ≠ some ⟨4⟩) (held : Holds before.refs) : Holds after.refs := by
  intro value found
  rw [syncOpStep_refPeek_other actual ⟨4⟩ unrelated] at found
  exact held value found

/-- The actual successor row keeps its existing Nat counter, including a missing-cell frontier. -/
theorem counter_update (env : List Val) (before after : Stores) (answer : Val)
    (actual : syncOpStep (.refUpdateAndGet ⟨4⟩ (.app "succ" (.cons (.var env.length) .nil)) env)
      before = some (after, answer)) (held : Holds before.refs) : Holds after.refs := by
  have projected := syncOpStep_refProjection actual
  cases read : refPeek before.refs ⟨4⟩ with
  | none =>
    simp only [refStep, read, Option.bind_none] at projected
    rw [projected]
    exact held
  | some value =>
    obtain ⟨count, rfl⟩ := held value read
    simp only [refStep, read, Option.bind_some, QueueWorkersCountSource.successor, Option.map_some] at projected
    have heap := congrArg Prod.snd projected
    change refPoke before.refs ⟨4⟩ (.nat (count + 1)) = after.refs at heap
    intro value found
    rw [← heap, refPeek_poke_self before.refs ⟨4⟩ (.nat (count + 1)) (.nat count) read] at found
    cases found
    exact ⟨count + 1, rfl⟩

/-- The actual stable source census discharges the counter invariant at every native writer. -/
theorem source_keeps (total : Nat) (rows : RowTable) (operation : SyncOp)
    (source : AnswerSlots.Typed.OperationSource (QueueWorkersFlow.spec total rows) operation)
    (before after : Stores) (answer : Val) (actual : syncOpStep operation before = some (after, answer))
    (held : Holds before.refs) : Holds after.refs := by
  obtain ⟨point, row, request, requestValue, permission, found, reads, converted⟩ := source
  have checked := QueueWorkersWriteCensus.source_head total point.path _ found
  have counted := QueueWorkersCountSource.source_head total point.path _ found
  generalize envEq : point.env = env at converted
  revert converted
  fun_cases NativeOp.syncOpOf row env requestValue
  all_goals intro converted
  case case21 => cases converted
  all_goals cases converted
  case case1 => exact (QueueWorkersWriteCensus.stable_not_make total rows point request permission found).elim
  case case2 =>
    rw [syncOpStep_refGet_refs actual]
    exact held
  case case3 | case4 | case5 | case7 | case9 | case10 | case11 | case13 => cases checked
  case case6 term index =>
    by_cases selected : index = 4
    · subst index
      have excluded : request ≠ .var 4 := of_decide_eq_true counted
      have destination : WriterSource.Destination point.path request := of_decide_eq_true checked
      rcases destination with zero | one | three | four | ⟨two, _release⟩
      · subst request
        have impossible := QueueWorkersReadonly.read_index point 0 4 (by decide) permission.2.1 reads
        cases impossible
      · subst request
        have impossible := QueueWorkersReadonly.read_index point 1 4 (by decide) permission.2.1 reads
        cases impossible
      · subst request
        have impossible := QueueWorkersReadonly.read_index point 3 4 (by decide) permission.2.1 reads
        cases impossible
      · exact (excluded four).elim
      · subst request
        have impossible := QueueWorkersReadonly.read_index point 2 4 (by decide) permission.2.1 reads
        cases impossible
    · apply outside _ before after answer actual ?_ held
      intro impossible
      exact selected (by cases impossible; rfl)
  case case8 term index =>
    rw [← envEq] at actual
    obtain ⟨rfl, termEq⟩ := QueueWorkersCountSource.counter_term total point term request permission.1 found
    change point.env[4]? = some (.cell ⟨index⟩) at reads
    rw [permission.2.1.read 4 (by change 4 < 6; decide)] at reads
    cases reads
    rw [termEq] at actual
    exact counter_update point.env before after answer actual held
  case case12 term index =>
    have destination : request = .var 0 := of_decide_eq_true checked
    subst request
    change point.env[0]? = some (.cell ⟨index⟩) at reads
    rw [permission.2.1.read 0 (by change 0 < 6; decide)] at reads
    cases reads
    apply outside _ before after answer actual ?_ held
    intro impossible
    cases impossible
  all_goals apply outside _ before after answer actual ?_ held
  all_goals intro impossible
  all_goals cases impossible
end Test.Dogfood.Proofs.QueueWorkersCountCell
