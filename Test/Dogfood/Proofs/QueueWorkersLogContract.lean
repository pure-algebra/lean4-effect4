import Test.Dogfood.Proofs.QueueWorkersWriteCensus
import Effect4.Laws.Program.CrewLogs.Initialized

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: the queue crew instantiates the shared actual cleanup-write observation.
Consumer: QueueWorkers.Assertions.logs_history through CrewLogs.history.
Reach: every source operation, initialized leading binding and acquired identity.
The initialized frame-history producer remains a separate premise.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersLogContract
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- The queue crew selects its existing three release sites and cleanup reference. -/
def crew : CrewLogs.Spec :=
  ⟨[1, 2, 3], Programs.queueAcquire, ReleaseWrites.releaseTerm, 2⟩

/-- Each actual queue operation either leaves the log or appends its captured acquisition identity. -/
theorem source_change (total : Nat) (rows : RowTable) (operation : SyncOp)
    (source : AnswerSlots.Typed.OperationSource (QueueWorkersFlow.spec total rows) operation)
    (before after : Stores) (value : Val) (actual : syncOpStep operation before = some (after, value)) :
    CrewLogs.SyncChange crew before.refs after.refs (.op operation) := by
  obtain ⟨point, row, request, requestValue, permission, found, reads, converted⟩ := source
  have checked := QueueWorkersWriteCensus.source_head total point.path _ found
  generalize envEq : point.env = env at converted
  revert converted
  fun_cases NativeOp.syncOpOf row env requestValue
  all_goals intro converted
  case case21 => cases converted
  all_goals cases converted
  case case1 => exact (QueueWorkersWriteCensus.stable_not_make total rows point request permission found).elim
  case case2 => exact .inl (by rw [syncOpStep_refGet_refs actual])
  case case3 | case4 | case5 | case7 | case9 | case10 | case11 | case13 => cases checked
  case case6 term index =>
    rw [← envEq] at actual ⊢
    by_cases selected : index = 2
    · subst index
      obtain ⟨identity, member, path, termEq, acquired⟩ :=
        QueueWorkersLogValues.update_at_log total rows point term request permission found reads
      subst term
      apply CrewLogs.update_change crew identity member point.env before after value ?_ actual
      intro old
      have length := QueueWorkersLogValues.release_length total identity member point path permission.1
      change evalTerm (point.env ++ [old]) (CrewLogs.appendTerm (identity + 7) (identity + 5)) = _
      rw [← length]
      exact CrewLogs.append_value point.env (identity + 5) identity acquired old
    · apply CrewLogs.outside_change crew _ before after value actual
      intro equal
      exact selected (by cases equal; rfl)
  case case8 term index =>
    have destination : request = .var 4 := of_decide_eq_true checked
    subst request
    change point.env[4]? = some (.cell ⟨index⟩) at reads
    rw [permission.2.1.read 4 (by change 4 < 6; decide)] at reads
    cases reads
    apply CrewLogs.outside_change crew _ before after value actual
    intro impossible
    cases impossible
  case case12 term index =>
    have destination : request = .var 0 := of_decide_eq_true checked
    subst request
    change point.env[0]? = some (.cell ⟨index⟩) at reads
    rw [permission.2.1.read 0 (by change 0 < 6; decide)] at reads
    cases reads
    apply CrewLogs.outside_change crew _ before after value actual
    intro impossible
    cases impossible
  all_goals apply CrewLogs.outside_change crew _ before after value actual
  all_goals intro impossible
  all_goals cases impossible

/-- The actual five initial values have empty native list views. -/
theorem initial_empty (index : Nat) (small : index < 5) :
    (InitialSlots.initial index).asList?.getD [] = [] := by
  rcases index with _ | _ | _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

/-- One concrete source contract supplies both membership and count debits. -/
theorem contract (total : Nat) (rows : RowTable) : CrewLogs.SyncContract crew (QueueWorkersFlow.initializedSpec total rows) where
  initial := initial_empty
  source := source_change total rows
end Test.Dogfood.Proofs.QueueWorkersLogContract
