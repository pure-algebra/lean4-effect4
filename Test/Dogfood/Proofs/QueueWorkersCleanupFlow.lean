import Test.Dogfood.Proofs.QueueWorkersJobFamilies
import Test.Dogfood.Proofs.QueueWorkersWaitSites

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through its actual protected waiting cleanup.
The actual withdrawal and notification tail retain the captured body exit together.
A failed body supplies no waiting or successful job permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCleanupFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The cleanup discards notification values and keeps only its captured exit permission. -/
theorem flat (owner : FiberId) (token : Nat) (option : Val) (exit : ExitV) :
    ∀ world value, ValueAt world (.restoreSnapshot owner token option exit) value ↔
      ValueAt world (.restoreSnapshot owner token option exit) .unit := by
  intro world value
  cases exit <;> rfl

/-- The actual interrupted-wait branch executes withdrawal before its certified notification tail. -/
theorem withdraw_body (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (world : QueueWorkersCustodyFlow.World)
    (token : Nat) (option : Val) (exit : ExitV) (point : Point)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWaitSites.path worker ++ [0, 1, 0])
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : ValueAt world (.restoreSnapshot owner token option exit) .unit) :
    QueueWorkersJobGraph.CodeAt total table owner world (.restoreSnapshot owner token option exit)
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersWaitSites.withdraw_source total worker member
  rw [← path] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ available =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .restoreSnapshot owner token option exit) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        have slot : evalTerm (point.child 0).env (.var 0) = some (.cell ⟨0⟩) := leading.read 0 (by decide)
        rw [slot]
        apply QueueWorkersJobGraph.CodeAt.withdraw member
          (SourceScope.child_at _ point 0 (SourceScope.next_of_at _ _ _ 0 0 found source rfl)) leading
        · change point.path ++ [0] = QueueWorkersWithdrawalSites.path worker
          rw [path]
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            QueueWorkersWaitSites.withdraw_path worker member
        · exact key
        · exact phase
    · intro nextWorld future view answer good
      let spec := QueueWorkersNotificationFlow.specification total
        (QueueWorkersWaitSites.path worker ++ [0, 1, 0, 1])
        (QueueWorkersWaitSites.notification_member total worker member)
      change QueueWorkersJobGraph.CodeAt total table owner nextWorld (.restoreSnapshot owner token option exit)
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 answer))
      apply QueueWorkersJobGraph.CodeAt.notification spec (flat owner token option exit)
        ((flat owner token option exit nextWorld answer).mp good)
      apply QueueWorkersNotificationFlow.resolve_at spec point.env
      constructor
      · change (QueueWorkersWaitSites.path worker ++ [0, 1, 0, 1]).IsPrefix (point.path ++ [1])
        simp only [path, List.append_assoc, List.cons_append, List.nil_append]
        exact List.prefix_refl _
      · exact (show AnswerSlots.Prefix point.env point.env from List.take_length).append [answer]
end Test.Dogfood.Proofs.QueueWorkersCleanupFlow
