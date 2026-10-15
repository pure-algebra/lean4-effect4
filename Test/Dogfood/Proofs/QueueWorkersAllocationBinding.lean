import Test.Dogfood.Proofs.QueueWorkersTakeBinding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at request and retry-hint allocation.
The request allocation selects a fresh logical request and captures its actual native key.
Hint allocation preserves that request and supplies only an ignored wake key.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersAllocationBinding
open Effect4 Effect4.Machine Effect4.Program
open QueueWorkersCustodyFlow

/-- The actual worker allocator returns the key of its newly selected waiting request. -/
theorem worker_step (total : Nat) (table : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (state after : Stores) (value : Val)
    (fresh : Fresh world) (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved)
    (bound : QueueWorkersRequestKeys.Bound world.requests state)
    (unique : QueueWorkersRequestKeys.Unique world.requests)
    (actual : syncOpStep .deferredMake state = some (after, value)) :
    let next := allocate world owner ⟨state.deferreds.cells.length⟩
    Future world next ∧ Fresh next ∧ next.requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits next.requests.custody ∧
      QueueWorkersRequestKeys.Bound next.requests after ∧ QueueWorkersRequestKeys.Unique next.requests ∧
      QueueWorkersJobGraph.CodeAt total table owner next (.workerKey owner) (.success value) := by
  obtain ⟨future, newKey, counted, unused, nextBound, nextUnique⟩ :=
    allocate_native world owner state after value fresh credits bound unique actual
  exact ⟨future, unused, conserved, counted, nextBound, nextUnique,
    .success (allocate_worker_input world owner _ value newKey)⟩

/-- A retry hint does not create or replace any logical request or held occurrence. -/
theorem hint_step (total : Nat) (table : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token : Nat) (state after : Stores) (value : Val)
    (selected : Owns world owner token) (waiting : world.requests.custody.requests token = .waiting)
    (actual : syncOpStep .deferredMake state = some (after, value)) :
    QueueWorkersJobGraph.CodeAt total table owner world (.hintKey owner token) (.success value) := by
  rw [syncOpStep_deferredMake] at actual
  cases actual
  exact .success ⟨selected, waiting⟩

/-- A successful hint input contains its real wake key and the same still-waiting request. -/
theorem hint_value (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (value : Val)
    (good : ValueAt world (.hintKey owner token) value) :
    ∃ hint, value = .promise hint ∧ Owns world owner token ∧
      world.requests.custody.requests token = .waiting := by
  cases value
  case handle kind index =>
    rcases kind with _ | _ | _ | _ | kind
    · exact good.elim
    · exact good.elim
    · exact good.elim
    · exact ⟨⟨index⟩, rfl, good⟩
    · exact good.elim
  all_goals exact good.elim

/-- The actual hint binder carries the old request key and appends only its returned wake key. -/
theorem hint_callback (total : Nat) (table : RowTable) (owner : FiberId) (token index : Nat)
    (world nextWorld : QueueWorkersCustodyFlow.World) (future : Future world nextWorld)
    (point : Point) (before after : NativeEff) (view : List (FiberId × ExitV)) (value : Val)
    (request : QueueWorkersJobBinding.RequestCapture
      (Test.Dogfood.Scenario.Programs.queueProgram total) world owner index point)
    (selected : Owns world owner token)
    (found : Node.at_ (.eff (Test.Dogfood.Scenario.Programs.queueProgram total)) point.path =
      some (.eff (.bind before after)))
    (good : ValueAt nextWorld (.hintKey owner token) value) :
    (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).contA (.cont point) value =
      resolve (Test.Dogfood.Scenario.Programs.queueProgram total)
        ({point with completed := view}.childWith 1 value) ∧
      QueueWorkersJobBinding.RequestCapture (Test.Dogfood.Scenario.Programs.queueProgram total)
        nextWorld owner index ({point with completed := view}.childWith 1 value) ∧
      ∃ hint, ({point with completed := view}.childWith 1 value).env[point.env.length]? = some (.promise hint) := by
  obtain ⟨hint, rfl, nextSelected, waiting⟩ := hint_value nextWorld owner token value good
  obtain ⟨key, published, _oldWaiting, captured⟩ :=
    QueueWorkersTakeBinding.request_key total world owner token index point selected request
  have nextRequest : QueueWorkersJobBinding.RequestCapture
      (Test.Dogfood.Scenario.Programs.queueProgram total) nextWorld owner index {point with completed := view} := by
    refine ⟨request.1, token, .promise key, nextSelected, ?_, waiting, captured⟩
    exact ⟨future.1.2 token key published, by rw [waiting]; trivial⟩
  refine ⟨rfl, ?_, hint, ?_⟩
  · apply QueueWorkersJobBinding.request_bound _ _ _ _ _ 1 (.promise hint)
      (SourceScope.next_of_at _ _ (.bind before after) 1 1 found request.1 rfl) nextRequest
  · exact List.getElem?_concat_length
end Test.Dogfood.Proofs.QueueWorkersAllocationBinding
