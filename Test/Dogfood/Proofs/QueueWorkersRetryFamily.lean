import Test.Dogfood.Proofs.QueueWorkersRetryFlow
import Effect4.Laws.Machine.AnswerFlowRecursiveFamily

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through actual retry answers at their saved input class.
The existing recursive family consumes the classified option and retains its actual loop suffix.
No finite loop bound or arbitrary-answer replacement is used.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersRetryFamily
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- The saved name retains source and its immutable request key, without requiring a waiting phase. -/
def Loop (total token worker : Nat) (world : QueueWorkersCustodyFlow.World) : EffName → Prop
  | .loop point => QueueWorkersJobGraph.RetryAt total world token worker point
  | _ => False

/-- The actual retry callback consumes its classified option at the current world and view. -/
theorem hooks (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (owner : FiberId) (token : Nat) (view : List (FiberId × ExitV)) :
    TypedRecursiveHooks (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (.captured owner token (.takeOption token)) (Loop total token worker) (fun _ _ => False) where
  loop_future _world _nextWorld future name held := by
    cases name
    case loop point => exact QueueWorkersJobGraph.RetryAt.future held future
    all_goals exact held.elim
  iter_future _ _ _ _ held := held.elim
  loop_resume world name cursor answer held typed := by
    cases name
    case loop point =>
      have heldView := QueueWorkersJobGraph.RetryAt.view held view
      obtain ⟨shape, result⟩ := QueueWorkersRetryFlow.shape total worker member world token _ heldView
      obtain ⟨selected, classified⟩ := typed
      have paths := QueueWorkersCustody.retry_classified (Programs.queueProgram total)
        {point with completed := view} _ shape result world.requests.custody token cursor answer classified
      change RecursiveLoopResult (QueueWorkersJobGraph.model total table owner view)
        (.captured owner token (.takeOption token)) world
        (loopResumeAt (Programs.queueProgram total) {point with completed := view} cursor answer)
      rcases paths with ⟨waiting, actual⟩ | ⟨job, _holding, _value, actual⟩
      · rw [actual]
        exact QueueWorkersRetryFlow.body_entry total worker member table world owner token _ heldView ⟨selected, waiting⟩
      · rw [actual]
        exact QueueWorkersJobGraph.CodeAt.success ⟨selected, classified⟩
    all_goals exact held.elim
  iter_next _ _ _ held _ := held.elim

/-- The existing mixed saved path and the classified retry hook share their actual input and output. -/
abbrev Edge (total : Nat) (table : RowTable) (owner : FiberId) (token worker : Nat) :=
  RecursiveFamilyEdge (QueueWorkersJobFamilies.Edge total table owner)
    (.captured owner token (.takeOption token)) (Loop total token worker) (fun _ _ => False)

/-- Existing recursive-family composition supplies every saved callback and actual pushed suffix. -/
theorem family (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (owner : FiberId) (token : Nat) (view : List (FiberId × ExitV)) :
    SavedFamily (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (Edge total table owner token worker) :=
  recursive_family_of_typed (QueueWorkersJobGraph.model total table owner view)
    (interpAt (Programs.queueProgram total) view table).toPrimInterp
    (QueueWorkersJobFamilies.Edge total table owner) (.captured owner token (.takeOption token))
    (Loop total token worker) (fun _ _ => False)
    (QueueWorkersJobFamilies.family total table owner view) (hooks total worker member table owner token view)
/-- The actual retry head either enters its waiting body or returns its exact classified cursor. -/
theorem head (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (owner : FiberId) (token : Nat) (view : List (FiberId × ExitV))
    (world : QueueWorkersCustodyFlow.World) (point : Point) (cursor : Val)
    (held : QueueWorkersJobGraph.RetryAt total world token worker point)
    (typed : ValueAt world (.captured owner token (.takeOption token)) cursor) :
    HeadAt (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (Edge total table owner token worker) world (.captured owner token (.takeOption token))
      (.whileLoop (.loop point) cursor) := by
  have heldView := QueueWorkersJobGraph.RetryAt.view held view
  obtain ⟨shape, result⟩ := QueueWorkersRetryFlow.shape total worker member world token _ heldView
  have classified : QueueWorkersCustody.OptionAt world.requests.custody token cursor := typed.2
  unfold QueueWorkersCustody.OptionAt at classified
  split at classified
  next =>
    have chosen := QueueWorkersCustody.retry_waiting (Programs.queueProgram total) {point with completed := view} _ shape
    apply HeadAt.whileLoop
    · intro next body actual
      change loopNextAt (Programs.queueProgram total) {point with completed := view} .none = .continue next body at actual
      rw [chosen] at actual
      cases actual
      exact ⟨.captured owner token (.takeOption token),
        QueueWorkersRetryFlow.body_entry total worker member table world owner token _ heldView ⟨typed.1, classified⟩,
        .cons (.loop Store.Val.none held) (.nil _)⟩
    · intro body actual
      change loopNextAt (Programs.queueProgram total) {point with completed := view} .none = .finish body at actual
      rw [chosen] at actual
      cases actual
  next job =>
    have chosen := QueueWorkersCustody.retry_obtained (Programs.queueProgram total) {point with completed := view} _ shape result job
    apply HeadAt.whileLoop
    · intro next body actual
      change loopNextAt (Programs.queueProgram total) {point with completed := view} (.some (.nat job)) = .continue next body at actual
      rw [chosen] at actual
      cases actual
    · intro body actual
      change loopNextAt (Programs.queueProgram total) {point with completed := view} (.some (.nat job)) = .finish body at actual
      rw [chosen] at actual
      cases actual
      exact ⟨.captured owner token (.takeOption token), .success typed, .nil _⟩
  next => exact classified.elim
end Test.Dogfood.Proofs.QueueWorkersRetryFamily
