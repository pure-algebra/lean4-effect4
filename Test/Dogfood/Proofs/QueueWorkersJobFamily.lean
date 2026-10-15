import Test.Dogfood.Proofs.QueueWorkersJobGraph
import Effect4.Laws.Machine.AnswerFlowViews

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through its actual worker success callback.
The model uses the existing uniform saved-family producer at the actual completed-fiber view.
Successful input retains its request class; unwinding a failure creates no job permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersJobGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open QueueWorkersCustodyFlow

/-- Current code and returned values read the same custody world. -/
def model (total : Nat) (table : RowTable) (owner : FiberId) (view : List (FiberId × ExitV)) :
    Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
      (ι := FiberId) (α := Ann) QueueWorkersCustodyFlow.World Kind where
  future := Future
  future_refl := order.refl
  future_trans _ _ _ := order.trans
  value := ValueAt
  cause _ _ _ := True
  code := CodeAt total table owner
  finalizer _ name exit := ((interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).finalizerProgram name exit).map
    (finalizerCode (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table) exit)
  success _ _ _ := CodeAt.success
  failure _ _ _ _ := CodeAt.failure

/-- The same saved binder retains its common endpoints through changes of completed-fiber view. -/
abbrev Semantic (total : Nat) (table : RowTable) (owner : FiberId) :=
  ViewSavedAt (model total table owner)
    (fun view => (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp)

/-- The actual classified callback is the only successful entry into the assignment continuation. -/
theorem bound_saved (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (input output : Kind) (body : NCode) (name : EffName)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt nextWorld input answer → CodeAt total table owner nextWorld output
        ((interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).contA name answer)) :
    Semantic total table owner world input output (.onSuccess body name) := by
  refine ⟨?_, ?_, ?_⟩
  · intro view
    exact saved_success (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      world input output body name
      (fun nextWorld future answer good => callback nextWorld future view answer good)
      (fun _ _ _ _ => trivial)
  · intros; intro impossible; cases impossible
  · intros; intro impossible; cases impossible

/-- Actual bind heads use the existing current-head constructor and uniform semantic family. -/
theorem bound_head (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (input output : Kind) (body : NCode) (name : EffName)
    (view : List (FiberId × ExitV)) (first : CodeAt total table owner world input body)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt nextWorld input answer → CodeAt total table owner nextWorld output
        ((interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).contA name answer)) :
    HeadAt (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      (Semantic total table owner) world output (.onSuccess body name) :=
  .onSuccess input body name first (bound_saved total table owner world input output body name callback)

/-- The existing saved-family proof owns all actual callback and unwinding cases. -/
theorem semantic_family (total : Nat) (table : RowTable) (owner : FiberId) (view : List (FiberId × ExitV)) :
    SavedFamily (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      (Semantic total table owner) :=
  ViewSavedAt.family (model total table owner)
    (fun currentView => (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) currentView table).toPrimInterp) view
end Test.Dogfood.Proofs.QueueWorkersJobGraph
