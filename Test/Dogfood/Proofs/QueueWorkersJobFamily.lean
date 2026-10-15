import Test.Dogfood.Proofs.QueueWorkersJobGraph
import Effect4.Laws.Machine.AnswerFlowViews
import Effect4.Laws.Machine.AnswerFlowProtected

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

/-- The real mask-restoration frame retains the same classified input at every completed-fiber view. -/
theorem mask_saved (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (kind : Kind) (flag : Bool) :
    Semantic total table owner world kind kind (.setInterruptible flag) := by
  refine ⟨?_, ?_, ?_⟩
  · intro view
    exact saved_mask (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp world kind flag
  · intros; intro impossible; cases impossible
  · intros; intro impossible; cases impossible

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

/-- Cleanup success restores its captured body exit under that exit's actual input permission. -/
theorem restoring_saved (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (option : Val) (exit : ExitV) (body : NCode) :
    Semantic total table owner world (.restoreSnapshot owner token option exit)
      (.snapshot owner token option) (.onSuccess body (.restore exit)) := by
  apply bound_saved
  intro nextWorld future view answer good
  change CodeAt total table owner nextWorld (.snapshot owner token option)
    (contAOf (Test.Dogfood.Scenario.Programs.queueProgram total) (.restore exit) answer)
  rw [Agreement.contAOf_restore]
  cases exit with
  | success value => exact .success good
  | failure cause => exact .failure

/-- The installed cleanup's failure arm returns a failure and creates no successful job input. -/
theorem merging_saved (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (kind : Kind) (exit : ExitV) (body : NCode) :
    Semantic total table owner world kind kind (.onFailure body (.merge exit)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply saved_failure (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      world kind kind body (.merge exit)
    · intro _ _ _ good
      exact good
    · intro nextWorld _ cause _
      change CodeAt total table owner nextWorld kind
        (contEOf (Test.Dogfood.Scenario.Programs.queueProgram total) (.merge exit) cause)
      rw [Agreement.contEOf_merge]
      cases exit with
      | success value => exact .failure
      | failure original => exact .failure
    · intros
      trivial
  · intros; intro impossible; cases impossible
  · intros; intro impossible; cases impossible

/-- The installed restore head keeps the captured body exit and actual older suffix. -/
theorem restoring_head (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (option : Val) (exit : ExitV) (body : NCode)
    (view : List (FiberId × ExitV))
    (first : CodeAt total table owner world (.restoreSnapshot owner token option exit) body) :
    HeadAt (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      (Semantic total table owner) world (.snapshot owner token option) (.onSuccess body (.restore exit)) := by
  refine HeadAt.onSuccess (Kind.restoreSnapshot owner token option exit) body (.restore exit) ?_ ?_
  · exact first
  · exact restoring_saved total table owner world token option exit body

/-- The actual failure-merging head shares its input class with its successful cleanup result. -/
theorem merging_head (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (kind : Kind) (exit : ExitV) (body : NCode)
    (view : List (FiberId × ExitV)) (first : CodeAt total table owner world kind body) :
    HeadAt (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      (Semantic total table owner) world kind (.onFailure body (.merge exit)) :=
  .onFailure kind body (.merge exit) first (merging_saved total table owner world kind exit body)

/-- The actual installed finalizer wrapper preserves its body's captured result permission. -/
theorem finalizer_code (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (option : Val) (exit : ExitV) (body : NCode)
    (view : List (FiberId × ExitV))
    (first : CodeAt total table owner world (.restoreSnapshot owner token option exit) body) :
    CodeAt total table owner world (.snapshot owner token option)
      (finalizerCode (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table) exit body) := by
  cases exit with
  | success value => exact .restoring first
  | failure cause => exact .restoring (.merging first)

/-- The actual protected wait finalizer retains the captured body exit at installation. -/
theorem protected_saved (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (option : Val) (body : NCode) (point : Point)
    (installed : ∀ nextWorld, Future world nextWorld → ∀ view exit,
      (match exit with
        | .success value => ValueAt nextWorld (.snapshot owner token option) value
        | .failure _ => True) →
      CodeAt total table owner nextWorld (.restoreSnapshot owner token option exit)
        (resolve (Test.Dogfood.Scenario.Programs.queueProgram total)
          ({point with completed := view}.childWith 1 (reifyExitVal exit)))) :
    Semantic total table owner world (.snapshot owner token option) (.snapshot owner token option)
      (.onExit body (.fin point) false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply saved_protected_finalizer (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      world (.snapshot owner token option) (.snapshot owner token option) body (.fin point)
    intro nextWorld future exit good
    cases exit with
    | success value =>
      exact ⟨_, rfl, finalizer_code total table owner nextWorld token option (.success value) _ view
        (installed nextWorld future view (.success value) good)⟩
    | failure cause =>
      exact ⟨_, rfl, finalizer_code total table owner nextWorld token option (.failure cause) _ view
        (installed nextWorld future view (.failure cause) True.intro)⟩
  · intros; intro impossible; cases impossible
  · intros; intro impossible; cases impossible

/-- The existing saved-family proof owns all actual callback and unwinding cases. -/
theorem semantic_family (total : Nat) (table : RowTable) (owner : FiberId) (view : List (FiberId × ExitV)) :
    SavedFamily (model total table owner view)
      (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) view table).toPrimInterp
      (Semantic total table owner) :=
  ViewSavedAt.family (model total table owner)
    (fun currentView => (interpAt (Test.Dogfood.Scenario.Programs.queueProgram total) currentView table).toPrimInterp) view
end Test.Dogfood.Proofs.QueueWorkersJobGraph
