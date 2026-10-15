import Test.Dogfood.Proofs.QueueWorkersTakeFlow
import Test.Dogfood.Proofs.QueueWorkersAllocationBinding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual classified retry body.
The authored hint binder preserves the immutable request key and consumes its actual new hint.
A completed cursor retains its exact held job through the existing retry hook.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersRetryFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The actual hint allocation binds its returned key into the complete take attempt. -/
theorem hint_body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (point : Point)
    (request : QueueWorkersJobBinding.RequestCapture (Programs.queueProgram total) world owner (worker + 8) point)
    (selected : Owns world owner token)
    (path : point.path = QueueWorkersRetrySites.path worker ++ [0])
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersRetrySites.body_source total worker member
  rw [← path] at found
  have depth : point.env.length = worker + 10 := by
    have level := request.1
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [path, QueueWorkersRetrySites.body_level total worker member] at level
    exact (Option.some.inj level).symm
  obtain ⟨_key, _published, waiting, _captured⟩ :=
    QueueWorkersTakeBinding.request_key total world owner token (worker + 8) point selected request
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .hintKey owner token) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        exact .hintMake selected waiting
    · intro nextWorld future view answer good
      obtain ⟨actual, nextRequest, nextHint⟩ := QueueWorkersAllocationBinding.hint_callback total table owner token
        (worker + 8) world nextWorld future point _ _ view answer request selected found good
      obtain ⟨_hint, _value, nextSelected, _nextWaiting⟩ :=
        QueueWorkersAllocationBinding.hint_value nextWorld owner token answer good
      rw [actual]
      apply QueueWorkersTakeFlow.attempt total worker member table nextWorld owner token _ nextRequest nextSelected
      · change point.path ++ [1] = QueueWorkersTakeFlow.attemptPath worker
        rw [path]
        simpa only [QueueWorkersTakeFlow.attemptPath, List.append_assoc, List.cons_append, List.nil_append] using
          QueueWorkersRetrySites.attempt_path worker member
      · exact leading.append [answer]
      · simpa only [depth] using nextHint
/-- The saved retry reads its authored cursor positions under its actual captured environment length. -/
theorem shape (total worker : Nat) (member : worker ∈ [1, 2])
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point)
    (held : QueueWorkersJobGraph.RetryAt total world token worker point) :
    loopAt (Programs.queueProgram total) point =
      some (QueueWorkersCustody.retryTest point.env.length, .var (point.env.length + 1),
        QueueWorkersTakeTailSites.body (QueueWorkersRetrySites.path worker ++ [0])) ∧
      loopResultAt (Programs.queueProgram total) point = some (.var point.env.length) := by
  have depth : point.env.length = worker + 9 := by
    have level := held.source
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [held.path, QueueWorkersRetrySites.level total worker member] at level
    exact (Option.some.inj level).symm
  unfold loopAt loopResultAt
  rw [held.path, QueueWorkersRetrySites.source total worker member, depth]
  exact ⟨rfl, rfl⟩

/-- An actual waiting cursor enters the hint binder with its same captured request. -/
theorem body_entry (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (point : Point)
    (held : QueueWorkersJobGraph.RetryAt total world token worker point)
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) (point.childWith 0 .none)) := by
  have found := QueueWorkersRetrySites.source total worker member
  rw [← held.path] at found
  have depth : point.env.length = worker + 9 := by
    have level := held.source
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [held.path, QueueWorkersRetrySites.level total worker member] at level
    exact (Option.some.inj level).symm
  obtain ⟨nativeKey, published, captured⟩ := held.key
  refine hint_body total worker member table world owner token _ ?_ phase.1 ?_ (held.leading.append [.none])
  · refine ⟨SourceScope.childWith_at _ _ 0 _ (SourceScope.next_of_at _ _ _ 0 1 found held.source rfl),
      token, .promise nativeKey, phase.1, ?_, phase.2, ?_⟩
    · constructor
      · exact published
      · rw [phase.2]
        trivial
    · exact (List.getElem?_append_left (by change worker + 8 < point.env.length; omega)).trans captured
  · change point.path ++ [0] = QueueWorkersRetrySites.path worker ++ [0]
    rw [held.path]
/-- The actual source suspension starts the retry at its classified empty cursor. -/
theorem loop_entry (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (point : Point)
    (held : QueueWorkersJobGraph.RetryAt total world token worker point)
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersRetrySites.source total worker member
  rw [← held.path] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_iterate _ _ _ _ _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.suspended
    intro view
    change QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (suspendBodyAt (Programs.queueProgram total) (.body {point with completed := view}))
    simp only [suspendBodyAt, fuel, found, evalTerm, evalTerms]
    exact .retry member ⟨held.source, held.path, held.leading, held.key⟩ phase
end Test.Dogfood.Proofs.QueueWorkersRetryFlow
