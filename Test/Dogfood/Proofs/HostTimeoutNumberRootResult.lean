import Test.Dogfood.Proofs.HostTimeoutNumberRootModel
import Test.Dogfood.Proofs.HostTimeoutNumberFormFamily

/-!
Concept: translation-simulation R10 with scope-lifetime-finalization R11.
Question: delivered typed-failure provenance still yields the exact declared selected retry.
Consumer: the declared-prefix component of Timeout.retries_declared.
Reach: the actual source catch test and a plain selected singleton failure.
Limit: the initialized producer must supply that selected exit and its provenance.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootResult
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutNumberPhaseFlow HostTimeoutNumberPhase HostTimeoutNumberLedger

/-- A delivered represented error has the selected singleton failure's exact payload. -/
theorem singleton_error (tag message : String) (annotations : ReasonAnnotations Ann)
    (cause : CauseV) (value : Val)
    (origin : TypedFrom (.failure {reasons := [.fail (.tagged tag message) annotations]}) cause)
    (first : firstErrorValue? cause = some value) : value = .list [.str tag, .str message] := by
  obtain ⟨error, selected, decoded⟩ := Option.bind_eq_some_iff.mp first
  obtain ⟨reason, member, actual⟩ := List.exists_of_findSome?_eq_some selected
  cases reason with
  | die defect stored => cases actual
  | interrupt fiber stored => cases actual
  | fail failure stored =>
      have source := origin (.fail failure stored) member rfl
      have equal : Reason.fail failure stored = Reason.fail (.tagged tag message) annotations :=
        List.mem_singleton.mp source
      have errorEqual : failure = .tagged tag message := Option.some.inj (congrArg Reason.error? equal)
      have chosen : failure = error := Option.some.inj actual
      rw [← chosen, errorEqual] at decoded
      exact (Option.some.inj decoded).symm

/-- The actual catch selection has a represented first failure before it can test the retry predicate. -/
theorem handled_first (env : List Val) (test : Term) (cause : CauseV) (value : Val)
    (handled : caughtErrorValue? env test cause = some value) : firstErrorValue? cause = some value := by
  unfold caughtErrorValue? at handled
  obtain ⟨first, selected, accepted⟩ := Option.bind_eq_some_iff.mp handled
  split at accepted
  · have equal := Option.some.inj accepted
    rw [← equal]
    exact selected
  · cases accepted

/-- The exact declared retry follows from the selected singleton even after actual cause combination. -/
theorem caught_declared (n : Fin 4) (delay : Nat) (previous : Val)
    (tag message : String) (annotations : ReasonAnnotations Ann) (cause : CauseV) (value : Val)
    (origin : TypedFrom (.failure {reasons := [.fail (.tagged tag message) annotations]}) cause)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest cause = some value) :
    HostTimeoutNumberLedger.exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  have selected := handled_first _ _ cause value handled
  have valueEqual := singleton_error tag message annotations cause value origin selected
  have singleton : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest {reasons := [.fail (.tagged tag message) annotations]} = some value := by
    unfold caughtErrorValue? at handled ⊢
    have firstSingleton : firstErrorValue? {reasons := [.fail (.tagged tag message) annotations]} =
        some (.list [.str tag, .str message]) := rfl
    rw [selected] at handled
    rw [firstSingleton]
    simpa only [valueEqual] using handled
  exact HostTimeoutNumberFormFamily.caught_singleton_declared n delay previous tag message annotations value singleton

/-- The actual completed-form heap identifies its selected exit without a completed-cleanup count assumption. -/
theorem selected_unique (phase : Phase) (first second : ExitV)
    (heap : (phase.form phase.count first).heap = (phase.form phase.count second).heap) : first = second := by
  have cells := congrArg (fun (refs : RefHeap) => refs[2]?) heap
  change some (Val.list (phase.form phase.count first).completed) =
    some (Val.list (phase.form phase.count second).completed) at cells
  have logs := congrArg Store.Val.children (Option.some.inj cells)
  change (phase.form phase.count first).completed = (phase.form phase.count second).completed at logs
  have firstDecoded := form_exits (phase.form phase.count first).formsAt
  have secondDecoded := form_exits (phase.form phase.count second).formsAt
  have decoded := firstDecoded.symm.trans ((congrArg (List.filterMap entryExit) logs).trans secondDecoded)
  change phase.exits ++ [first] = phase.exits ++ [second] at decoded
  exact (List.cons.inj (List.append_cancel_left decoded)).1

/-- The root cause class and actual published singleton jointly give its exact declared retry. -/
theorem published_caught_declared (state : Stores) (phase : Phase) (n : Fin 4) (delay : Nat) (previous : Val)
    (tag message : String) (annotations : ReasonAnnotations Ann) (cause : CauseV) (value : Val)
    (good : HostTimeoutNumberPhaseFlow.CauseAt state (.published phase) cause)
    (published : HostTimeoutNumberPhaseFlow.At (phase.form phase.count (.failure {reasons := [.fail (.tagged tag message) annotations]})) state)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest cause = some value) :
    exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  obtain ⟨selected, heap, origin⟩ := good
  have equal := selected_unique phase selected (.failure {reasons := [.fail (.tagged tag message) annotations]})
    (heap.symm.trans published)
  rw [equal] at origin
  exact caught_declared n delay previous tag message annotations cause value origin handled

end Test.Dogfood.Proofs.HostTimeoutNumberRootResult
