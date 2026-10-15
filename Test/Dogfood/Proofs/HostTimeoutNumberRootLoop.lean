import Test.Dogfood.Proofs.HostTimeoutNumberRootSuffix
import Test.Dogfood.Proofs.HostTimeoutNumberLoop
import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concepts: translation-simulation R10 and scope-lifetime-finalization R11.
Question: the actual returned retry creates the next attempt's numeric permissions.
Consumer: the root loop outcome of the coupled Timeout command producer.
Reach: the actual loop callback, selected singleton publication, and completed cleanup barrier.
Limit: the actual command producer must supply these facts at the selected loop frame.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootLoop
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhase HostTimeoutNumberRootModel HostTimeoutNumberConfiguration

/-- The actual published failure identifies the returned retry's failure encoding. -/
theorem failure_value (state : Stores) (phase : Phase) (n : Fin 4) (delay : Nat) (previous value : Val)
    (cause : CauseV) (good : RetryValue state phase n delay previous value)
    (published : HostTimeoutNumberPhaseFlow.At (phase.form phase.count (.failure cause)) state) :
    ∃ error, value = .list [.none, .some error] := by
  obtain ⟨selected, heap, success | ⟨delivered, error, origin, handled, encoded⟩⟩ := good
  · have equal := HostTimeoutNumberRootResult.selected_unique phase selected (.failure cause)
      (heap.symm.trans published)
    obtain ⟨body, returned, encoded⟩ := success
    rw [equal] at returned
    cases returned
  · exact ⟨error, encoded⟩

/-- A completed source retry supplies all permissions for the next concrete attempt context. -/
def nextContext (phase : Phase) (selected : ExitV) (n : Fin 4)
    (cleanups : phase.cleanups.length = phase.count) (cursor : phase.count ≤ n.val + 1)
    (next : n.val + 1 < 4) (captured : Point) (fuel delay : Nat) (error : Val) : CountContext where
  before := phase.form phase.count selected
  n := ⟨n.val + 1, next⟩
  cleanups := cleanups
  forms := by
    change phase.count ≤ (phase.exits ++ [selected]).length
    have upper := phase.formUpper
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  cursor := cursor
  captured := captured
  fuel := fuel
  delay := if 0 < n.val then delay * 2 else delay
  previous := .some error

/-- The actual loop continuation joins exact source control, declared predecessors, and next-count permissions. -/
theorem failure_continue (state : Stores) (phase : Phase) (n : Fin 4) (delay fuel : Nat)
    (previous value : Val) (captured point : Point)
    (tag message : String) (annotations : ReasonAnnotations Ann)
    (good : RetryValue state phase n delay previous value)
    (published : HostTimeoutNumberPhaseFlow.At
      (phase.form phase.count (.failure {reasons := [.fail (.tagged tag message) annotations]})) state)
    (cleanups : phase.cleanups.length = phase.count) (cursor : phase.count ≤ n.val + 1)
    (prior : phase.exits.all HostTimeoutNumberLedger.exitRetries = true)
    (next : n.val + 1 < 4)
    (slots : HostTimeoutSlots.EnvAt [] point.path point.env) (path : point.path = [1,1,1,0]) :
    ∃ error,
      let context := nextContext phase (.failure {reasons := [.fail (.tagged tag message) annotations]})
        n cleanups cursor next captured fuel delay error
      loopResumeAt HostTimeoutSource.program point (HostTimeoutSource.cursor n.val delay .none previous) value =
        .continue (HostTimeoutSource.cursor context.n.val context.delay .none context.previous)
          (resolve HostTimeoutSource.program (point.childWith 0
            (HostTimeoutSource.cursor context.n.val context.delay .none context.previous))) ∧
      HostTimeoutNumberPhaseFlow.At context.before state ∧
      context.before.exits.all HostTimeoutNumberLedger.exitRetries = true := by
  obtain ⟨error, encoded⟩ := failure_value state phase n delay previous value _ good published
  have declared := HostTimeoutNumberRootSuffix.retry_declared state phase n delay previous value
    tag message annotations good published
  refine ⟨error, ?_, published, ?_⟩
  · rw [encoded, HostTimeoutNumberLoop.failure_next point n.val delay previous error slots path]
    simp only [next, ↓reduceIte]
    rfl
  · change (phase.exits ++ [(Exit.failure {reasons := [.fail (.tagged tag message) annotations]} : ExitV)]).all
      HostTimeoutNumberLedger.exitRetries = true
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, prior, declared]

end Test.Dogfood.Proofs.HostTimeoutNumberRootLoop
