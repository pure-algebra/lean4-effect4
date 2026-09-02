import Effect4.Concurrency.Scheduler
import Effect4.Runtime.Scope

/-!
# Fork and supervision counterexamples

These finite, kernel-checked witnesses use canonical FiberState, Cause, Exit,
and Scope data. They do not import the missing Supervision implementation.
They expose the named information loss or false law; they are not a whole
runtime equivalence proof. E4-CONC-CE-024 and 025 additionally have independent
pinned-runtime witnesses in `harness/fiber-supervision/runtime-check.ts`.
-/

set_option autoImplicit false

namespace Effect4Test.Counterexamples.Concurrency.FiberSupervision

private abbrev C := Effect4.Cause Nat Nat Nat Unit
private abbrev X := Effect4.Exit Nat Nat Nat Nat Unit

private def fid (n : Nat) : Effect4.FiberId := ⟨n⟩

private def observed (fiber : Effect4.FiberState X) : Option X :=
  if fiber.status = .done then fiber.terminal else none

private def heldBody : Effect4.FiberState X where
  id := fid 0
  status := .finalizing
  terminal := some (.success 7)
  mask := .unmasked
  interruptPending := false
  cleanup := .pending
  cleanupCount := 0

private def completed : Effect4.FiberState X :=
  {heldBody with status := .done, cleanup := .done, cleanupCount := 1}

private def register (daemon : Bool) (child : Effect4.FiberState X)
    (children : List Effect4.FiberId) : List Effect4.FiberId :=
  if daemon = false ∧ (observed child).isNone = true then
    children ++ [child.id]
  else children

/-- E4-CONC-CE-012: registration before immediate execution retains a child
which the source deliberately never registers after it has already completed. -/
theorem immediate_completion_not_tracked :
    register false completed [] = [] ∧
      register false heldBody [] = [fid 0] := by decide

private def parentRequests (middleware : Bool) (children : List Nat) : List Nat :=
  if middleware then children else []

/-- E4-CONC-CE-013: daemon and child ownership differ even when the global
middleware has previously been installed by another fiber. -/
theorem daemon_parent_exit_distinction :
    register true heldBody [] = [] ∧
      register false heldBody [] = [fid 0] ∧
      parentRequests true [] = [] ∧ parentRequests true [1] = [1] := by decide

private def afterRegistration (children : List Nat) (newChild : Nat) : List Nat :=
  children ++ [newChild]

/-- E4-CONC-CE-014: immediate execution removes a sibling and creates a nested
child while installing global middleware. Reusing the pre-start snapshot loses
all three observations even when the returned new-child identity agrees. -/
theorem post_start_state_not_pre_state :
    afterRegistration [] 2 = [2] ∧
      afterRegistration [1] 2 ≠ afterRegistration [] 2 ∧
      ([0, 1, 2] : List Nat) ≠ [0, 1, 2, 3] ∧
      (false : Bool) ≠ true := by decide

/-- E4-CONC-CE-015: the local body Exit exists before cleanup/publication.
A join that reads terminal without checking publication returns too early. -/
theorem unpublished_body_exit :
    heldBody.terminal = some (.success 7) ∧
      observed heldBody = none ∧ observed completed = some (.success 7) := by decide

private def failed : X := .failure (Effect4.Cause.fail 3)
private def awaitFailed : Effect4.Exit X Nat Nat Nat Unit := .success failed

/-- E4-CONC-CE-016: awaiting a failed child succeeds with its Exit as a value;
joining the same child resumes the failure as an effect. -/
theorem await_failure_as_value :
    awaitFailed.isSuccess = true ∧ failed.isSuccess = false := by decide

private inductive Call
  | request (child : Nat)
  | awaitAll (children : List Nat)
  deriving DecidableEq

private def requestsBeforeAwait : List Call -> List Nat
  | [] => []
  | .request child :: rest => child :: requestsBeforeAwait rest
  | .awaitAll _ :: _ => []

/-- E4-CONC-CE-017: awaiting the first child before requesting the next can
block the second request forever. This does not forbid publications during a
request: it fixes the explicit request/await call order only. -/
theorem request_all_before_wait :
    requestsBeforeAwait [.request 1, .request 2, .awaitAll [1, 2]] = [1, 2] ∧
      requestsBeforeAwait [.request 1, .awaitAll [1], .request 2] = [1] := by decide

private def finalizerInterruptor (skipSelf : Bool) (child current : Nat) : Option Nat :=
  if skipSelf = true ∧ current = child then none else some current

/-- E4-CONC-CE-018: forkIn guards self-interruption; fiberRunIn does not.
Their already-closed branches also choose different interruptor identities. -/
theorem scope_binding_asymmetry :
    finalizerInterruptor true 22 22 = none ∧
      finalizerInterruptor false 22 22 = some 22 ∧
      (some 11 : Option Nat) ≠ some 22 := by decide

private abbrev TestScope := Effect4.Scope Nat Nat Nat Nat Nat Nat Unit

private def linked : TestScope :=
  ((Effect4.Scope.make .sequential).addUnsafe 1 10).addUnsafe 2 20

/-- E4-CONC-CE-019: removing a freshly minted or unrelated key does not remove
the exact linked finalizer. Removing the shared key preserves the other slot. -/
theorem shared_scope_key_required :
    (linked.removeUnsafe 1).finalizerKeys = [2] ∧
      (linked.removeUnsafe 37).finalizerKeys = [1, 2] := by decide

private def addedChildren (initial current : List Nat) : List Nat :=
  current.filter (fun child => decide (child ∉ initial))

/-- E4-CONC-CE-020: awaitAllChildren waits for new children still present after
the body; it neither waits for old siblings nor resurrects a finished child. -/
theorem only_new_children_awaited :
    addedChildren [1] [1, 2] = [2] ∧
      addedChildren [1] [2] = [2] ∧
      addedChildren [1] [] = [] := by decide

private def interruptOne : C := Effect4.Cause.interrupt (some 1)
private def interruptTwo : C := Effect4.Cause.interrupt (some 2)

/-- E4-CONC-CE-021: overwriting the interruption cause loses the first
interruptor, while canonical Cause.combine retains both reasons. -/
theorem interruptors_accumulate :
    (Effect4.Cause.combine interruptOne interruptTwo).reasons =
      interruptOne.reasons ++ interruptTwo.reasons ∧
      Effect4.Cause.combine interruptOne interruptTwo ≠ interruptTwo := by decide

private def failOne : C := Effect4.Cause.fail 1
private def failTwo : C := Effect4.Cause.fail 2

private def raceFailure (arrivals : List C) : X :=
  .failure ⟨arrivals.flatMap Effect4.Cause.reasons⟩

/-- E4-CONC-CE-022: the all-failure race appends callback-arrival reasons,
retains duplicates, and remains Failure for a nonempty all-empty-cause input. -/
theorem race_failure_order_and_duplicates :
    raceFailure [failOne, failTwo] ≠ raceFailure [failTwo, failOne] ∧
      (raceFailure [failOne, failOne]).causeReasons =
        failOne.reasons ++ failOne.reasons ∧
      (raceFailure [failOne, failOne]).causeReasons ≠
        (Effect4.Cause.combine failOne failOne).reasons ∧
      (raceFailure [Effect4.Cause.empty]).isSuccess = false := by decide

private def waitResult (targets published : List Nat) (selected : Option X) : Option X :=
  if (targets.filter (fun child => decide (child ∉ published))).isEmpty then
    selected
  else none

/-- E4-CONC-CE-023: neither empty input nor a selected winner waiting for a
masked live child supplies a completed result. A publication changes the latter. -/
theorem race_empty_and_cleanup_frontiers :
    waitResult [] [] none = none ∧
      waitResult [2] [] (some (.success 7)) = none ∧
      waitResult [2] [2] (some (.success 7)) = some (.success 7) := by decide

private def cleanupTargets (liveAtWinner liveAtRequest : List Nat) : List Nat :=
  if liveAtWinner.isEmpty then [] else liveAtRequest

/-- E4-CONC-CE-024: a reentrant winner captures only the empty/nonempty branch.
With an empty set, a late entrant is left live. With a nonempty set, the mutable
set is read later and includes the late entrant. Neither all-launched cleanup
nor a fixed winner-time target snapshot matches both pinned source traces. -/
theorem race_reentrant_launch_branch :
    cleanupTargets [] [2] = [] ∧
      2 ∉ cleanupTargets [] [2] ∧
      cleanupTargets [2] [2, 3] = [2, 3] ∧
      3 ∈ cleanupTargets [2] [2, 3] ∧
      cleanupTargets [2] [2, 3] ≠ ([2] : List Nat) := by decide

private def continueAfterWait (body : X)
    (waitExit : Effect4.Exit Unit Nat Nat Nat Unit) : X :=
  match waitExit with
  | .success _ => body
  | .failure cause => .failure cause

/-- E4-CONC-CE-025: the stored local body Exit is the successful wait
continuation. A further interruption of the parent can fail that wait and
replace the accepted Exit; storing the old value does not establish stability. -/
theorem parent_interruption_replaces_exit :
    continueAfterWait (.success 7) (.success ()) = .success 7 ∧
      continueAfterWait (.success 7)
        (.failure (Effect4.Cause.interrupt (some 99))) =
          .failure (Effect4.Cause.interrupt (some 99)) ∧
      continueAfterWait (.success 7) (.success ()) ≠
        continueAfterWait (.success 7)
          (.failure (Effect4.Cause.interrupt (some 99))) := by decide

/-- E4-CONC-CE-026: an individually well-formed child's child set can still
name an unallocated identity. Without global ownership admission, that identity
can be minted again. A post-start parent ownership check alone misses it. -/
theorem post_start_child_ownership_required :
    (99 : Nat) ∉ [0, 1] ∧ (99 : Nat) ∈ [99] ∧
      ([] : List Nat).Nodup ∧ ([99] : List Nat).Nodup := by decide

#print axioms post_start_child_ownership_required
#print axioms immediate_completion_not_tracked
#print axioms daemon_parent_exit_distinction
#print axioms post_start_state_not_pre_state
#print axioms unpublished_body_exit
#print axioms await_failure_as_value
#print axioms request_all_before_wait
#print axioms scope_binding_asymmetry
#print axioms shared_scope_key_required
#print axioms only_new_children_awaited
#print axioms interruptors_accumulate
#print axioms race_failure_order_and_duplicates
#print axioms race_empty_and_cleanup_frontiers
#print axioms race_reentrant_launch_branch
#print axioms parent_interruption_replaces_exit

end Effect4Test.Counterexamples.Concurrency.FiberSupervision
