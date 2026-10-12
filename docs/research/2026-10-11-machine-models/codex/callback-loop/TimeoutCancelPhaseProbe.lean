import TimeoutRaceWaitingProbe

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the actual parked cancellation edge and its post-join restore callback.
Reach: actual async-finalizer arms and a completed join containing the assigned attempt.
The retired cleanup witness and reached public-cut premise remain producer obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutCancelPhase
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open HostTimeoutFlow HostTimeoutNumberFlow HostTimeoutJointGeneration HostTimeoutNumberSteps

/-- A waiting success already carries cleanup; only an actual interrupt may enter before cleanup. -/
def WaitingCause (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (cause : CauseV) : Prop :=
  (∃ exit, ImageAt (image.cleanup own exit) state) ∨
    (ImageAt image state ∧ cause.hasInterrupts = true)

/-- The active heap cannot already be the cleanup heap of that same generation. -/
theorem active_not_cleaned (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (heap : ImageAt image state) :
    ¬ ∃ exit, ImageAt (image.cleanup own exit) state := by
  intro cleaned
  obtain ⟨exit, after⟩ := cleaned
  have same := heap.symm.trans after
  have logs := congrArg (fun refs : RefHeap => refs[1]?) same
  change some (Val.list image.cleanups) =
    some (Val.list (image.cleanups ++ [.list [.nat image.count, .bool (interruptionFlag exit)]])) at logs
  have lengths := congrArg (fun value : Val => value.children.length) (Option.some.inj logs)
  simp only [Effect4.Store.Val.children, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at lengths
  omega

/-- The pre-cleanup waiting input permits only an actual interrupt cause. -/
theorem active_cause_interrupt (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (heap : ImageAt image state) (cause : CauseV)
    (good : WaitingCause state image own cause) : cause.hasInterrupts = true := by
  rcases good with cleaned | active
  · exact False.elim (active_not_cleaned state image own heap cleaned)
  · exact active.2

/-- The actual cancellation arm retains the original cause and executes cancellation only for interrupts. -/
theorem cause_arm (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (cause : CauseV) (race token : Nat) (owner : FiberId)
    (provided : Option ExitV) (good : WaitingCause state image own cause) :
    let name := EffName.withWaiter (.store (.cancelRace race)) owner token
    ((.asyncFinalizer name : NCode).armE (interpreter view).toPrimInterp cause provided =
      some ((interpreter view).cancelThenFail name cause, []) ∧ cause.hasInterrupts = true ∧
        (ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)) ∨
      ((.asyncFinalizer name : NCode).armE (interpreter view).toPrimInterp cause provided =
        some (.failure cause, []) ∧ CauseAt state (.cleanupExit image own) cause) := by
  dsimp only
  cases interrupted : cause.hasInterrupts with
  | true =>
    refine .inl ⟨Prim.armE_asyncFinalizer_interrupt _ _ cause provided interrupted, rfl, ?_⟩
    rcases good with cleaned | active
    · exact .inr cleaned
    · exact .inl active.1
  | false =>
    refine .inr ⟨Prim.armE_asyncFinalizer_no_interrupt _ _ cause provided interrupted, ?_⟩
    rcases good with cleaned | active
    · exact cleaned
    · rw [interrupted] at active
      cases active.2

/-- The actual cancel hook builds the race action beneath the callback that re-raises its captured cause. -/
theorem cancel_program (view : View) (race token : Nat) (owner : FiberId) (cause : CauseV) :
    (interpreter view).cancelThenFail (.withWaiter (.store (.cancelRace race)) owner token) cause =
      .onSuccess (.withFiber (.store (.act (.cancelRace race)))) (.reFail cause) := by
  kernel_rfl

/-- The re-failure callback consumes completed cleanup and retains exactly the original cause. -/
theorem restore_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (cause : CauseV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) (.cleanupExit image own) (.onSuccess program (.reFail cause)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    exact CodeAt.failure _ cause good
  · intro next future other good
    exact good

/-- A completed join containing the assigned attempt feeds the actual captured-cause restore callback.
The retirement premise retains cleanup issued by the writer; a timer-only join cannot discharge membership. -/
theorem joined_restore (view : View) (machine : NativeMachine) (image : Image) (n : Fin 4)
    {plain : Bool} (active : Active image n plain) (target : FiberId) (attempt : Guard.NFiber)
    (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (member : target ∈ targets) (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        CleanupCommitted n exit (image.cleanup active.own exit).cleanups)
    (fiber : HostTimeoutFrames.NativeFrame) (program : NCode) (cause : CauseV)
    (output : HostTimeoutNumberFlow.Kind) (noDeferred : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit image active.own) output fiber.stack) :
    ({fiber with stack := .onSuccess program (.reFail cause) :: fiber.stack}).resumeValue
      (interpreter view).toPrimInterp .unit none =
        (.running {fiber with current := .failure cause}, [.popped (.onSuccess program (.reFail cause))]) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp machine.state output
        {fiber with current := .failure cause} := by
  obtain ⟨attemptExit, ended, heap, committed⟩ := join_cleaned machine image n active target attempt
    targets exits joined member found retired
  exact AnswerFlow.resume_success (model view) (interpreter view).toPrimInterp machine.state
    (.cleanupExit image active.own) (.cleanupExit image active.own) output fiber program (.reFail cause)
    .unit none noDeferred ⟨attemptExit, heap⟩ (by intro exit member; cases member)
    (restore_saved view machine.state image active.own cause program) stack
end Test.Dogfood.Proofs.HostTimeoutCancelPhase
