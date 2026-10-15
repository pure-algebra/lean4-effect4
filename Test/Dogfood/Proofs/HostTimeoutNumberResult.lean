import Test.Dogfood.Proofs.HostTimeoutNumberFormFamily

/-!
Concept: translation-simulation R10, with scope-lifetime-finalization R11.
Question: the actual retry result retains the selected exit already published by the form.
Consumer: the root retry-cursor assertion of Timeout.retries_declared.
Reach: the real success encoder and typed catch callback at their actual captured source points.
Limit: arbitrary recorded interruption causes are not assumed free of typed failures.
The actual root-pop assertion must supply that fact when it skips a handler.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberResult
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberState HostTimeoutNumberLedger
open HostTimeoutNumberFlow HostTimeoutNumberFormFamily

/-- The actual success encoder captures the same retry cursor as the completed form. -/
def answerPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous
    fuel := fuel + 2}

/-- The actual catch callback captures the concrete retry predicate. -/
def catchPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous
    fuel := fuel + 2}

/-- The actual success callback returns the loop's encoded successful result. -/
theorem answer_code (view : View) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (previous body : Val) :
    (interpreter view).contA (.cont (answerPoint captured fuel delay n previous)) body =
      .success (.list [.some body, .none]) := by kernel_rfl

/-- The actual typed catch callback either rethrows or returns its tested failure payload. -/
theorem catch_code (view : View) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (previous : Val) (cause : CauseV) :
    (interpreter view).contE (.caughtError (catchPoint captured fuel delay n previous)) cause =
      match caughtErrorValue? (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
          HostTimeoutSource.retryTest cause with
      | none => .failure cause
      | some error => .success (.list [.none, .some error]) := by kernel_rfl

/-- The saved success encoder retains the exact published selected success and its post-cleanup heap. -/
theorem answer_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.formAfterCleanup image own) (.retryResult image own)
      (.onSuccess body (.cont (answerPoint captured fuel delay n previous))) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨attemptExit, selected, heap, equal⟩ := good
    rw [equal] at heap
    rw [answer_code]
    exact CodeAt.success _ _ ⟨attemptExit, .success value, heap, rfl⟩
  · intro next future cause good
    exact good

/-- The actual typed callback retains its published cause before any future handler can select it. -/
theorem catch_result (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (cause : CauseV)
    (good : CauseAt state (.retryResult image own) cause) :
    CodeAt state (.retryResult image own)
      ((interpreter view).contE (.caughtError (catchPoint captured fuel delay n previous)) cause) := by
  rw [catch_code]
  cases handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest cause with
  | none => exact CodeAt.failure _ cause good
  | some error =>
    obtain ⟨attemptExit, selected, heap, original | interrupted⟩ := good
    · rw [original] at heap
      exact CodeAt.success _ _ ⟨attemptExit, .failure cause, heap,
        n, delay, previous, error, rfl, handled⟩
    · have refused := no_typed_test
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
        HostTimeoutSource.retryTest cause interrupted
      rw [refused] at handled
      cases handled

/-- Skipping an actual handler uses its recorded interruption premise instead of an arbitrary-frame closure. -/
theorem catch_skip (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (fiber : HostTimeoutFrames.NativeFrame) (body : NCode) (name : EffName) (cause delivered : CauseV)
    (good : CauseAt state (.retryResult image own) cause)
    (recordedClean : ∀ recorded, fiber.interruptedCause = some recorded → NoTypedFailure recorded)
    (skipped : FrameFiber.skippedCause .contE (.onFailure body name) fiber (some cause) = some delivered) :
    CauseAt state (.retryResult image own) delivered := by
  cases recorded : fiber.interruptedCause with
  | none =>
    simp only [FrameFiber.skippedCause, recorded] at skipped
    change some cause = some delivered at skipped
    have equal := Option.some.inj skipped
    rw [← equal]
    exact good
  | some interrupted =>
    have clean := recordedClean interrupted recorded
    have step : FrameFiber.skippedCause .contE (.onFailure body name) fiber (some cause) =
        some (Cause.sanitize cause interrupted) := by
      simp only [FrameFiber.skippedCause, recorded]
      rfl
    rw [step] at skipped
    have equal := Option.some.inj skipped
    rw [← equal]
    exact cause_sanitize state (.retryResult image own) cause interrupted good clean

/-- The actual completed-form cell determines the selected exit, independently of cleanup's interruption flag. -/
theorem selected_unique (image : Image) (own : image.count = image.cleanups.length + 1)
    (firstAttempt first secondAttempt second : ExitV)
    (equal : (image.afterForm own firstAttempt first).heap = (image.afterForm own secondAttempt second).heap) :
    first = second := by
  have cells := congrArg (fun (heap : RefHeap) => heap[2]?) equal
  change some (Val.list (image.afterForm own firstAttempt first).completed) =
    some (Val.list (image.afterForm own secondAttempt second).completed) at cells
  have logsEqual := congrArg Store.Val.children (Option.some.inj cells)
  change (image.afterForm own firstAttempt first).completed =
    (image.afterForm own secondAttempt second).completed at logsEqual
  have firstDecoded := form_exits (image.afterForm own firstAttempt first).numbers.formsAt
  have secondDecoded := form_exits (image.afterForm own secondAttempt second).numbers.formsAt
  have decoded := firstDecoded.symm.trans ((congrArg (List.filterMap entryExit) logsEqual).trans secondDecoded)
  change image.exits ++ [first] = image.exits ++ [second] at decoded
  have entries := List.append_cancel_left decoded
  exact (List.cons.inj entries).1

/-- A tested singleton failure result permits a declared predecessor in the actual completed log. -/
theorem failure_declared (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (value : Val)
    (good : ValueAt state (.retryResult image own) value)
    (tag message : String) (annotations : ReasonAnnotations Ann)
    (actualAttempt : ExitV)
    (published : ImageAt (image.afterForm own actualAttempt
      (.failure {reasons := [.fail (.tagged tag message) annotations]})) state) :
    exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  obtain ⟨attemptExit, saved, heap, returned⟩ := good
  have equal := selected_unique image own attemptExit saved actualAttempt
    (.failure {reasons := [.fail (.tagged tag message) annotations]}) (heap.symm.trans published)
  rw [equal] at returned
  obtain ⟨n, delay, previous, error, encoded, handled⟩ := returned
  exact caught_singleton_declared n delay previous tag message annotations error handled

end Test.Dogfood.Proofs.HostTimeoutNumberResult
