import Test.Dogfood.Proofs.HostTimeoutNumberResult

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the root's active form region carries the numeric result to the actual retry handler.
Consumer: the root phase of Timeout.cleanup_keeps and Timeout.retries_declared.
Reach: the actual ordered saved prefix above its untouched source-handler suffix.
Limit: the producer must establish this prefix and its source captures at the race registration.
The catch handler is outside the region and uses the actual recorded-interruption premise.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutNumberRegion
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberFlow HostTimeoutNumberFinalizers HostTimeoutNumberResult

/-- The numeric root region ends immediately before its actual source catch handler. -/
def RootRegionAt (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) : Prop :=
  ∃ above, frame.stack = above ++ suffix ∧
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state (.retryResult image own)
      {frame with stack := above}

/-- The actual form finalizer and success encoder compose before the source handler suffix. -/
theorem form_answer_stack (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (formFuel answerFuel delay : Nat) (n : Fin 4) (previous : Val)
    (count : image.count = n.val + 1) (raceBody formBody : NCode) :
    AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) (.retryResult image own)
      [.onExit raceBody (.fin (formPoint captured formFuel delay n previous)) false,
        .onSuccess formBody (.cont (HostTimeoutNumberResult.answerPoint captured answerFuel delay n previous))] :=
  .cons (HostTimeoutNumberFormFamily.form_saved view state image own captured formFuel delay n previous count raceBody)
    (.cons (answer_saved view state image own captured answerFuel delay n previous formBody) (.nil _ _))

/-- Race registration's actual saved numeric prefix supports the root's waiting region. -/
theorem waiting_region (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (formFuel answerFuel delay : Nat) (n : Fin 4) (previous : Val)
    (count : image.count = n.val + 1) (race token : Nat) (owner : FiberId)
    (raceBody formBody : NCode) (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (current : frame.current = .suspend (.park (.race race)))
    (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)
    (stack : frame.stack =
      [.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token),
        .onExit raceBody (.fin (formPoint captured formFuel delay n previous)) false,
        .onSuccess formBody (.cont (HostTimeoutNumberResult.answerPoint captured answerFuel delay n previous))] ++ suffix) :
    RootRegionAt view state image own frame suffix := by
  refine ⟨_, stack, .raceWaiting image own, ?_, ?_⟩
  · change CodeAt state (.raceWaiting image own) frame.current
    rw [current]
    exact CodeAt.raceWaiting image own race phase
  · exact .cons (race_cancel_saved view state image own race token owner)
      (form_answer_stack view state image own captured formFuel answerFuel delay n previous count raceBody formBody)

/-- Reaching the actual handler suffix exposes the exact numeric result established by the region. -/
theorem returned_result (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) (value : Val)
    (region : RootRegionAt view state image own frame suffix)
    (boundary : frame.stack = suffix) (returned : frame.current = .success value) :
    ValueAt state (.retryResult image own) value := by
  obtain ⟨above, frames, input, code, stack⟩ := region
  have lengths := congrArg List.length (boundary.symm.trans frames)
  simp only [List.length_append] at lengths
  have empty : above = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst above
  cases stack
  change CodeAt state (.retryResult image own) frame.current at code
  rw [returned] at code
  cases code with
  | success kind value good => exact good

end Test.Dogfood.Proofs.HostTimeoutNumberRegion
