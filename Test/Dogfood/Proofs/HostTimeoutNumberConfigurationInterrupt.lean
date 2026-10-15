import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: actual interruption consumes the numeric role's execution and masking permission.
Consumer: the contextual addressed-message component of both Timeout numeric goals.
Reach: the actual interrupted fiber, clean incoming cause, and its actual recorded cause.
Limit: masked read and unit classes require their actual mask premise at the producer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberConfigurationInterrupt
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberConfiguration HostTimeoutNumberFlow

/-- Role frame assertions read the actual current code and ordered saved frames. -/
theorem frame_fields (machine : Effect4.Program.NativeMachine) (role : Role)
    (before after : HostTimeoutFrames.NativeFrame)
    (current : after.current = before.current) (stack : after.stack = before.stack)
    (held : FrameAt machine role before) : FrameAt machine role after := by
  cases role with
  | rootRead suffix =>
      obtain ⟨control⟩ := held
      exact ⟨{control with
        current := by rw [current]; exact control.current
        stack := stack.trans control.stack}⟩
  | root image own suffix =>
      intro view
      obtain ⟨above, equation, input, code, saved⟩ := held view
      exact ⟨above, stack.trans equation, input, by rw [current]; exact code, saved⟩
  | retired => trivial
  | pending context =>
      refine ⟨HostTimeoutNumberSourceWrites.FrameAt.fields context before after held.1 current stack, ?_⟩
      obtain ⟨input, code, saved⟩ := held.2
      exact ⟨input, by rw [current]; exact code, by rw [stack]; exact saved⟩
  | phase output =>
      intro view
      obtain ⟨input, code, saved⟩ := held view
      exact ⟨input, by rw [current]; exact code, by rw [stack]; exact saved⟩
  | numeric output =>
      intro view
      obtain ⟨input, code, saved⟩ := held view
      exact ⟨input, by rw [current]; exact code, by rw [stack]; exact saved⟩
  | timer =>
      intro view
      obtain ⟨input, code, saved⟩ := held view
      exact ⟨input, by rw [current]; exact code, by rw [stack]; exact saved⟩

/-- The actual recording operation combines only the existing clean cause and the incoming clean cause. -/
theorem accumulated_clean (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (incoming : NoTypedFailure cause)
    (recorded : ∀ old, fiber.frame.interruptedCause = some old → NoTypedFailure old) :
    NoTypedFailure (match fiber.frame.interruptedCause with
      | none => cause | some old => Cause.combine old cause) := by
  cases found : fiber.frame.interruptedCause with
  | none => exact incoming
  | some old => exact no_typed_combine old cause (recorded old found) incoming

/-- The actual interrupt obtains its replacement permission from the addressed live fiber. -/
theorem interrupt_frame (machine : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (held : FiberAt machine role fiber) (incoming : NoTypedFailure cause) :
    FrameAt machine role (interruptWithCause cause fiber).1.frame := by
  unfold interruptWithCause
  split
  · exact held.frame
  · rename_i notFinished
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · rename_i interruptible
      split
      · exact frame_fields machine role fiber.frame _ rfl rfl held.frame
      · rename_i idle
        have running : fiber.running = false := Bool.eq_false_iff.mpr idle
        have live : fiber.exit = none := by
          cases found : fiber.exit with
          | none => rfl
          | some exit =>
              have finished : fiber.exit.isSome = true := by rw [found]; rfl
              exact False.elim (notFinished finished)
        cases recorded : fiber.frame.interruptedCause with
        | none =>
            exact frame_fields machine role {fiber.frame with current := .failure cause} _
              rfl rfl
              (held.immediate cause incoming live running interruptible)
        | some previous =>
            exact frame_fields machine role {fiber.frame with current := .failure (Cause.combine previous cause)} _
              rfl rfl
              (held.immediate _ (no_typed_combine previous cause (held.recorded previous recorded) incoming)
                live running interruptible)
    · exact frame_fields machine role fiber.frame _ rfl rfl held.frame


/-- Actual role permissions transport across metadata edits without changing the saved suffix. -/
theorem fiber_fields (machine : Effect4.Program.NativeMachine) (role : Role)
    (before after : Effect4.Program.SourceScope.SourceFiber) (held : FiberAt machine role before)
    (frame : FrameAt machine role after.frame) (exit : after.exit = before.exit)
    (running : after.running = before.running) (stack : after.frame.stack = before.frame.stack)
    (mask : after.frame.interruptible = before.frame.interruptible)
    (recorded : ∀ cause, after.frame.interruptedCause = some cause → NoTypedFailure cause) :
    FiberAt machine role after := by
  constructor
  · exact frame
  · intro selected published
    exact held.exit selected (exit.symm.trans published)
  · intro retired
    rw [exit]
    exact held.retired retired
  · exact recorded
  · intro cause clean live idle interruptible
    exact frame_fields machine role {before.frame with current := .failure cause}
      {after.frame with current := .failure cause} rfl stack
      (held.immediate cause clean (exit.symm.trans live) (running.symm.trans idle)
        (mask.symm.trans interruptible))
  · intro context same heap installed
    rw [running]
    apply held.pendingRunning context same heap
    change _ ∈ before.frame.stack
    change _ ∈ after.frame.stack at installed
    rw [stack] at installed
    exact installed

  · intro context same heap interruptible
    change _ ∈ after.frame.stack
    rw [stack]
    exact held.pendingCustody context same heap (mask.symm.trans interruptible)

/-- An actual interruption retains the fiber fields used by the numeric execution permission. -/
theorem interrupt_fields (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) :
    (interruptWithCause cause fiber).1.exit = fiber.exit ∧
    (interruptWithCause cause fiber).1.running = fiber.running ∧
    (interruptWithCause cause fiber).1.frame.stack = fiber.frame.stack ∧
    (interruptWithCause cause fiber).1.frame.interruptible = fiber.frame.interruptible := by
  unfold interruptWithCause
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Actual cause recording retains the interruption-only reason condition. -/
theorem interrupt_recorded (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (incoming : NoTypedFailure cause)
    (recorded : ∀ old, fiber.frame.interruptedCause = some old → NoTypedFailure old) :
    ∀ old, (interruptWithCause cause fiber).1.frame.interruptedCause = some old → NoTypedFailure old := by
  have clean := accumulated_clean fiber cause incoming recorded
  unfold interruptWithCause
  split
  · exact recorded
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    cases saved : fiber.frame.interruptedCause <;> simp only [saved] at clean ⊢
    all_goals
      split
      · split
        · intro old equal
          cases Option.some.inj equal
          exact clean
        · intro old equal
          cases Option.some.inj equal
          exact clean
      · intro old equal
        cases Option.some.inj equal
        exact clean

/-- The actual addressed interruption retains the whole numeric fiber assertion. -/
theorem interrupt_fiber (machine : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (held : FiberAt machine role fiber) (incoming : NoTypedFailure cause) :
    FiberAt machine role (interruptWithCause cause fiber).1 := by
  have fields := interrupt_fields fiber cause
  exact fiber_fields machine role fiber _ held (interrupt_frame machine role fiber cause held incoming)
    fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 (interrupt_recorded fiber cause incoming held.recorded)

end Test.Dogfood.Proofs.HostTimeoutNumberConfigurationInterrupt
