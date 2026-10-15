import Effect4.Laws.Program.Guard.Interruption

/-!
Concept: reactive-scheduling R9 and scope-lifetime-finalization R11.
Consumer: the common pending allocation configuration and actual Timeout source-entry handoff.
The pending root records only causes without typed failure.
Actual native moves retain that record, and actual outside interruption supplies the admitted cause.
This relative fact does not prove application history after entry.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- The pending record excludes typed failures supplied by fabricated interruption commands. -/
def CleanCause (cause : CauseV) : Prop := ∀ reason ∈ cause.reasons, reason.tag ≠ .fail

/-- Every actual pending interruption record satisfies the same cause admission. -/
def CleanRecorded (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∀ cause, frame.interruptedCause = some cause → CleanCause cause

/-- Actual caller and target annotations cannot turn an interruption into a typed failure. -/
theorem clean_interrupt (root : NativeEff) (table : RowTable) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (target : FiberId) :
    CleanCause (interruptCause (interpOf root table) who extra target) := by
  intro reason member
  simp only [Machine.interruptCause, Supervision.interruptCause, Cause.annotate,
    Cause.interrupt, List.map_singleton, List.mem_singleton] at member
  subst reason
  rw [Reason.annotate_tag, Reason.annotate_tag]
  intro impossible
  cases impossible

/-- The real accumulation combines only the admitted incoming cause and the admitted actual record. -/
theorem CleanRecorded.interruption (fiber : Moves.NFiber) (cause : CauseV)
    (incoming : CleanCause cause) (recorded : CleanRecorded fiber.frame) :
    CleanRecorded (interruptWithCause cause fiber).1.frame := by
  have clean : CleanCause (match fiber.frame.interruptedCause with
      | none => cause | some old => Cause.combine old cause) := by
    cases found : fiber.frame.interruptedCause with
    | none => exact incoming
    | some old =>
      intro reason member
      rcases (Cause.mem_combine reason old cause).mp member with before | after
      · exact recorded old found reason before
      · exact incoming reason after
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

end Effect4.Program.AnswerSlots.AllocationAdapter
