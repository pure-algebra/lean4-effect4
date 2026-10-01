/-- A recorded cause has only interrupt reasons, so it meets part one's exclusion. -/
theorem recorded_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    {cause : CauseV} (recorded : x.interruptedCause = some cause) :
    NoShapeDefect ty (.failure cause) :=
  noShapeDefect_of_interrupts ty cause (hp.recorded cause recorded)

/-- The injected pending cause is recorded interruption or the empty cause. -/
theorem pendingCause_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x) :
    NoShapeDefect ty (.failure x.pendingCause) := by
  cases recorded : x.interruptedCause with
  | some cause =>
    have pending : x.pendingCause = cause := by
      simp only [RSaved.pendingCause, recorded, Option.getD_some]
    rw [pending]
    exact recorded_noShapeDefect ty hp recorded
  | none =>
    have pending : x.pendingCause = Cause.empty := by
      simp only [RSaved.pendingCause, recorded, Option.getD_none]
    rw [pending]
    exact noShapeDefect_of_interrupts ty Cause.empty (fun _ member => nomatch member)

/-- Preemption keeps exclusion only when the original cause has it; provenance supplies
exclusion of the recorded cause. No requirement-row transport is claimed in part one. -/
theorem sanitize_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    (cause : CauseV) {interrupted : CauseV} (recorded : x.interruptedCause = some interrupted)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_sanitize ty cause interrupted shape (recorded_noShapeDefect ty hp recorded)

