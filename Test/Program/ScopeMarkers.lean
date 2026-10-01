import Effect4.Laws.Program.ScopeMarkers

/-!
# The scope markers: controls

Controls for `src/Effect4/Laws/Program/ScopeMarkers.lean` (formal pass, algebra note §2.2, probe
`P5ScopeMarkers.lean`; verifier ALG-12). Red: a scope is not an algebraic operation
(`guardR_not_algebraic`); erasure runs a continuation on the exits a guard skips, so erasure and
the machine's sequencing agree only for continuations that pass those exits through
(`erasure_runs_skipped`). Both refusals are also pinned by elaboration. Positive: `denoteR`'s
sequencing shape meets the premise (`seqR_passesSkipped`), so the taken-only reading applies.
-/

set_option autoImplicit false
namespace Test.Program.ScopeMarkers
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- A body that fails at once. -/
def failing : RProgram := .pure (.failure Cause.empty)

/-- A continuation into `unit` on every exit: it does not pass a failure through. -/
def toUnit : ExitV → RProgram := fun _ => .pure (.success Val.unit)

/-- **Red control: a scope is not an algebraic operation.** Putting the continuation inside the
scope changes the program: the saved branch passes the exit out instead of continuing. -/
theorem guardR_not_algebraic :
    ∃ (kind : GuardKind) (body : RProgram) (k : ExitV → RProgram),
      (guardR kind body).bind k ≠ guardR kind (body.bind k) := by
  let ex0 : ExitV := .success Val.unit
  let ex1 : ExitV := .success (Val.nat 1)
  refine ⟨.onSuccess, .pure ex0, fun _ => .pure ex1, ?_⟩
  intro h
  rw [guardR_bind] at h
  unfold guardR at h
  injection h with _ hk
  have hc := congrFun hk (some ex0)
  injection hc with hv
  injection hv with hv'
  cases hv'

/-- **Red control: erasure runs the skipped exits.** `toUnit` does not pass an `onSuccess`
guard's skipped failure through, and for it the erased scope is not the taken-only sequencing:
erasure answers `unit` where the machine's frame skip would hand the failure on. -/
theorem erasure_runs_skipped :
    ¬ PassesSkipped .onSuccess toUnit ∧
      eraseControl ((guardR .onSuccess failing).bind toUnit) ≠
        (eraseControl failing).bind (fun ex =>
          if GuardKind.onSuccess.hasExitArm ex then eraseControl (toUnit ex) else .pure ex) := by
  refine ⟨fun pass => ?_, ?_⟩
  · have h := pass (.failure Cause.empty) rfl
    injection h with h'
    cases h'
  · rw [eraseControl_guardR_bind]
    unfold failing toUnit
    rw [eraseControl_pure, eraseControl_pure]
    intro h
    injection h with h'
    cases h'

/-- The sequencing shape `denoteR` uses meets the premise, so erasure reads it taken-only. -/
theorem seq_reads_taken (body : RProgram) (k : Val → RProgram) :
    eraseControl ((guardR .onSuccess body).bind (seqR k)) =
      (eraseControl body).bind (fun ex =>
        if GuardKind.onSuccess.hasExitArm ex then eraseControl (seqR k ex) else .pure ex) :=
  eraseControl_guardR_bind_taken .onSuccess body (seqR k) (seqR_passesSkipped k)

/-! The two refusals by elaboration: algebraicity does not hold by computation, and the
taken-only law refuses `toUnit` at its premise. -/

/--
error: Type mismatch
  rfl
has type
  ?m.23 = ?m.23
but is expected to have type
  Effects.Program.bind (guardR GuardKind.onSuccess (Effects.Program.pure (Exit.success Val.unit))) toUnit =
    guardR GuardKind.onSuccess ((Effects.Program.pure (Exit.success Val.unit)).bind toUnit)
-/
#guard_msgs (error) in
example : (guardR .onSuccess (.pure (.success Val.unit))).bind toUnit =
    guardR .onSuccess ((.pure (.success Val.unit) : RProgram).bind toUnit) := rfl

/--
error: Type mismatch
  rfl
has type
  ?m.21 = ?m.21
but is expected to have type
  toUnit x✝¹ = Effects.Program.pure x✝¹
-/
#guard_msgs (error) in
example : eraseControl ((guardR .onSuccess failing).bind toUnit) =
    (eraseControl failing).bind (fun ex =>
      if GuardKind.onSuccess.hasExitArm ex then eraseControl (toUnit ex) else .pure ex) :=
  eraseControl_guardR_bind_taken .onSuccess failing toUnit (fun _ _ => rfl)

#print axioms guardR_not_algebraic
#print axioms erasure_runs_skipped
#print axioms seq_reads_taken
end Test.Program.ScopeMarkers
