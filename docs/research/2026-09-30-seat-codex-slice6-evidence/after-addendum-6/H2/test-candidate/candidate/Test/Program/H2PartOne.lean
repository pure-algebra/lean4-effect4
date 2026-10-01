import Effect4.Laws.Program.Typed.Assembly

/-! H2 part-one candidate controls; not yet compiled. These are new test declarations.
The old field-only placement is retained separately in FieldOnlyRed.lean. -/
set_option autoImplicit false
namespace Test.Program.H2PartOne
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-- The base membership judgment remains deliberately unchanged. -/
theorem base_badName_still_fits (w : W) (ty : EffTy) :
    FitsExit w ty (.failure (Cause.die .badName)) := fitsExit_of_clean w ty _ rfl

theorem clean_still_allows_badName :
    cleanExit (.failure (Cause.die .badName)) = true := rfl

theorem badName_refused (w : W) (ty : EffTy) :
    ¬ ExitOk w ty (.failure (Cause.die .badName)) := by
  intro typed
  have excluded := typed.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl

theorem notImplemented_refused (w : W) (ty : EffTy) :
    ¬ ExitOk w ty (.failure (Cause.die .notImplemented)) := by
  intro typed
  have excluded := typed.2 (.die .notImplemented .empty) (List.mem_singleton_self _)
  exact excluded.2 rfl

theorem bad_current_code_refused (root : ProgramSource) (w : W) (ty : EffTy) :
    ¬ TypedProg root w ty (.pure (.failure (Cause.die .badName))) :=
  fun typed => badName_refused w ty (TypedProg.pure_inv typed)

theorem notImplemented_current_code_refused (root : ProgramSource) (w : W) (ty : EffTy) :
    ¬ TypedProg root w ty (.pure (.failure (Cause.die .notImplemented))) :=
  fun typed => notImplemented_refused w ty (TypedProg.pure_inv typed)

/-- The defect clause is finite and independent of requirement rows in part one. -/
theorem ordinary_die_shape (ty : EffTy) (defect : Defect)
    (notBadName : defect ≠ .badName) (implemented : defect ≠ .notImplemented) :
    NoShapeDefect ty (.failure (Cause.die defect)) := by
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst member
  exact ⟨notBadName, implemented⟩

theorem user_die_admitted (w : W) (ty : EffTy) (payload : Nat) :
    ExitOk w ty (.failure (Cause.die (.user payload))) :=
  strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty (.user payload) (by intro h; cases h) (by intro h; cases h))

theorem user_current_code_admitted (root : ProgramSource) (w : W) (ty : EffTy) (payload : Nat) :
    TypedProg root w ty (.pure (.failure (Cause.die (.user payload)))) :=
  TypedProg.pure (user_die_admitted w ty payload)

theorem missingService_admitted_at_any_type (w : W) (ty : EffTy) :
    ExitOk w ty (.failure (Cause.die .missingService)) :=
  strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty .missingService (by intro h; cases h) (by intro h; cases h))

theorem missingService_empty_admitted (w : W) :
    ExitOk w (EffTy.pure .unit) (.failure (Cause.die .missingService)) :=
  missingService_admitted_at_any_type w _

theorem missingService_nonempty_admitted (w : W) :
    ExitOk w ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩
      (.failure (Cause.die .missingService)) := missingService_admitted_at_any_type w _

theorem missingService_current_code_admitted (root : ProgramSource) (w : W) (ty : EffTy) :
    TypedProg root w ty (.pure (.failure (Cause.die .missingService))) :=
  TypedProg.pure (missingService_admitted_at_any_type w ty)

#print axioms base_badName_still_fits
#print axioms clean_still_allows_badName
#print axioms badName_refused
#print axioms notImplemented_refused
#print axioms bad_current_code_refused
#print axioms notImplemented_current_code_refused
#print axioms ordinary_die_shape
#print axioms user_die_admitted
#print axioms user_current_code_admitted
#print axioms missingService_admitted_at_any_type
#print axioms missingService_empty_admitted
#print axioms missingService_nonempty_admitted
#print axioms missingService_current_code_admitted

theorem interrupt_admitted (w : W) (ty : EffTy) (who : Option FiberId) :
    ExitOk w ty (.failure (Cause.interrupt who)) := by
  apply strongExit_of_clean w ty _ rfl
  apply noShapeDefect_of_interrupts
  intro reason member
  simp only [Cause.interrupt_reasons, List.mem_singleton] at member
  subst member
  rfl

#print axioms interrupt_admitted
end Test.Program.H2PartOne
