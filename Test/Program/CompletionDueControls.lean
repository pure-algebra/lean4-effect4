import Effect4.Laws.Program.Typed.Commands.Bookkeeping
set_option autoImplicit false
namespace CompletionHypothesisControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World
/- Concept4, hypothesis controls for M6.step_loop's due-field transfer.
These refute stronger helper interfaces, not a whole ConfigTyped or reachable state. -/
def bad : Completion Val Err Defect FiberId Ann := .ofExit (.failure (Cause.die .badName))
theorem coarse_bad (w : W) (ty : EffTy) : CompletionOk w (ty.answer, ty.error) bad := rfl
theorem strong_bad_refused (w : W) (ty : EffTy) : ¬ CompletionStrong w ty bad := by
  intro typed
  have excluded := typed.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl
theorem ordinary_defect_admitted (w : W) (ty : EffTy) (payload : Nat) :
    CompletionStrong w ty (.ofExit (.failure (Cause.die (.user payload)))) := by
  apply strongExit_of_clean w ty _ rfl
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst member
  exact ⟨(by intro h; cases h), (by intro h; cases h)⟩
theorem coarse_not_sufficient (w : W) (ty : EffTy) :
    ¬ (CompletionOk w (ty.answer, ty.error) bad → CompletionStrong w ty bad) :=
  fun h => strong_bad_refused w ty (h (coarse_bad w ty))

def due (w : W) (owed : List (Owed (Completion Val Err Defect FiberId Ann))) : Prop :=
  ∀ o ∈ owed, ∀ ty, w.Θ o.waiter o.token = some ty → CompletionStrong w ty o.code

def u : EffTy := EffTy.pure Ty.unit
def w0 : W := initialWorld u
def w1 : W := { w0 with Θ := fun _ _ => some u }
def badOwed : Owed (Completion Val Err Defect FiberId Ann) := ⟨Api.root, 0, bad, .now⟩

theorem growing : w0.leHost w1 := by
  refine ⟨⟨Effect4.Machine.World.le_refl _, table_refl _, table_refl _, table_refl _,
    ⟨fun _ _ h => h, fun _ _ h => h⟩, ?_, rfl⟩, fun _ _ h => h⟩
  intro id token ty h
  cases h

theorem old_due : due w0 [badOwed] := by
  intro o _ ty declared
  cases declared

theorem new_due_refused : ¬ due w1 [badOwed] := by
  intro h
  exact strong_bad_refused w1 u (h badOwed (List.mem_singleton_self _) u rfl)

theorem due_not_monotone :
    ¬ (∀ (a b : W), a.leHost b → ∀ owed, due a owed → due b owed) := by
  intro h
  exact new_due_refused (h w0 w1 growing [badOwed] old_due)

end CompletionHypothesisControls
