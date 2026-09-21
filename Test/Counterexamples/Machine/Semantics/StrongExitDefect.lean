import Effect4.Laws.Program.Typed.Contracts

/-! E4-TYPED-CE-003: the input review's strong cause condition checks Fail payloads.
It cannot exclude a Die reason, including the existing badShapeExit observation. -/
set_option autoImplicit false
namespace Test.Counterexamples.StrongExitDefect
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Typed
abbrev TWorld := Effect4.Program.Typed.World

def ReviewedStrongCause (StrongValue : TWorld → Ty → Val → Prop)
    (w : TWorld) (ty : Ty) (cause : CauseV) : Prop :=
  ∀ error ann, Reason.fail error ann ∈ cause.reasons →
    ∃ value, valOfErr error = some value ∧ StrongValue w ty value

def ReviewedStrongExit (StrongValue : TWorld → Ty → Val → Prop)
    (w : TWorld) (ty : EffTy) (ex : ExitV) : Prop :=
  CompletionOk w (ty.answer, ty.error) (.ofExit ex) ∧
    (∀ value, ex = .success value → StrongValue w ty.answer value) ∧
    (∀ cause, ex = .failure cause → ReviewedStrongCause StrongValue w ty.error cause)

/-- This holds for every possible stronger value predicate, so adding nested handle
checks cannot repair the claimed no-badShape consequence. -/
theorem bad_shape_still_admitted (StrongValue : TWorld → Ty → Val → Prop)
    (w : TWorld) (ty : EffTy) : ReviewedStrongExit StrongValue w ty badShapeExit := by
  refine ⟨rfl, ?_, ?_⟩
  · intro value h
    cases h
  · intro cause h error ann mem
    cases h
    change Reason.fail error ann ∈ [Reason.die Defect.badName ReasonAnnotations.empty] at mem
    simp only [List.mem_singleton] at mem
    cases mem

#print axioms bad_shape_still_admitted
end Test.Counterexamples.StrongExitDefect
