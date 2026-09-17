import Effect4.Program.CheckedTyping
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound

/-!
# Whole-program typing certificates retain exactly the existing checker

The executable certificate is a view of `typeOfProgram`, with no additional
acceptance or refusal. Uniqueness follows from the checker equation and proof
irrelevance. Its reference conditions are the checker's existing conditions;
`HasTy` applies to `expandRefs`, not to a claim about executing expanded programs.

Proof graph: the computed match gives erasure, acceptance and refusal; the existing
`effTy_sound`/`effTy_complete` connect that equation to the declarative judgment.
The final admission equation checks an existing runner certificate without changing
the order or meaning of any runner refusal.
-/

namespace Effect4.Program

variable {Op : Type} {sig : Signature Op} {program : Eff Op}

/-- Erasing evidence returns exactly the existing checker's result. -/
@[simp] theorem checkTypedProgram_type (sig : Signature Op) (program : Eff Op) :
    (checkTypedProgram sig program).map TypedProgram.ty = typeOfProgram sig program := by
  unfold checkTypedProgram
  split <;> simp_all

/-- Every returned certificate states the original whole-program typing equation. -/
theorem checkTypedProgram_sound {checked : TypedProgram sig program}
    (_ : checkTypedProgram sig program = some checked) :
    typeOfProgram sig program = some checked.ty :=
  checked.typed

/-- There is only one recorded type for a fixed program and signature. -/
theorem TypedProgram.type_unique (left right : TypedProgram sig program) :
    left.ty = right.ty :=
  Option.some.inj (left.typed.symm.trans right.typed)

/-- Certificates for the same checked input coincide, including their evidence fields. -/
theorem TypedProgram.unique (left right : TypedProgram sig program) : left = right := by
  have same := left.type_unique right
  cases left
  cases right
  cases same
  rfl

/-- Rechecking any completed certificate returns that same certificate. -/
theorem checkTypedProgram_eq_some (checked : TypedProgram sig program) :
    checkTypedProgram sig program = some checked := by
  unfold checkTypedProgram
  split
  · rename_i refused
    rw [checked.typed] at refused
    contradiction
  · congr 1
    exact TypedProgram.unique _ _

/-- Every successful result of the original checker is retained, at the same type. -/
theorem checkTypedProgram_complete {ty : EffTy}
    (h : typeOfProgram sig program = some ty) :
    ∃ checked, checkTypedProgram sig program = some checked ∧ checked.ty = ty :=
  ⟨⟨ty, h⟩, checkTypedProgram_eq_some ⟨ty, h⟩, rfl⟩

/-- Evidence packaging adds no refusal and removes no existing refusal. -/
theorem checkTypedProgram_refusal_iff :
    checkTypedProgram sig program = none ↔ typeOfProgram sig program = none := by
  unfold checkTypedProgram
  split <;> simp_all

/-- A completed whole-program check validates every stored layer reference. -/
theorem TypedProgram.layerRefsWF (checked : TypedProgram sig program) :
    program.layerRefsWF = true := by
  have typed := checked.typed
  unfold typeOfProgram at typed
  split at typed
  · rename_i admitted
    exact (Bool.and_eq_true_iff.mp admitted).1
  · contradiction

/-- The expanded tree used for typing has no remaining reference sites. -/
theorem TypedProgram.expanded_refSites (checked : TypedProgram sig program) :
    program.expandRefs.refSites [] = [] := by
  have typed := checked.typed
  unfold typeOfProgram at typed
  split at typed
  · rename_i admitted
    exact List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp admitted).2
  · contradiction

/-- The certificate's type derives from the existing whole-language typing rules on
the reference-expanded tree. This theorem makes no execution-expansion claim. -/
theorem TypedProgram.hasTy (checked : TypedProgram sig program) :
    Conform.Effect4.Typing.HasTy sig [] program.expandRefs checked.ty := by
  apply Conform.Effect4.Typing.effTy_sound
  have typed := checked.typed
  simpa [typeOfProgram, typeOf, checked.layerRefsWF, checked.expanded_refSites] using typed

/-- Conversely, the checker's exact reference conditions and the existing declarative
judgment produce a certificate; no codegen or execution restriction is needed. -/
theorem checkTypedProgram_of_hasTy {ty : EffTy}
    (references : program.layerRefsWF = true)
    (expanded : program.expandRefs.refSites [] = [])
    (typed : Conform.Effect4.Typing.HasTy sig [] program.expandRefs ty) :
    ∃ checked, checkTypedProgram sig program = some checked ∧ checked.ty = ty := by
  apply checkTypedProgram_complete
  simpa [typeOfProgram, typeOf, references, expanded] using
    (Conform.Effect4.Typing.effTy_complete sig program.expandRefs [] ty typed)

/-- A completed runner certificate passes the unchanged sequence of admission checks.
Its typing component is the same shared certificate used by other boundaries. -/
theorem admitProgram_eq_ok {program : NativeEff} {table : RowTable}
    (admitted : AdmittedProgram program table) :
    admitProgram program table = .ok admitted := by
  have tableFree := admitted.intFreeTable
  have programFree := admitted.intFreeProgram
  have typeFree := admitted.intFreeType
  have lawful := admitted.lawful
  have runnable := admitted.runnable
  have checked := checkTypedProgram_eq_some admitted.toTypedProgram
  unfold admitProgram
  split
  · simp_all
  · split
    · simp_all
    · split
      · simp_all
      · rename_i typing htyping
        have same : typing = admitted.toTypedProgram :=
          Option.some.inj (htyping.symm.trans checked)
        subst same
        split
        · simp_all
        · simp only [lawful, dite_true]
          split
          · simp_all
          · cases admitted
            rfl

end Effect4.Program
