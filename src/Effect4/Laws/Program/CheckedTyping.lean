import Effect4.Program.CheckedTyping
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Definitions

/-!
# Whole-program typing certificates retain exactly the existing checker

The executable certificate is a view of `typeOfProgram`, with no additional
acceptance or refusal. Uniqueness follows from the checker equation and proof
irrelevance. Its reference condition is the checker's one test: the references are well
formed (`TypedProgram.layerRefsWF`). The expansion then has no reference site by a theorem,
not by a test (`TypedProgram.expanded_refSites`, from `expanded_refs_nil_of_wf`).
`HasTy` applies to `expandRefs`, not to a claim about executing expanded programs.

Proof graph: the computed match gives erasure, acceptance and refusal; the module check's
`checkModule_sound`/`checkModule_complete` connect that equation to the declarative judgment.
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

/-- A completed whole-program check validates every stored layer reference. The checker
answers only where the references are well formed, and it makes no other test of them. -/
theorem TypedProgram.layerRefsWF (checked : TypedProgram sig program) :
    program.layerRefsWF = true := by
  have typed := checked.typed
  unfold typeOfProgram at typed
  split at typed
  · rename_i admitted
    exact admitted
  · contradiction

/-- The expanded tree used for typing has no remaining reference sites. The checker does not
test it: the certificate's references are well formed (`TypedProgram.layerRefsWF`), and such a
program expands to a program with no reference site (`expanded_refs_nil_of_wf`,
`Laws/Program/ReferenceExpansion.lean`). -/
theorem TypedProgram.expanded_refSites (checked : TypedProgram sig program) :
    program.expandRefs.refSites [] = [] :=
  expanded_refs_nil_of_wf program checked.layerRefsWF

/-- The certificate's type derives from the whole-language typing rules on the
reference-expanded tree: the module judgment (`ModuleHasTy`, decisions row 328), which is the
program judgment `HasTy` for a program with no block. This theorem makes no
execution-expansion claim. -/
theorem TypedProgram.hasTy (checked : TypedProgram sig program) :
    ModuleHasTy sig program.expandRefs checked.ty := by
  have typed := checked.typed
  rw [typeOfProgram_eq_if_refsWF, if_pos checked.layerRefsWF] at typed
  exact checkModule_sound sig _ _ (Effect4.Laws.Auto.toOption_eq_some.mp typed)

/-- Conversely, well-formed references and the existing declarative judgment on the expanded
tree produce a certificate; no codegen or execution restriction is needed. The caller owes no
fact about the expansion's reference sites: the checker tests the references' formation only
(`typeOfProgram_eq_if_refsWF`, `Laws/Program/ReferenceTyping.lean`). The theorem makes no claim
about executing the expanded tree. -/
theorem checkTypedProgram_of_hasTy {ty : EffTy}
    (references : program.layerRefsWF = true)
    (typed : ModuleHasTy sig program.expandRefs ty) :
    ∃ checked, checkTypedProgram sig program = some checked ∧ checked.ty = ty := by
  apply checkTypedProgram_complete
  rw [typeOfProgram_eq_if_refsWF, if_pos references, checkModule_complete sig _ ty typed]
  rfl

/-- A completed runner certificate passes every retained admission check.
Its typing component is the same shared certificate used by other boundaries. -/
theorem admitProgram_eq_ok {program : NativeEff} {app : SigApp}
    (admitted : AdmittedProgram program app) :
    admitProgram program app = .ok admitted := by
  unfold admitProgram
  split
  · rename_i why hwhy
    rw [admitted.signature] at hwhy
    contradiction
  · split
    · rename_i why refused
      rw [(Formation.checkInput_eq_none_iff program app.rows app.services).mpr
        admitted.formed] at refused
      cases refused
    · rw [checkTypedProgram_eq_some admitted.toTypedProgram]
      dsimp only
      split
      · rename_i pos hpos
        rw [admitted.columnsType] at hpos
        contradiction
      · cases admitted
        rfl

end Effect4.Program
