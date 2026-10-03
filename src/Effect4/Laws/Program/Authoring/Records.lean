import Effect4.Program.Authoring.Records
import Effect4.Laws.Program.Authoring

/-! Scope compatibility for the record authoring builders (decisions row 195).
These are steps of the existing authoring scope judgment, consumed by record programs.
They certify resolved variables only; formation and typing remain separate checks. -/

namespace Effect4.Program.Authoring

/-- Each supplied source keeps its scope; metadata introduces no variable. -/
theorem record_scoped (fields : List (String × Bool × Ty)) {present : List (String × TermSrc)}
    (scopeProof : ∀ entry ∈ present, entry.2.Scoped) : (record fields present).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold record at accepted
  obtain ⟨values, elaborated, accepted⟩ := bind_ok accepted
  cases accepted
  simp only [Term.scoped]
  apply termsOfList_scoped
  intro value member
  obtain ⟨entry, member, resolved⟩ := mapM_ok_mem elaborated value member
  exact (scopeProof entry member).holds env path value resolved

/-- Required field access retains the target's resolved scope. -/
theorem field_scoped {target : TermSrc} (scopeProof : target.Scoped) (name : String) :
    (field target name).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold field at accepted
  obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
  cases accepted
  exact scopeProof.holds env path value resolved

/-- Optional access changes the stored mode, without changing variable scope. -/
theorem optionalField_scoped {target : TermSrc} (scopeProof : target.Scoped) (name : String) :
    (optionalField target name).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold optionalField at accepted
  obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
  cases accepted
  exact scopeProof.holds env path value resolved

/-- An overwrite resolves both children under the same scope. -/
theorem recordSet_scoped {target replacement : TermSrc}
    (targetScoped : target.Scoped) (replacementScoped : replacement.Scoped) (name : String) :
    (recordSet target name replacement).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold recordSet at accepted
  obtain ⟨value, targetResolved, accepted⟩ := bind_ok accepted
  obtain ⟨next, replacementResolved, accepted⟩ := bind_ok accepted
  cases accepted
  simp only [Term.scoped, Bool.and_eq_true]
  exact ⟨targetScoped.holds env path value targetResolved,
    replacementScoped.holds env path next replacementResolved⟩

end Effect4.Program.Authoring
