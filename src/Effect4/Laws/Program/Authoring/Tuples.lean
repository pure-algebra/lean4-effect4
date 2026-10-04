import Effect4.Program.Authoring.Tuples
import Effect4.Laws.Program.Authoring

/-! Tuple builders retain the existing authoring scope judgment.
These helpers serve `denote-typed` through scoped authored programs.
They establish no typing or bounds judgment. -/

namespace Effect4.Program.Authoring

/-- Each tuple item is resolved in the same current scope. -/
theorem tuple_scoped {items : List TermSrc} (h : ∀ item ∈ items, item.Scoped) :
    (tuple items).Scoped := app_scoped "tuple" h

/-- A static index introduces no variable or binder. -/
theorem tupleAt_scoped {target : TermSrc} (h : target.Scoped) (index : Nat) :
    (tupleAt target index).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold tupleAt at accepted
  obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
  cases accepted
  exact h.holds env path value resolved

end Effect4.Program.Authoring
