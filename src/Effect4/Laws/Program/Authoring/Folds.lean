import Effect4.Program.Authoring.Folds
import Effect4.Laws.Program.Authoring

/-! The fold's builder retains the existing authoring scope judgment (decisions row 228).
This is the scope rule of `fold-typed-atomic-update` (R4) at the surface an author writes.
Its consumer is a scoped authored program whose term folds, the Queue's service pass first.
It establishes no typing. -/

namespace Effect4.Program.Authoring

/-- The list and the initial value are scoped at the term's scope, and the body two levels up,
under the two names the fold binds. -/
theorem fold_scoped (acc item : String) (accTy : Option Ty) {list init body : TermSrc}
    (hl : list.Scoped) (hi : init.Scoped) (hb : body.Scoped) :
    (fold acc item accTy list init body).Scoped := by
  refine ⟨fun env path term accepted => ?_⟩
  unfold fold at accepted
  obtain ⟨listTerm, hlist, accepted⟩ := bind_ok accepted
  obtain ⟨initTerm, hinit, accepted⟩ := bind_ok accepted
  obtain ⟨bodyTerm, hbody, accepted⟩ := bind_ok accepted
  cases accepted
  have sb := hb.holds _ _ _ hbody
  simp only [Env.push_length, List.length_cons, List.length_nil] at sb
  simp only [Term.scoped, Bool.and_eq_true]
  exact ⟨⟨hl.holds _ _ _ hlist, hi.holds _ _ _ hinit⟩, sb⟩

end Effect4.Program.Authoring
