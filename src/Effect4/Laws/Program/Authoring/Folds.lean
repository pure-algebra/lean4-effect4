import Effect4.Program.Authoring.Folds
import Effect4.Laws.Program.Authoring
import Effect4.Laws.Program.Author

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

/-- The hygienic fold keeps the scope judgment: the body's two arguments are scoped readers of
the minted binders. A step of the same scope rule, for the builders of the Queue's steps. -/
theorem foldWith_scoped {list init : TermSrc} {body : TermSrc → TermSrc → TermSrc}
    (accTy : Option Ty) (hl : list.Scoped) (hi : init.Scoped)
    (hb : ∀ acc item : TermSrc, acc.Scoped → item.Scoped → (body acc item).Scoped) :
    (foldWith list init body accTy).Scoped :=
  ⟨fun env path term accepted =>
    (fold_scoped (env.mint "acc") (env.mint "item") accTy hl hi
      (hb _ _ (minted_scoped _) (minted_scoped _))).holds env path term accepted⟩

/-- A variable an author wrote keeps its reading under two binders the surface minted: the two
names of a hygienic fold. `var_push_minted` once for each binder. Consumer: a builder that
places a caller's term in the body of `foldWith`. -/
theorem var_push_minted_pair {first second x : String} (h1 : Name.reserved first = true)
    (h2 : Name.reserved second = true) (hx : Name.reserved x = false) (env : Env)
    (p : List Nat) : var x (env.push [first, second]) p = var x env p := by
  have split : env.push [first, second] = (env.push [first]).push [second] := by
    unfold Env.push
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [split, var_push_minted h2 hx, var_push_minted h1 hx]

end Effect4.Program.Authoring
