import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Laws.Program.Authoring.Rows
import Effect4.Program.Authoring.Sugar

/-!
# Laws.Program.Authoring.Sugar — the hand-written surface preserves scope

`Program/Authoring/Sugar.lean` is the only hand-written part of the authoring surface (the
binders over a fresh name and the derived forms; the row wrappers and their lemmas are
generated, `Authoring/Rows.lean`). Each definition gets the same lemma the generated lifts carry,
named so `authoring_scoped` finds it, and each is one application of the lemmas of the
lifts it is made of. `elaborate_scoped` is the consequence for authors: a program that
elaborates is closed at level `0`.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

theorem bindWith_scoped {Op : Type} {first : Src Op} {rest : TermSrc → Src Op}
    (h0 : first.Scoped) (h1 : ∀ r : TermSrc, r.Scoped → (rest r).Scoped) :
    (bindWith first rest).Scoped :=
  ⟨fun env p e h => (bind_scoped _ h0 (h1 _ (var_scoped _))).holds env p e h⟩

theorem bindName_scoped {Op : Type} (name : String) {first : Src Op} {rest : TermSrc → Src Op}
    (h0 : first.Scoped) (h1 : ∀ r : TermSrc, r.Scoped → (rest r).Scoped) :
    (bindName name first rest).Scoped :=
  ⟨fun env p e h => (bind_scoped name h0 (h1 _ (var_scoped name))).holds env p e h⟩

theorem OfNat.ofNat_scoped {n : Nat} : (OfNat.ofNat n : TermSrc).Scoped := nat_scoped n

theorem ite_scoped {Op : Type} (c : Prop) [Decidable c] {t e : Src Op}
    (ht : t.Scoped) (he : e.Scoped) : (if c then t else e).Scoped :=
  if h : c then by rw [if_pos h]; exact ht else by rw [if_neg h]; exact he

theorem flatMap_scoped {Op : Type} (answer : String) {first rest : Src Op}
    (h0 : first.Scoped) (h1 : rest.Scoped) : (flatMap answer first rest).Scoped :=
  bind_scoped answer h0 h1

theorem andThen_scoped {Op : Type} {first rest : Src Op} (h0 : first.Scoped) (h1 : rest.Scoped) :
    (andThen first rest).Scoped :=
  bind_scoped _ h0 h1

theorem map_scoped {Op : Type} (atom : String) {effect : Src Op} (h : effect.Scoped) :
    (map atom effect).Scoped :=
  bindWith_scoped h fun _ hr =>
    succeed_scoped (app_scoped atom (TermSrc.Scoped_cons hr TermSrc.Scoped_nil))

theorem ifElse_scoped {Op : Type} {test : TermSrc} {thenB elseB : Src Op}
    (h0 : test.Scoped) (h1 : thenB.Scoped) (h2 : elseB.Scoped) :
    (ifElse test thenB elseB).Scoped :=
  selectBool_scoped h0 h1 h2

/-- Scope safety by construction: a program that elaborates is closed at level `0`. -/
theorem elaborate_scoped {Op : Type} {src : Src Op} (h : src.Scoped) {e : Eff Op}
    (he : elaborate src = .ok e) : Eff.scopedAt 0 e = true :=
  h.holds {} [] e he

end Effect4.Program.Authoring
