import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Program.Authoring.Loops

/-!
# Laws.Program.Authoring.Loops — the loop sugar preserves scope

Each definition of `Program/Authoring/Loops.lean` gets the lemma the generated lifts carry, named
so `authoring_scoped` finds it. `iterateWith_scoped` is `bindWith_scoped`'s shape over
`iterate_scoped`; the rest are one application of it.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

theorem iterateWith_scoped {Op : Type} {initial : TermSrc} {spec : LoopSpec Op}
    (h0 : initial.Scoped)
    (hw : ∀ c : TermSrc, c.Scoped → (spec.while_ c).Scoped)
    (hb : ∀ c : TermSrc, c.Scoped → (spec.body c).Scoped)
    (hs : ∀ c a : TermSrc, c.Scoped → a.Scoped → (spec.step c a).Scoped)
    (hr : ∀ c : TermSrc, c.Scoped → (spec.result c).Scoped) :
    (iterateWith initial spec).Scoped :=
  ⟨fun env p e h =>
    (iterate_scoped _ _ spec.cursorTy h0 (hw _ (var_scoped _))
      (hs _ _ (var_scoped _) (var_scoped _)) (hr _ (var_scoped _)) (hb _ (var_scoped _))).holds
      env p e h⟩

theorem forRange_scoped {Op : Type} {lo hi : TermSrc} {body : TermSrc → Src Op}
    (h0 : lo.Scoped) (h1 : hi.Scoped) (h2 : ∀ i : TermSrc, i.Scoped → (body i).Scoped) :
    (forRange lo hi body).Scoped :=
  iterateWith_scoped h0
    (fun _ hc => app_scoped "lt" (TermSrc.Scoped_cons hc (TermSrc.Scoped_cons h1 TermSrc.Scoped_nil)))
    h2
    (fun _ _ hc _ => app_scoped "succ" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))
    (fun _ hc => hc)

theorem foldRange_scoped {Op : Type} {lo hi zero : TermSrc} {f : TermSrc → TermSrc → Src Op}
    (h0 : lo.Scoped) (h1 : hi.Scoped) (h2 : zero.Scoped)
    (h3 : ∀ i acc : TermSrc, i.Scoped → acc.Scoped → (f i acc).Scoped) :
    (foldRange lo hi zero f).Scoped :=
  have one {atom : String} {x : TermSrc} (hx : x.Scoped) : (app atom [x]).Scoped :=
    app_scoped atom (TermSrc.Scoped_cons hx TermSrc.Scoped_nil)
  have two {atom : String} {x y : TermSrc} (hx : x.Scoped) (hy : y.Scoped) :
      (app atom [x, y]).Scoped :=
    app_scoped atom (TermSrc.Scoped_cons hx (TermSrc.Scoped_cons hy TermSrc.Scoped_nil))
  iterateWith_scoped (two h0 h2)
    (fun _ hc => two (one hc) h1)
    (fun _ hc => h3 _ _ (one hc) (one hc))
    (fun _ _ hc ha => two (one (one hc)) ha)
    (fun _ hc => one hc)

theorem repeatWhile_scoped {Op : Type} {cond body : Src Op} (h0 : cond.Scoped)
    (h1 : body.Scoped) : (repeatWhile cond body).Scoped :=
  bindWith_scoped h0 fun _ hfirst =>
    iterateWith_scoped hfirst (fun _ hc => hc) (fun _ _ => andThen_scoped h1 h0)
      (fun _ _ _ ha => ha) (fun _ _ => unit_scoped)

end Effect4.Program.Authoring
