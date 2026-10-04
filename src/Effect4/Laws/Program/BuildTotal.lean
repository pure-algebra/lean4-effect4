import Effect4.Laws.Program.Provision
import Effect4.Laws.Program.Typing.Sound

/-!
# Laws.Program.BuildTotal — a well-typed layer builds (R5, decisions row 147)

`build` (`Program/Provision.lean`) is the specification of provisioning: structural over the
layer combinators, with the leaves interpreted by a supplied `LeafSem`. Its totality theorem was
cut as unused at `b08f3b58`; decisions row 147 owes its restoration under R5. This module restores
it against the typing judgment as it stands since the join:

* `LeafSem.Typed`: the trusted-boundary premise. A leaf whose body types at the empty environment
  builds under any context that satisfies the body's scope-free row (`bodyRequires`).
* `build_total_of_hasTy` and `buildAll_total_of_hasTy`: by structural recursion on the
  `LayerHasTy` and `LayersHasTy` derivations, a well-typed layer builds under every context that
  satisfies its requirement row, and the built context satisfies its output row.
* `build_total`: the same from the checker's answer (`layerTy`, through `layerTy_sound`), the
  statement that was cut.

A layer that types holds no reference: `LayerHasTy` has no rule for `LayerTerm.ref`, which the
whole program resolves. So the restoration needs no reference premise.

Placement (`AGENTS.md`): concept `context-requirements`, claim `build-total`. Reach: the
structural specification `build`, at any signature, for every supplied typed leaf semantics. It
does not establish that the machine's build of a layer (`Eff.provideLayer`, run by the frame
machine) refines `build`: that is `lower_refines_build`, row 147's other half. The leaf
semantics' typedness is a premise, the boundary `ServiceUniverse` and `RunInterp` also occupy.
Scopes, finalizers and memoization are outside `build`. It serves R5 (services) and unlocks, with
`lower_refines_build`, the service half of R5.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement Ctx Context)
open Conform.Effect4.Typing (HasTy LayerHasTy LayersHasTy layerTy_sound)

/-- A leaf semantics is typed at a signature when every leaf whose body types at the empty
environment builds under every context that satisfies the body's scope-free row. -/
structure LeafSem.Typed {Op : Type} (sig : Signature Op) (sem : LeafSem Op) : Prop where
  effect : ∀ (key : ServiceKey) (body : Eff Op) (ctx : Ctx) (t : EffTy),
    HasTy sig [] body t → ctx.Satisfies (bodyRequires sig t) →
      (sem.effect key body ctx).isSome = true
  discard : ∀ (body : Eff Op) (ctx : Ctx) (t : EffTy),
    HasTy sig [] body t → ctx.Satisfies (bodyRequires sig t) →
      (sem.discard body ctx).isSome = true

/-- The dependency of a `provide` or `provideMerge` builds under the requirement the dependent
leaves to it, and the dependent then builds under the merged context. -/
private theorem merged_satisfies {ctx d : Ctx} {s t : LayerTy}
    (hsat : ctx.Satisfies (Row.union (Row.diff s.requires t.out) t.requires))
    (hd : d.Satisfies t.out) : (ctx.merge d).Satisfies s.requires := by
  intro key hk
  by_cases hout : key ∈ t.out
  · exact satisfies_merge_right ctx d t.out hd key hout
  · have hk' : key ∈ Row.union (Row.diff s.requires t.out) t.requires :=
      (Row.mem_union key _ _).mpr (Or.inl ((Row.mem_diff key _ _).mpr ⟨hk, hout⟩))
    exact satisfies_merge_left ctx d _ hsat key hk'

mutual
/-- **Build totality, on derivations.** Under a typed leaf semantics, a layer with a typing
derivation builds under every context that satisfies its requirement row, and the built context
satisfies its output row. -/
theorem build_total_of_hasTy {Op : Type} {sig : Signature Op} {sem : LeafSem Op}
    (hsem : sem.Typed sig) : ∀ {l : LayerTerm Op} {t : LayerTy}, LayerHasTy sig l t →
      ∀ ctx : Ctx, ctx.Satisfies t.requires →
        ∃ out, build sem l ctx = some out ∧ out.Satisfies t.out
  | _, _, .succeed (key := key) (v := v) hv _ _, _, _ =>
    ⟨Context.empty.addV key v, by simp only [build, hv, Option.map_some],
      satisfies_single_addV key v⟩
  | _, _, .effect (key := key) (body := body) (t := tb) hbody _ _, ctx, hsat => by
    have hs := hsem.effect key body ctx tb hbody hsat
    cases hv : sem.effect key body ctx with
    | none => rw [hv] at hs; exact Bool.noConfusion hs
    | some v =>
      exact ⟨Context.empty.addV key v, by simp only [build, hv, Option.map_some],
        satisfies_single_addV key v⟩
  | _, _, .effectDiscard (body := body) (t := tb) hbody, ctx, hsat => by
    have hs := hsem.discard body ctx tb hbody hsat
    cases hv : sem.discard body ctx with
    | none => rw [hv] at hs; exact Bool.noConfusion hs
    | some _ =>
      exact ⟨Context.empty, by simp only [build, hv, Option.map_some],
        Context.satisfies_empty _⟩
  | _, _, .provide (s := s) (t := t) hs ht, ctx, hsat => by
    obtain ⟨d, hdb, hdout⟩ := build_total_of_hasTy hsem ht ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
    obtain ⟨out, hsb, hsout⟩ := build_total_of_hasTy hsem hs (ctx.merge d)
      (merged_satisfies hsat hdout)
    exact ⟨out, by simp only [build, hdb, hsb, Option.bind_eq_bind, Option.bind_some], hsout⟩
  | _, _, .provideMerge (s := s) (t := t) hs ht, ctx, hsat => by
    obtain ⟨d, hdb, hdout⟩ := build_total_of_hasTy hsem ht ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
    obtain ⟨out, hsb, hsout⟩ := build_total_of_hasTy hsem hs (ctx.merge d)
      (merged_satisfies hsat hdout)
    exact ⟨d.merge out, by simp only [build, hdb, hsb, Option.bind_eq_bind, Option.bind_some],
      satisfies_union_of _ _ _ (satisfies_merge_right d out _ hsout)
        (satisfies_merge_left d out _ hdout)⟩
  | _, _, .merge (a := a) (b := b) ha hb, ctx, hsat => by
    obtain ⟨actx, hab, haout⟩ := build_total_of_hasTy hsem ha ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_left _ _))
    obtain ⟨bctx, hbb, hbout⟩ := build_total_of_hasTy hsem hb ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
    exact ⟨actx.merge bctx, by simp only [build, hab, hbb, Option.bind_eq_bind, Option.bind_some],
      satisfies_union_of _ _ _ (satisfies_merge_left actx bctx _ haout)
        (satisfies_merge_right actx bctx _ hbout)⟩
  | _, _, .fresh hi, ctx, hsat => by
    obtain ⟨out, hb, hout⟩ := build_total_of_hasTy hsem hi ctx hsat
    exact ⟨out, by simp only [build, hb], hout⟩
  | _, _, .orDie hi, ctx, hsat => by
    obtain ⟨out, hb, hout⟩ := build_total_of_hasTy hsem hi ctx hsat
    exact ⟨out, by simp only [build, hb], hout⟩
  | _, _, .mergeAll hls, ctx, hsat => by
    obtain ⟨out, hb, hout⟩ := buildAll_total_of_hasTy hsem hls ctx hsat
    exact ⟨out, by simp only [build, hb], hout⟩

/-- **Build totality of a `mergeAll` spine**, on derivations: the siblings build under the same
context and their right-biased merge satisfies the union of their outputs. -/
theorem buildAll_total_of_hasTy {Op : Type} {sig : Signature Op} {sem : LeafSem Op}
    (hsem : sem.Typed sig) : ∀ {ls : LayerTerms Op} {t : LayerTy}, LayersHasTy sig ls t →
      ∀ ctx : Ctx, ctx.Satisfies t.requires →
        ∃ out, buildAll sem ls ctx = some out ∧ out.Satisfies t.out
  | _, _, .one hh, ctx, hsat => by
    obtain ⟨out, hb, hout⟩ := build_total_of_hasTy hsem hh ctx hsat
    exact ⟨out, by simp only [buildAll, hb], hout⟩
  | _, _, .cons hh hrest, ctx, hsat => by
    obtain ⟨a, hab, haout⟩ := build_total_of_hasTy hsem hh ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_left _ _))
    obtain ⟨b, hbb, hbout⟩ := buildAll_total_of_hasTy hsem hrest ctx
      (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
    exact ⟨a.merge b, by simp only [buildAll, hab, hbb, Option.bind_eq_bind, Option.bind_some],
      satisfies_union_of _ _ _ (satisfies_merge_left a b _ haout)
        (satisfies_merge_right a b _ hbout)⟩
end

/-- **Build totality** (`build_total`, cut at `b08f3b58`, restored under decisions row 147):
under a typed leaf semantics, a layer the checker types builds under every context that satisfies
its requirement row, and the built context satisfies its output row. -/
theorem build_total {Op : Type} (sig : Signature Op) (sem : LeafSem Op) (hsem : sem.Typed sig)
    (l : LayerTerm Op) (t : LayerTy) (ctx : Ctx) (ht : layerTy sig l = some t)
    (hsat : ctx.Satisfies t.requires) :
    ∃ out, build sem l ctx = some out ∧ out.Satisfies t.out :=
  build_total_of_hasTy hsem (layerTy_sound sig l t ht) ctx hsat

end Effect4.Program.Provision
