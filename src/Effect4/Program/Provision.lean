import Effect4.Program.Typing
import Effect4.Program.Compile

/-!
# Provision — the requirement algebra, the layer signature, and the layer term

Landed 2026-09-04 from the `workshop/Provision` spike. Plan and grill:
`docs/research/2026-09-04-provision-algebra.md`; battery `Test/Program/ProvisionContract.lean`.

What this module adds to the tree, and what it deliberately reuses:

* **Reused, never re-declared.** `Requirement := Row ServiceKey` and the eleven context
  laws (`src/Effect4/Machine/Context.lean`), `Ty`/`EffTy`/`typeOf` and, since the join
  (2026-09-07), `LayerTy`/`LayerTerm`/`layerTy` themselves (`src/Effect4/Program/Typing.lean`,
  `Eff.lean`: a layer is a subterm of the program that provides it), and the compile route
  that builds one at its point (`src/Effect4/Program/Compile.lean`). The machine is the
  semantics; this module is the *typed face* over it and the *specification* it refines.
* **`Row.diff`** (`src/Effect4/Data/Row.lean`, landed with this module). `Exclude<R, ROut>`
  is set difference, and `Layer.provide`'s requirement row is `RIn | Exclude<RIn2, ROut>`
  (`vendor/effect-4.0.0-rc.112/src/Layer.ts:2089`); every law below is a membership law
  over `mem_diff` and `mem_union`.
* **`LayerTy`, the signature `Layer<ROut, E, RIn>`** (`Layer.ts:54`), and the *provision
  algebra*: `provide`, `provideMerge`, `merge` and `orDie` as operations on signatures, with
  the laws rc.112 states only as TypeScript types. `LayerTy.provide` is
  `HttpApiMiddleware.ApplyServices` (`unstable/httpapi/HttpApiMiddleware.ts:199`) read as
  a function on rows — the same rule types a middleware and a layer.
* **`LayerTerm`, the first-order layer language**, one constructor per rc.112 export the
  corpus uses (`succeed`, `effect`, `effectDiscard`, `provide`, `provideMerge`, `merge`,
  `fresh`, `orDie`, and since the host rows slice `ref` and the n-ary `mergeAll`), with `layerTy` its typing and
  `Eff` bodies at the `effect` leaves — the same `Eff` the printer prints and the
  compile compiles; both live in `Program/Eff.lean` and `Program/Typing.lean` since the
  join. Nothing here is a closure; `DecidableEq` throughout.
* **`App`** — `Effect.provide(program, layer)` (`internal/layer.ts:8-22`) — and the
  theorem that its requirement row is empty exactly when the layer closes the program.
* **`build`, the specification of provisioning**, structural over the combinators with the
  leaves supplied as a `LeafSem` hook (the trusted-boundary position `ServiceUniverse` and
  `RunInterp` already occupy), and `build_total`: *a well-typed layer builds under every
  context that satisfies its requirement row, and what it builds satisfies its output row*.
  That sentence is what "the `R` channel guarantees the wiring" means, and it is proved once
  over the algebra, for every leaf semantics that is honest about its own leaves.
* **The machine half, on the compile route.** `Effect.provide(self, layer)` is a program
  (`Eff.provideLayer`), so the witnesses are runs: `buildServices`, `buildSucceeds` and
  `provideThenService` run native programs through `runSyncExit` at `interpOf` and pin, by
  `#guard`, that the produced context has the keys `build` predicts — a refinement mapping
  in Lamport's sense (`keysRow` of the fiber context the body reads), checked on finite
  probes here and stated as an owed theorem in the plan. Before the join a term lowered into
  the Layer machine's table (`lower`, `runOver`, retired with it).

Every rc.112 line named below is in `vendor/effect-4.0.0-rc.112/src/`.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision

open Effect4
open Effect4.Machine.Env (Requirement Ctx Context Service decode encode scopeKey natOfVal
  rightBiased)

/-! ## The signature: `Layer<ROut, E, RIn>` (`Layer.ts:54`)

`LayerTy` and its four operations live in `Program/Typing.lean` since the join (2026-09-07):
`typeOf` of `Eff.provideLayer` reads them. Their laws stay here. -/

namespace LayerTy

/-! ### The provision algebra — the laws rc.112 states only as TypeScript types -/

/-- `provide` keeps exactly the dependent's outputs. -/
theorem provide_out (s t : LayerTy) : (s.provide t).out = s.out := rfl

/-- `provideMerge` keeps both output rows. -/
theorem provideMerge_out (s t : LayerTy) : (s.provideMerge t).out = Row.union s.out t.out := rfl

/-- Providing never adds a requirement neither operand had: weakening for `provide`. -/
theorem provide_requires_subset (s t : LayerTy) :
    Row.Subset (s.provide t).requires (Row.union s.requires t.requires) := by
  intro a ha
  have ha : a ∈ Row.union (Row.diff s.requires t.out) t.requires := ha
  rw [Row.mem_union] at ha ⊢
  rcases ha with hd | ht
  · exact Or.inl ((Row.mem_diff a _ _).mp hd).1
  · exact Or.inr ht

/-- A requirement of the dependent that the dependency provides is discharged. -/
theorem provide_discharges (s t : LayerTy) (key : ServiceKey) (hout : key ∈ t.out)
    (hreq : key ∉ t.requires) : key ∉ (s.provide t).requires := by
  intro h
  have h : key ∈ Row.union (Row.diff s.requires t.out) t.requires := h
  rw [Row.mem_union] at h
  rcases h with hd | ht
  · exact ((Row.mem_diff key _ _).mp hd).2 hout
  · exact hreq ht

/-- **The closure theorem.** A dependency that is itself closed and provides everything the
dependent needs closes the dependent: `Layer<ROut, E, never>`. This is the sentence
`Effect.provide(program, layer)` type-checks by, and the sentence a deployment is checked by. -/
theorem provide_closed (s t : LayerTy) (hclosed : t.Closed)
    (hcovers : Row.Subset s.requires t.out) : (s.provide t).Closed := by
  have hc : t.requires = Requirement.empty := hclosed
  show Row.union (Row.diff s.requires t.out) t.requires = Requirement.empty
  rw [(Row.diff_eq_empty_iff_subset s.requires t.out).mpr hcovers, hc]
  exact Row.union_empty_left _

/-- The converse direction of the closure theorem, member by member: a closed `provide` means
the dependency covered every dependent requirement. -/
theorem covers_of_provide_closed (s t : LayerTy) (h : (s.provide t).Closed) (key : ServiceKey)
    (hs : key ∈ s.requires) : key ∈ t.out := by
  by_cases hout : key ∈ t.out
  · exact hout
  · exfalso
    have hc : (s.provide t).requires = Requirement.empty := h
    have hm : key ∈ (s.provide t).requires :=
      (Row.mem_union key _ _).mpr (Or.inl ((Row.mem_diff key _ _).mpr ⟨hs, hout⟩))
    rw [hc] at hm
    exact Row.not_mem_empty key hm

/-- **Provide is associative up to `provideMerge`**, on the rows: providing two dependencies
one after the other is providing their `provideMerge` at once. This is the algebraic content
of "wire the dependencies in any grouping"; the error column is `Ty.join`, whose
associativity is an owed row of the type language, so the statement is over `out` and
`requires`. -/
theorem provide_provide_rows (l d₁ d₂ : LayerTy) :
    ((l.provide d₁).provide d₂).out = (l.provide (d₁.provideMerge d₂)).out ∧
      ((l.provide d₁).provide d₂).requires = (l.provide (d₁.provideMerge d₂)).requires := by
  refine ⟨rfl, ?_⟩
  apply Row.eq_of_mem_iff
  intro a
  simp only [LayerTy.provide, LayerTy.provideMerge, Row.mem_union, Row.mem_diff, not_or]
  by_cases hL : a ∈ l.requires <;> by_cases hO₁ : a ∈ d₁.out <;> by_cases hO₂ : a ∈ d₂.out <;>
    by_cases hR₁ : a ∈ d₁.requires <;> by_cases hR₂ : a ∈ d₂.requires <;>
    simp [hL, hO₁, hO₂, hR₁, hR₂]

/-- `merge` is commutative on the rows. What is *not* commutative is the built context
(`src/Effect4/Machine/Context.lean`, counterexample CE 5: `merge` is right-biased), and the
witnesses below exhibit two layers with this same signature that build different contexts.
The type does not see provider order; the run does. -/
theorem merge_rows_comm (a b : LayerTy) :
    (a.merge b).out = (b.merge a).out ∧ (a.merge b).requires = (b.merge a).requires :=
  ⟨Row.union_comm _ _, Row.union_comm _ _⟩

/-- `merge` provides nothing to its siblings: a requirement of either operand survives. -/
theorem merge_requires (a b : LayerTy) (key : ServiceKey)
    (h : key ∈ a.requires ∨ key ∈ b.requires) : key ∈ (a.merge b).requires :=
  (Row.mem_union key _ _).mpr h

/-- Providing is antitone in the dependency's outputs: a dependency that provides more
leaves fewer requirements. -/
theorem provide_requires_antitone_out (s t t' : LayerTy) (hout : Row.Subset t.out t'.out)
    (hreq : t'.requires = t.requires) :
    Row.Subset (s.provide t').requires (s.provide t).requires := by
  intro a ha
  have ha : a ∈ Row.union (Row.diff s.requires t'.out) t'.requires := ha
  show a ∈ Row.union (Row.diff s.requires t.out) t.requires
  rw [Row.mem_union] at ha ⊢
  rcases ha with hd | ht
  · exact Or.inl (Row.diff_subset_diff_right s.requires hout a hd)
  · rw [hreq] at ht
    exact Or.inr ht

end LayerTy

/-! ## The adjunction between contexts and requirement rows

`Satisfies` is inclusion into `keysRow`: a context satisfies exactly the subrows of its own
key row. This is the whole content of "what a context can provide", and it is what turns
the eleven context laws into laws of the provision algebra. -/

theorem satisfies_iff_subset_keysRow (ctx : Ctx) (r : Requirement) :
    ctx.Satisfies r ↔ Row.Subset r ctx.keysRow := by
  constructor
  · intro h key hk
    show key ∈ Row.normalize (ctx.entries.map Service.key)
    rw [Row.mem_normalize]
    exact (Context.lookup_isSome_iff_mem key ctx.entries).mp (h key hk)
  · intro h key hk
    have hm : key ∈ Row.normalize (ctx.entries.map Service.key) := h key hk
    rw [Row.mem_normalize] at hm
    exact (Context.lookup_isSome_iff_mem key ctx.entries).mpr hm

/-- `rightBiased` answers when either operand does. -/
theorem rightBiased_isSome {A : Type} (x y : Option A) :
    (rightBiased x y).isSome = (x.isSome || y.isSome) := by
  cases x <;> cases y <;> rfl

/-- A merge satisfies what its left operand satisfies (`get?_merge`). -/
theorem satisfies_merge_left (a b : Ctx) (r : Requirement) (h : a.Satisfies r) :
    (a.merge b).Satisfies r := by
  intro key hk
  rw [Context.get?_merge, rightBiased_isSome, h key hk]
  exact Bool.or_true _

/-- A merge satisfies what its right operand satisfies. -/
theorem satisfies_merge_right (a b : Ctx) (r : Requirement) (h : b.Satisfies r) :
    (a.merge b).Satisfies r := by
  intro key hk
  rw [Context.get?_merge, rightBiased_isSome, h key hk]
  rfl

/-- A context satisfies the union of two rows it satisfies. -/
theorem satisfies_union_of (ctx : Ctx) (r s : Requirement) (hr : ctx.Satisfies r)
    (hs : ctx.Satisfies s) : ctx.Satisfies (Row.union r s) :=
  (Context.satisfies_union ctx r s).mpr ⟨hr, hs⟩

/-- `Context.empty.addV key v` satisfies the singleton row at `key`. -/
theorem satisfies_single_addV (key : ServiceKey) (v : Effect4.Machine.Env.Val) :
    ((Context.empty : Ctx).addV key v).Satisfies (Requirement.single key) := by
  intro key' hk
  have e : key' = key := (Row.mem_singleton key key').mp hk
  subst e
  show (((Context.empty : Ctx).addV key' v).getV key').isSome = true
  rw [Context.getV_addV_same]
  rfl

/-! ## The layer language

`LayerTerm` is a member of the program family since the join (`Program/Eff.lean`: a layer is
a subterm of the program that provides it, and its build runs at its point), and `layerTy`,
`bodyRequires`, `litVal` and `WellTypedLayer` type it beside `typeOf` (`Program/Typing.lean`).
This module keeps the algebra's laws, the specification `build` and its totality, and the
docs deployment the laws are shown on. -/

/-! ## `App` — `Effect.provide(program, layer)` (`internal/layer.ts:8-22`) -/

/-- A program with the layer that is to provide it. -/
structure App (Op : Type) where
  layer : LayerTerm Op
  program : Eff Op
deriving DecidableEq

/-- `Effect<A, E | E2, RIn | Exclude<R, ROut>>` (`internal/layer.ts:14`). -/
def appTy {Op : Type} (sig : Signature Op) (app : App Op) : Option EffTy := do
  let l ← layerTy sig app.layer
  let p ← typeOf sig app.program
  some ⟨p.answer, p.error.join l.error, Row.union l.requires (Row.diff p.requires l.out)⟩

/-- The requirement row of an app whose halves type. -/
theorem appTy_requires {Op : Type} (sig : Signature Op) (app : App Op) (l : LayerTy) (p : EffTy)
    (hl : layerTy sig app.layer = some l) (hp : typeOf sig app.program = some p) :
    (appTy sig app).map EffTy.requires =
      some (Row.union l.requires (Row.diff p.requires l.out)) := by
  simp [appTy, hl, hp]

/-- **An app is closed exactly when its layer is closed and covers the program.** The
right-hand side is what a deployment checks; the left-hand side is what `printDecl`
(`src/Effect4/Codegen/Print.lean`) needs for the two-parameter `Effect.Effect<A, E>` spelling. -/
theorem appTy_closed_iff {Op : Type} (sig : Signature Op) (app : App Op) (l : LayerTy) (p : EffTy)
    (hl : layerTy sig app.layer = some l) (hp : typeOf sig app.program = some p) :
    (appTy sig app).map EffTy.requires = some Requirement.empty ↔
      (l.Closed ∧ Row.Subset p.requires l.out) := by
  rw [appTy_requires sig app l p hl hp, Option.some.injEq]
  constructor
  · intro h
    have hboth : ∀ a, a ∈ Row.union l.requires (Row.diff p.requires l.out) ↔
        a ∈ (Requirement.empty : Requirement) := fun a => by rw [h]
    refine ⟨?_, ?_⟩
    · show l.requires = Requirement.empty
      apply Row.eq_of_mem_iff
      intro a
      constructor
      · intro ha
        exact (hboth a).mp ((Row.mem_union a _ _).mpr (Or.inl ha))
      · intro ha
        exact absurd ha (Row.not_mem_empty a)
    · intro a ha
      by_cases hout : a ∈ l.out
      · exact hout
      · exfalso
        exact Row.not_mem_empty a ((hboth a).mp
          ((Row.mem_union a _ _).mpr (Or.inr ((Row.mem_diff a _ _).mpr ⟨ha, hout⟩))))
  · intro ⟨hclosed, hcovers⟩
    have hc : l.requires = Requirement.empty := hclosed
    rw [(Row.diff_eq_empty_iff_subset p.requires l.out).mpr hcovers, hc]
    exact Row.union_empty_left _

/-! ## `build` — the specification of provisioning

Structural over the combinators, with the leaves interpreted by a supplied `LeafSem`: what
building `effect key body` under a context answers, and whether `effectDiscard body` completes.
The hook is the trusted-boundary position `RunInterp` occupies: never canonical content, always
a parameter of a theorem. The combinators follow the machine's own continuations:
`provide` provides the dependency's context to the dependent's build and keeps only the
dependent's output (`Layer.lean` `provideThenK`, `combineWithK`), `provideMerge` answers
`that.merge merged`, `merge` answers the right-biased merge of the siblings (`Context.mergeAll`,
`Layer.ts:1600`), and `fresh` changes nothing a context can see. -/

/-- The leaf semantics a build is parametric in. -/
structure LeafSem (Op : Type) where
  /-- The value `effect key body` binds under `key` when built under a context. -/
  effect : ServiceKey → Eff Op → Ctx → Option Effect4.Machine.Env.Val
  /-- Whether `effectDiscard body` completes under a context. -/
  discard : Eff Op → Ctx → Option Unit

mutual
/-- The context a layer builds under a context; `none` is a leaf that did not build. A
reference builds nothing here: this specification is structural, and a reference is typed
and resolved by the whole program (`Program/Refs.lean`). -/
def build {Op : Type} (sem : LeafSem Op) : LayerTerm Op → Ctx → Option Ctx
  | .succeed key value, _ => (litVal value).map fun v => Context.empty.addV key v
  | .effect key body, ctx => (sem.effect key body ctx).map fun v => Context.empty.addV key v
  | .effectDiscard body, ctx => (sem.discard body ctx).map fun _ => Context.empty
  | .provide self that, ctx => do
    let d ← build sem that ctx
    build sem self (ctx.merge d)
  | .provideMerge self that, ctx => do
    let d ← build sem that ctx
    let s ← build sem self (ctx.merge d)
    some (d.merge s)
  | .merge left right, ctx => do
    let a ← build sem left ctx
    let b ← build sem right ctx
    some (a.merge b)
  | .fresh inner, ctx => build sem inner ctx
  | .orDie inner, ctx => build sem inner ctx
  | .ref _, _ => none
  | .mergeAll layers, ctx => buildAll sem layers ctx

/-- The layers of a `mergeAll` built as siblings, merged to the right (`Context.mergeAll`,
`Layer.ts:1600`); none is nothing, as `layersTy` types it. -/
def buildAll {Op : Type} (sem : LeafSem Op) : LayerTerms Op → Ctx → Option Ctx
  | .nil, _ => none
  | .cons head .nil, ctx => build sem head ctx
  | .cons head tail, ctx => do
    let a ← build sem head ctx
    let b ← buildAll sem tail ctx
    some (a.merge b)
end

/-- A leaf semantics is *typed* for a signature when every leaf builds under a context that
satisfies the leaf's own requirement row. Every honest leaf semantics is: a body that reads
only what its row promises cannot meet a missing service (`Context.interpret_total`). -/
structure LeafSem.Typed {Op : Type} (sig : Signature Op) (sem : LeafSem Op) : Prop where
  effect : ∀ (key : ServiceKey) (body : Eff Op) (ctx : Ctx) (t : EffTy),
    typeOf sig body = some t → ctx.Satisfies (bodyRequires sig t) →
      (sem.effect key body ctx).isSome = true
  discard : ∀ (body : Eff Op) (ctx : Ctx) (t : EffTy),
    typeOf sig body = some t → ctx.Satisfies (bodyRequires sig t) →
      (sem.discard body ctx).isSome = true

mutual
/-- **Build totality.** Under a typed leaf semantics, a well-typed layer builds under every
context satisfying its requirement row, and the built context satisfies its output row. -/
theorem build_total {Op : Type} (sig : Signature Op) (sem : LeafSem Op) (hsem : sem.Typed sig) :
    ∀ (l : LayerTerm Op) (t : LayerTy) (ctx : Ctx), layerTy sig l = some t →
      ctx.Satisfies t.requires → ∃ out, build sem l ctx = some out ∧ out.Satisfies t.out
  -- structural in the layer (a member of the mutual program family since the join, so
  -- `induction` does not apply); the recursive calls are the old induction hypotheses
  | .succeed key value, t, ctx, ht, _ => by
    cases hv : litVal value with
    | none => simp [layerTy, hv] at ht
    | some v =>
      simp [layerTy, hv] at ht
      subst ht
      refine ⟨Context.empty.addV key v, ?_, satisfies_single_addV key v⟩
      simp [build, hv]
  | .effect key body, t, ctx, ht, hsat => by
    cases hb : effTy sig [] body with
    | none => simp [layerTy, hb] at ht
    | some tb =>
      simp [layerTy, hb] at ht
      subst ht
      have hs := hsem.effect key body ctx tb hb hsat
      cases hv : sem.effect key body ctx with
      | none => rw [hv] at hs; exact Bool.noConfusion hs
      | some v =>
        refine ⟨Context.empty.addV key v, ?_, satisfies_single_addV key v⟩
        simp [build, hv]
  | .effectDiscard body, t, ctx, ht, hsat => by
    cases hb : effTy sig [] body with
    | none => simp [layerTy, hb] at ht
    | some tb =>
      simp [layerTy, hb] at ht
      subst ht
      have hs := hsem.discard body ctx tb hb hsat
      cases hv : sem.discard body ctx with
      | none => rw [hv] at hs; exact Bool.noConfusion hs
      | some _ =>
        refine ⟨Context.empty, ?_, Context.satisfies_empty _⟩
        simp [build, hv]
  | .provide self that, t, ctx, ht, hsat => by
    have ihs := build_total sig sem hsem self
    have iht := build_total sig sem hsem that
    cases hs : layerTy sig self with
    | none => simp [layerTy, hs] at ht
    | some s =>
      cases hd : layerTy sig that with
      | none => simp [layerTy, hs, hd] at ht
      | some d =>
        simp [layerTy, hs, hd] at ht
        subst ht
        -- the dependency builds under `ctx`
        have hdreq : ctx.Satisfies d.requires :=
          Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _)
        obtain ⟨dctx, hdb, hdout⟩ := iht d ctx hd hdreq
        -- the dependent builds under `ctx.merge dctx`
        have hsreq : (ctx.merge dctx).Satisfies s.requires := by
          intro key hk
          by_cases hout : key ∈ d.out
          · exact satisfies_merge_right ctx dctx d.out hdout key hout
          · have hk' : key ∈ Row.union (Row.diff s.requires d.out) d.requires :=
              (Row.mem_union key _ _).mpr (Or.inl ((Row.mem_diff key _ _).mpr ⟨hk, hout⟩))
            exact satisfies_merge_left ctx dctx _ hsat key hk'
        obtain ⟨sctx, hsb, hsout⟩ := ihs s (ctx.merge dctx) hs hsreq
        refine ⟨sctx, ?_, hsout⟩
        simp [build, hdb, hsb]
  | .provideMerge self that, t, ctx, ht, hsat => by
    have ihs := build_total sig sem hsem self
    have iht := build_total sig sem hsem that
    cases hs : layerTy sig self with
    | none => simp [layerTy, hs] at ht
    | some s =>
      cases hd : layerTy sig that with
      | none => simp [layerTy, hs, hd] at ht
      | some d =>
        simp [layerTy, hs, hd] at ht
        subst ht
        have hdreq : ctx.Satisfies d.requires :=
          Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _)
        obtain ⟨dctx, hdb, hdout⟩ := iht d ctx hd hdreq
        have hsreq : (ctx.merge dctx).Satisfies s.requires := by
          intro key hk
          by_cases hout : key ∈ d.out
          · exact satisfies_merge_right ctx dctx d.out hdout key hout
          · have hk' : key ∈ Row.union (Row.diff s.requires d.out) d.requires :=
              (Row.mem_union key _ _).mpr (Or.inl ((Row.mem_diff key _ _).mpr ⟨hk, hout⟩))
            exact satisfies_merge_left ctx dctx _ hsat key hk'
        obtain ⟨sctx, hsb, hsout⟩ := ihs s (ctx.merge dctx) hs hsreq
        refine ⟨dctx.merge sctx, ?_, ?_⟩
        · simp [build, hdb, hsb]
        · exact satisfies_union_of _ _ _ (satisfies_merge_right dctx sctx _ hsout)
            (satisfies_merge_left dctx sctx _ hdout)
  | .merge left right, t, ctx, ht, hsat => by
    have ihl := build_total sig sem hsem left
    have ihr := build_total sig sem hsem right
    cases ha : layerTy sig left with
    | none => simp [layerTy, ha] at ht
    | some a =>
      cases hb : layerTy sig right with
      | none => simp [layerTy, ha, hb] at ht
      | some b =>
        simp [layerTy, ha, hb] at ht
        subst ht
        obtain ⟨actx, hab, haout⟩ :=
          ihl a ctx ha (Context.satisfies_weaken ctx hsat (Row.subset_union_left _ _))
        obtain ⟨bctx, hbb, hbout⟩ :=
          ihr b ctx hb (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
        refine ⟨actx.merge bctx, ?_, ?_⟩
        · simp [build, hab, hbb]
        · exact satisfies_union_of _ _ _ (satisfies_merge_left actx bctx _ haout)
            (satisfies_merge_right actx bctx _ hbout)
  | .fresh inner, t, ctx, ht, hsat => by
    have ih := build_total sig sem hsem inner
    obtain ⟨out, hb, hout⟩ := ih t ctx ht hsat
    refine ⟨out, ?_, hout⟩
    simp [build, hb]
  | .orDie inner, t, ctx, ht, hsat => by
    have ih := build_total sig sem hsem inner
    cases hi : layerTy sig inner with
    | none => simp [layerTy, hi] at ht
    | some i =>
      simp [layerTy, hi] at ht
      subst ht
      obtain ⟨out, hb, hout⟩ := ih i ctx hi hsat
      refine ⟨out, ?_, hout⟩
      simp [build, hb]
  | .ref _, t, ctx, ht, _ => by simp [layerTy] at ht
  | .mergeAll layers, t, ctx, ht, hsat => by
    have ih := buildAll_total sig sem hsem layers
    obtain ⟨out, hb, hout⟩ := ih t ctx (by simpa [layerTy] using ht) hsat
    refine ⟨out, ?_, hout⟩
    simp [build, hb]
termination_by structural l => l

/-- The list form of `build_total`: the layers of a `mergeAll`, their outputs the union. -/
theorem buildAll_total {Op : Type} (sig : Signature Op) (sem : LeafSem Op) (hsem : sem.Typed sig) :
    ∀ (ls : LayerTerms Op) (t : LayerTy) (ctx : Ctx), layersTy sig ls = some t →
      ctx.Satisfies t.requires → ∃ out, buildAll sem ls ctx = some out ∧ out.Satisfies t.out
  | .nil, t, ctx, ht, _ => by simp [layersTy] at ht
  | .cons head .nil, t, ctx, ht, hsat => by
    have ih := build_total sig sem hsem head
    obtain ⟨out, hb, hout⟩ := ih t ctx (by simpa [layersTy] using ht) hsat
    exact ⟨out, by simp [buildAll, hb], hout⟩
  | .cons head (.cons second rest), t, ctx, ht, hsat => by
    have ihh := build_total sig sem hsem head
    have iht := buildAll_total sig sem hsem (.cons second rest)
    cases ha : layerTy sig head with
    | none => simp [layersTy, ha] at ht
    | some a =>
      cases hb : layersTy sig (.cons second rest) with
      | none => simp [layersTy, ha, hb] at ht
      | some b =>
        simp [layersTy, ha, hb] at ht
        subst ht
        obtain ⟨actx, hab, haout⟩ :=
          ihh a ctx ha (Context.satisfies_weaken ctx hsat (Row.subset_union_left _ _))
        obtain ⟨bctx, hbb, hbout⟩ :=
          iht b ctx hb (Context.satisfies_weaken ctx hsat (Row.subset_union_right _ _))
        refine ⟨actx.merge bctx, ?_, ?_⟩
        · simp [buildAll, hab, hbb]
        · exact satisfies_union_of _ _ _ (satisfies_merge_left actx bctx _ haout)
            (satisfies_merge_right actx bctx _ hbout)
termination_by structural ls => ls
end
/-! ## References: the soft half of a requirement row

rc.112's `Context.Reference` (`Context.ts:485`, `:2002`) is a key with a default; `getOption`
(`Context.ts:1636`, modelled as `Context.getOption` over a `References` table) answers a
reference's default when the key is unbound, so a program reading a reference never meets a
missing service. `ConfigProvider` is one (`ConfigProvider.ts:341`), which is why a `Config`
read (`Config.ts:108`, `Config<T> extends Effect<T, ConfigError>`) has no hard requirement:
configuration is provisioning with a default. The hard row a deployment must still provide is
the program's row minus the reference keys. -/

/-- The reference table at the machine's universe. -/
abbrev Refs : Type := Context.References Effect4.Machine.Env.ValU

/-- Satisfaction through `getOption`: every key of the row is bound or is a reference. -/
def SatisfiesRefs (refs : Refs) (ctx : Ctx) (r : Requirement) : Prop :=
  ∀ key, key ∈ r → (Context.getOption refs ctx key).isSome = true

/-- The executable twin, over the row's canonical list. -/
def satisfiesRefsB (refs : Refs) (ctx : Ctx) (r : Requirement) : Bool :=
  r.elems.all fun key => (Context.getOption refs ctx key).isSome

/-- A satisfied hard row is satisfied under references too. -/
theorem satisfiesRefs_of_satisfies (refs : Refs) (ctx : Ctx) (r : Requirement)
    (h : ctx.Satisfies r) : SatisfiesRefs refs ctx r := by
  intro key hk
  show (rightBiased (ctx.get? key) (refs.default? key)).isSome = true
  rw [rightBiased_isSome, h key hk]
  rfl

/-- A row of reference keys is satisfied by every context, the empty one included. -/
theorem satisfiesRefs_of_defaults (refs : Refs) (ctx : Ctx) (r : Requirement)
    (h : ∀ key, key ∈ r → (refs.default? key).isSome = true) : SatisfiesRefs refs ctx r := by
  intro key hk
  show (rightBiased (ctx.get? key) (refs.default? key)).isSome = true
  rw [rightBiased_isSome, h key hk]
  exact Bool.or_true _

/-- **The hard row.** A context that satisfies the row minus the reference keys satisfies the
whole row under references: a deployment provides `r ∖ soft`, the defaults provide `soft`. -/
theorem satisfiesRefs_of_hard (refs : Refs) (ctx : Ctx) (r soft : Requirement)
    (hsoft : ∀ key, key ∈ soft → (refs.default? key).isSome = true)
    (hhard : ctx.Satisfies (Row.diff r soft)) : SatisfiesRefs refs ctx r := by
  intro key hk
  show (rightBiased (ctx.get? key) (refs.default? key)).isSome = true
  rw [rightBiased_isSome]
  by_cases hs : key ∈ soft
  · rw [hsoft key hs]
    exact Bool.or_true _
  · rw [hhard key ((Row.mem_diff key r soft).mpr ⟨hk, hs⟩)]
    rfl

/-! ## The machine half: a layer built on the compile route (the join, 2026-09-07)

Before the join a term lowered into a `LayerTable` and ran on the Layer machine; since it, a
layer is a subterm of the program that provides it (`Program/Eff.lean`), built at its point
by `Program/Compile.lean`, so the probes below are runs of native programs — `Effect.provide(
self, layer)` with the body that observes what the build produced. A witness alphabet
(`DocsOp` below, `Surface/Provision.lean`'s `DeployOp`) is transcribed onto the native route
the way the old lowering read it: a body that performs one row reads the row's one required
service (`Eff.service`; the old `Construction.fromService`). -/

open Effect4.Machine (runSyncExit RunMachine Stores emptyCtx)

/-- `Effect.runSyncExit` of a native program at the budget the old `runOver` ran (1024
commands: since source-repairs §19, a tracked child's exit path is a run of commands) and
compile fuel 1024, from the empty stores and context. -/
def runNative (program : NativeEff) : Effect4.Machine.ExitV :=
  letI := evaluatorFor program
  (runSyncExit (interpOf program) 1024 (RunMachine.empty Stores.empty) (compile program 1024)
    emptyCtx).2

/-- The services a fiber-context answer holds, as (key name, value) pairs in insertion order;
`[]` for a failure or any other value. -/
def servicesOfExit : Effect4.Machine.ExitV → List (Nat × Nat)
  | Exit.success value =>
    match Effect4.Machine.Val.context? value with
    | some ctx => ctx.services.entries.map fun s => (s.key.name.value, natOfVal 0 s.valueVal)
    | none => []
  | _ => []

/-- `Effect.provide(Effect.context(), l)` through the compile route: the services the built
context holds, as the body reads them (`provideContext`, `internal/effect.ts:2197`, over the
empty fiber context is the built context itself, `CurrentMemoMap` (key `3`) trailing,
`Layer.ts:762`). -/
def buildServices (l : LayerTerm NativeOp) : List (Nat × Nat) :=
  servicesOfExit (runNative (.provideLayer l false (.withFiber .getContext)))

/-- Whether `Effect.provide(Effect.void, l)` succeeds through the compile route. -/
def buildSucceeds (l : LayerTerm NativeOp) : Bool :=
  match runNative (.provideLayer l false (.succeed (.lit .unit))) with
  | Exit.success _ => true
  | _ => false

/-- `Effect.provide(Effect.service(key), l, { local: true })` through the compile route
(`internal/layer.ts:8-22`): the value the program reads. -/
def provideThenService (l : LayerTerm NativeOp) (key : ServiceKey) : Effect4.Machine.ExitV :=
  runNative (.provideLayer l true (.service key))

/-- The key names of the context the specification builds. -/
def specKeys {Op : Type} (sem : LeafSem Op) (l : LayerTerm Op) : Option (List Nat) :=
  (build sem l Context.empty).map fun ctx => ctx.keys.map fun k => k.name.value

/-! ## Witnesses: the docs deployment of the Surface plan (§13.3), as layers

Two bindings the platform provides, `DB` and `RATE`; two services the worker builds from
them, `Db` and `RateLimit`; the handler of `POST /feedback` requires both. The alphabet
below is the service route: each row names the services it requires. -/

section Witnesses

/-- The keys. Services `10`, `11`; bindings `20`, `21`; the ambient scope is `scopeKey`. -/
def dbKey : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩
def rateKey : ServiceKey := ⟨⟨11⟩, ⟨11⟩⟩
def dbBinding : ServiceKey := ⟨⟨20⟩, ⟨20⟩⟩
def rateBinding : ServiceKey := ⟨⟨21⟩, ⟨21⟩⟩

/-- The docs app's operation alphabet. -/
inductive DocsOp
  /-- Build `Db` from the `DB` binding. -/
  | makeDb
  /-- Build `RateLimit` from the `RATE` binding. -/
  | makeRate
  /-- `db.insertFeedback`. -/
  | insertFeedback
  /-- `rateLimit.check`. -/
  | rateCheck
deriving DecidableEq, Repr

def DocsOp.row : DocsOp → Row
  | .makeDb =>
    ⟨"makeDb", "makeDb", .call, [], .sync, .unit, .handle "Db", .never, [dbBinding], "docs app", []⟩
  | .makeRate =>
    ⟨"makeRate", "makeRate", .call, [], .sync, .unit, .handle "RateLimit", .never, [rateBinding],
      "docs app", []⟩
  | .insertFeedback =>
    ⟨"insertFeedback", "db.insertFeedback", .call, [], .sync, .nat, .unit, .never, [dbKey],
      "docs app", []⟩
  | .rateCheck =>
    ⟨"rateCheck", "rateLimit.check", .call, [], .sync, .unit, .bool, .never, [rateKey], "docs app", []⟩

/-- The docs signature's service table: the two services are the host objects their rows
build, the two bindings are the numbers the platform hands over. -/
def docsServiceTy (key : ServiceKey) : Option Ty :=
  if key = dbKey then some (.handle "Db")
  else if key = rateKey then some (.handle "RateLimit")
  else if key = dbBinding ∨ key = rateBinding then some .nat
  else none

def docsSig : Signature DocsOp := ⟨DocsOp.row, fun _ _ => none, scopeKey, docsServiceTy⟩

/-- The leaf semantics of the docs alphabet: a body that performs one row reads the row's one
required service and binds it as the new service (the machine's `Construction.fromService`);
a literal body binds the literal. -/
def docsSem : LeafSem DocsOp where
  effect := fun _ body ctx =>
    match body with
    | .perform op _ =>
      match (DocsOp.row op).requires with
      | [input] => ctx.getV input
      | _ => none
    | .succeed (.lit value) => litVal value
    | _ => none
  discard := fun body _ =>
    match body with
    | .succeed (.lit _) => some ()
    | _ => none

/-- The handler of `POST /feedback`: check the rate limit, insert the row. -/
def feedbackHandler : Eff DocsOp :=
  .bind (.perform .rateCheck (.lit .unit)) (.perform .insertFeedback (.lit (.nat 1)))

/-- The services layer: `Db` and `RateLimit`, each built from its binding. -/
def servicesLayer : LayerTerm DocsOp :=
  .merge (.effect dbKey (.perform .makeDb (.lit .unit)))
    (.effect rateKey (.perform .makeRate (.lit .unit)))

/-- The platform layer: the two bindings, values in hand (the model's stand-in for the
`env.DB` / `env.RATE` objects is their index, as it is for every host-minted object). -/
def bindingsLayer : LayerTerm DocsOp :=
  .merge (.succeed dbBinding (.nat 1)) (.succeed rateBinding (.nat 2))

/-- The deployment: the services provided by the bindings, both kept visible. -/
def deploymentLayer : LayerTerm DocsOp := .provideMerge servicesLayer bindingsLayer

/-- The same, with the bindings hidden. -/
def hiddenDeployment : LayerTerm DocsOp := .provide servicesLayer bindingsLayer

/-- The mistake: bindings and services as siblings — `merge` provides nothing to a sibling. -/
def siblingMistake : LayerTerm DocsOp := .merge servicesLayer bindingsLayer

def theApp : App DocsOp := ⟨deploymentLayer, feedbackHandler⟩

-- The handler needs both services and nothing else.
#guard (typeOf docsSig feedbackHandler).map EffTy.requires =
  some (Requirement.ofList [dbKey, rateKey])

-- The services layer requires the two bindings; the platform layer requires nothing.
#guard (layerTy docsSig servicesLayer).map LayerTy.requires =
  some (Requirement.ofList [dbBinding, rateBinding])
#guard (layerTy docsSig bindingsLayer).map LayerTy.requires = some Requirement.empty

-- The deployment is closed and provides all four keys; hiding the bindings provides two.
#guard (layerTy docsSig deploymentLayer).map LayerTy.requires = some Requirement.empty
#guard (layerTy docsSig deploymentLayer).map LayerTy.out =
  some (Requirement.ofList [dbKey, rateKey, dbBinding, rateBinding])
#guard (layerTy docsSig hiddenDeployment).map LayerTy.out =
  some (Requirement.ofList [dbKey, rateKey])
#guard (layerTy docsSig hiddenDeployment).map LayerTy.requires = some Requirement.empty

-- The sibling mistake is *typed*: its signature still requires the two bindings.
#guard (layerTy docsSig siblingMistake).map LayerTy.requires =
  some (Requirement.ofList [dbBinding, rateBinding])

-- The app is closed: the handler's requirements are covered by the deployment.
#guard (appTy docsSig theApp).map EffTy.requires = some Requirement.empty
#guard (appTy docsSig ⟨siblingMistake, feedbackHandler⟩).map EffTy.requires =
  some (Requirement.ofList [dbBinding, rateBinding])

-- The specification builds the deployment and the hidden deployment, and refuses the mistake.
#guard specKeys docsSem deploymentLayer = some [20, 21, 10, 11]
#guard specKeys docsSem hiddenDeployment = some [10, 11]
#guard specKeys docsSem siblingMistake = none

/-! ### The machine agrees on the finite probes

The docs layers on the native route (`docsLayer`), provided to a program through the compile
route: the produced context has the keys the specification predicts (plus `CurrentMemoMap`,
key `3`), the values flow from the bindings to the services, and the sibling mistake dies
with the missing service — a defect, never a typed error (`Context.getUnsafe`,
`internal/effect.ts:2134` through `:670-674`). -/

/-- The docs alphabet on the native route: a body that performs one row reads the row's one
required service (`Eff.service`), as the old lowering's `Construction.fromService` did; a
literal and a numeric failure are themselves. -/
def docsBody : Eff DocsOp → Option NativeEff
  | .perform op _ =>
    match (DocsOp.row op).requires with
    | [input] => some (.service input)
    | _ => none
  | .succeed (.lit value) => some (.succeed (.lit value))
  | .fail (.lit (.nat n)) => some (.fail (.lit (.nat n)))
  | _ => none

mutual
/-- A docs layer on the native route, leaf by leaf; `none` at a body the transcription does not
read. -/
def docsLayer : LayerTerm DocsOp → Option (LayerTerm NativeOp)
  | .succeed key value => some (.succeed key value)
  | .effect key body => (docsBody body).map (.effect key)
  | .effectDiscard body => (docsBody body).map .effectDiscard
  | .provide self that => do some (.provide (← docsLayer self) (← docsLayer that))
  | .provideMerge self that => do some (.provideMerge (← docsLayer self) (← docsLayer that))
  | .merge left right => do some (.merge (← docsLayer left) (← docsLayer right))
  | .fresh inner => (docsLayer inner).map .fresh
  | .orDie inner => (docsLayer inner).map .orDie
  | .ref target => some (.ref target)
  | .mergeAll layers => (docsLayers layers).map .mergeAll
def docsLayers : LayerTerms DocsOp → Option (LayerTerms NativeOp)
  | .nil => some .nil
  | .cons head tail => do some (.cons (← docsLayer head) (← docsLayers tail))
end

#guard (docsLayer deploymentLayer).map buildSucceeds = some true
#guard (docsLayer deploymentLayer).map buildServices =
  some [(20, 1), (21, 2), (10, 1), (11, 2), (3, 0)]
#guard (docsLayer hiddenDeployment).map buildSucceeds = some true
#guard (docsLayer hiddenDeployment).map buildServices = some [(10, 1), (11, 2), (3, 0)]
#guard (docsLayer siblingMistake).map buildSucceeds = some false

-- `Effect.provide(Effect.service(Db), deployment)` answers the binding's value, as the
-- specification says the service was built from it.
#guard (docsLayer deploymentLayer).map (provideThenService · dbKey) = some (Exit.success (.nat 1))
#guard (docsLayer hiddenDeployment).map (provideThenService · rateKey) =
  some (Exit.success (.nat 2))

/-! ### Order is invisible to the type and visible to the run (CE 5, lifted to layers) -/

def leftWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 1)) (.succeed dbKey (.nat 2))
def rightWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 2)) (.succeed dbKey (.nat 1))

#guard layerTy docsSig leftWins = layerTy docsSig rightWins
#guard (docsLayer leftWins).map buildServices = some [(10, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(10, 1), (3, 0)]
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 1))

/-! ### Configuration: the two scheduler references are satisfied by the empty context -/

-- `MaxOpsBeforeYield` and `PreventSchedulerYield` (`Scheduler.ts:269-298`) are references, so
-- a program reading them has no hard requirement: the empty context satisfies the row under
-- their defaults, and fails to satisfy it as a hard row.
#guard satisfiesRefsB [Effect4.Machine.Env.maxOpsRef, Effect4.Machine.Env.preventYieldRef]
  Context.empty (Requirement.ofList [Effect4.Machine.Env.maxOpsKey, Effect4.Machine.Env.preventYieldKey]) = true
#guard satisfiesRefsB [] Context.empty
  (Requirement.ofList [Effect4.Machine.Env.maxOpsKey, Effect4.Machine.Env.preventYieldKey]) = false
-- The hard row of a handler that also reads the scheduler budget is the handler's services.
#guard Row.diff (Requirement.ofList [dbKey, rateKey, Effect4.Machine.Env.maxOpsKey])
    (Requirement.ofList [Effect4.Machine.Env.maxOpsKey, Effect4.Machine.Env.preventYieldKey]) =
  Requirement.ofList [dbKey, rateKey]

/-! ### `orDie` builds, and refusals are data -/

-- `Layer.orDie` is `catch_(build, die)` (`Layer.ts:3327`, `internal/effect.ts:3289`): the type
-- says `E := never`, and on the compile route a leaf's typed failure comes out as the defect.
#guard (layerTy docsSig (.orDie servicesLayer)).map LayerTy.error = some Ty.never
#guard (docsLayer (.orDie deploymentLayer)).map buildSucceeds = some true
#guard (docsLayer (.effect dbKey (.fail (.lit (.nat 7))))).map (provideThenService · dbKey) =
  some (Exit.failure (Cause.fail (.tag 7)))
#guard (docsLayer (.orDie (.effect dbKey (.fail (.lit (.nat 7)))))).map (provideThenService · dbKey) =
  some (Exit.failure (Cause.die (Effect4.Machine.Defect.user 7)))

-- A string literal is not a machine value, so a layer over one is refused by the typing.
#guard layerTy docsSig (.succeed dbKey (.str "db")) = none

end Witnesses

/-! ## Separation gates: everything here is first-order data -/

example : DecidableEq LayerTy := inferInstance
example : DecidableEq (LayerTerm DocsOp) := inferInstance
example : DecidableEq (App DocsOp) := inferInstance

end Effect4.Program.Provision
