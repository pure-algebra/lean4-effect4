import Effect4.Program.Typing
import Effect4.Machine.Layer

/-!
# Provision — the requirement algebra, the layer signature, and the layer term

Landed 2026-09-04 from the `workshop/Provision` spike. Plan and grill:
`docs/research/2026-09-04-provision-algebra.md`; battery `Test/Program/ProvisionContract.lean`.

What this module adds to the tree, and what it deliberately reuses:

* **Reused, never re-declared.** `Requirement := Row ServiceKey` and the eleven context
  laws (`Effect4/Machine/Context.lean`), `Ty`/`EffTy`/`typeOf` (`Effect4/Program/Typing.lean`),
  and the whole rc.112 Layer machine — `LayerTable`, `LayerDesc`, `Construction`, `progOf`,
  `interp`, `runSyncExit` (`Effect4/Machine/Layer.lean`). The machine is the semantics; this
  module is the *typed face* over it and the *specification* it refines.
* **`Row.diff`** (`Effect4/Data/Row.lean`, landed with this module). `Exclude<R, ROut>`
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
  `fresh`, `orDie`; `mergeAll` is the fold of `merge`), with `layerTy` its typing and
  `Eff` bodies at the `effect` leaves — the same `Eff` the printer prints and the
  compile compiles. Nothing here is a closure; `DecidableEq` throughout.
* **`App`** — `Effect.provide(program, layer)` (`internal/layer.ts:8-22`) — and the
  theorem that its requirement row is empty exactly when the layer closes the program.
* **`build`, the specification of provisioning**, structural over the combinators with the
  leaves supplied as a `LeafSem` hook (the trusted-boundary position `ServiceUniverse` and
  `RunInterp` already occupy), and `build_total`: *a well-typed layer builds under every
  context that satisfies its requirement row, and what it builds satisfies its output row*.
  That sentence is what "the `R` channel guarantees the wiring" means, and it is proved once
  over the algebra, for every leaf semantics that is honest about its own leaves.
* **`lower`, the refinement into the machine.** A term becomes a `LayerTable` and a root
  id; the witnesses run the lowered tables through `runSyncExit` at the proved `interp` and
  pin, by `#guard`, that the machine's produced context has the keys `build` predicts —
  a refinement mapping in Lamport's sense (`keysRow ∘ decode` of the machine's answer),
  checked on finite probes here and stated as an owed theorem in the plan.

Every rc.112 line named below is in `vendor/effect-4.0.0-rc.112/src/`.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision

open Effect4
open Effect4.Machine.Env (Requirement Ctx Context Service decode encode scopeKey natOfVal
  rightBiased)

/-! ## The signature: `Layer<ROut, E, RIn>` (`Layer.ts:54`) -/

/-- What a layer provides (`ROut`), how it can fail (`E`), and what it needs (`RIn`). -/
structure LayerTy where
  out : Requirement
  error : Ty
  requires : Requirement
deriving DecidableEq

namespace LayerTy

/-- `Layer.provide(self, that)` (`Layer.ts:2089`, `:2258`):
`Layer<ROut2, E | E2, RIn | Exclude<RIn2, ROut>>` — the dependency's outputs are removed
from the dependent's requirements and the dependency's own requirements are added; only
the dependent's outputs remain visible. -/
def provide (self that : LayerTy) : LayerTy :=
  ⟨self.out, self.error.join that.error,
    Row.union (Row.diff self.requires that.out) that.requires⟩

/-- `Layer.provideMerge(self, that)` (`Layer.ts:2523`, `:2704`): the same requirement rule,
both output rows kept. -/
def provideMerge (self that : LayerTy) : LayerTy :=
  ⟨Row.union self.out that.out, self.error.join that.error,
    Row.union (Row.diff self.requires that.out) that.requires⟩

/-- `Layer.merge(a, b)` (`Layer.ts:1751`, `:1850`) and each step of `Layer.mergeAll`
(`:1652-1658`): every row unions; nothing is provided to a sibling. -/
def merge (a b : LayerTy) : LayerTy :=
  ⟨Row.union a.out b.out, a.error.join b.error, Row.union a.requires b.requires⟩

/-- `Layer.orDie` (`Layer.ts:3327`): the typed error becomes a defect, `E := never`. -/
def orDie (l : LayerTy) : LayerTy := ⟨l.out, .never, l.requires⟩

/-- A closed layer: `Layer<_, _, never>`, the shape `Effect.provide` accepts with nothing
left over and the shape a deployment must reach. -/
def Closed (l : LayerTy) : Prop := l.requires = Requirement.empty

instance (l : LayerTy) : Decidable (Closed l) := by unfold Closed; infer_instance

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
  simp only [provide, provideMerge, Row.mem_union, Row.mem_diff, not_or]
  by_cases hL : a ∈ l.requires <;> by_cases hO₁ : a ∈ d₁.out <;> by_cases hO₂ : a ∈ d₂.out <;>
    by_cases hR₁ : a ∈ d₁.requires <;> by_cases hR₂ : a ∈ d₂.requires <;>
    simp [hL, hO₁, hO₂, hR₁, hR₂]

/-- `merge` is commutative on the rows. What is *not* commutative is the built context
(`Effect4/Machine/Context.lean`, counterexample CE 5: `merge` is right-biased), and the
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

/-! ## The layer language -/

/-- A literal as a value of the Layer machine's alphabet; strings are not machine values. -/
def litVal : Lit → Option Effect4.Machine.Env.Val
  | .unit => some .unit
  | .nat n => some (.nat n)
  | .bool b => some (.bool b)
  | .str _ => none

/-- The first-order layer term. One constructor per rc.112 export, each naming the line it
transcribes; `Layer.mergeAll(a, b, …)` is `mergeAll`, the fold of `merge`. A body is an `Eff`
program: the same syntax the printer prints and the compile compiles. -/
inductive LayerTerm (Op : Type)
  /-- `Layer.succeed(key, value)` (`Layer.ts:1074`): a service from a value already in hand. -/
  | succeed (key : ServiceKey) (value : Lit)
  /-- `Layer.effect(key, body)` (`Layer.ts:1427`): a service built by a program, in the
  layer's own scope — `Exclude<R, Scope.Scope>` (`:1438`). -/
  | effect (key : ServiceKey) (body : Eff Op)
  /-- `Layer.effectDiscard(body)` (`Layer.ts:1512`): construction work that provides nothing. -/
  | effectDiscard (body : Eff Op)
  /-- `self.pipe(Layer.provide(that))` (`Layer.ts:2258`). -/
  | provide (self that : LayerTerm Op)
  /-- `self.pipe(Layer.provideMerge(that))` (`Layer.ts:2704`). -/
  | provideMerge (self that : LayerTerm Op)
  /-- `Layer.merge(left, right)` (`Layer.ts:1850`). -/
  | merge (left right : LayerTerm Op)
  /-- `Layer.fresh(inner)` (`Layer.ts:3850`): the same signature, a private memo map. -/
  | fresh (inner : LayerTerm Op)
  /-- `Layer.orDie(inner)` (`Layer.ts:3327`). -/
  | orDie (inner : LayerTerm Op)
deriving DecidableEq

namespace LayerTerm

variable {Op : Type}

/-- `Layer.mergeAll(l, …)` (`Layer.ts:1652`): a left fold of `merge`, so the last layer is the
rightmost operand and, in the built context, wins (`Context.mergeAll`, `Layer.ts:1600`). -/
def mergeAll (first : LayerTerm Op) : List (LayerTerm Op) → LayerTerm Op
  | [] => first
  | l :: rest => mergeAll (merge first l) rest

end LayerTerm

/-! ## Typing -/

/-- The scope-free requirement row of a layer body: `Exclude<R, Scope.Scope>` (`Layer.ts:1438`,
`:1512`): the layer's own scope answers the body's `Scope` requirement. -/
def bodyRequires {Op : Type} (sig : Signature Op) (t : EffTy) : Requirement :=
  Row.diff t.requires (Requirement.single sig.scopeKey)

/-- `layerTy` — the signature of a layer term, structural; `none` refuses an ill-typed body
or a literal outside the value alphabet. The rules are the four `LayerTy` operations and the
two leaf shapes; `fresh` is transparent (`Layer.ts:3850` changes sharing, not the type). -/
def layerTy {Op : Type} (sig : Signature Op) : LayerTerm Op → Option LayerTy
  | .succeed key value =>
    (litVal value).map fun _ => ⟨Requirement.single key, .never, Requirement.empty⟩
  | .effect key body =>
    (typeOf sig body).map fun t => ⟨Requirement.single key, t.error, bodyRequires sig t⟩
  | .effectDiscard body =>
    (typeOf sig body).map fun t => ⟨Requirement.empty, t.error, bodyRequires sig t⟩
  | .provide self that => do
    let s ← layerTy sig self
    let t ← layerTy sig that
    some (s.provide t)
  | .provideMerge self that => do
    let s ← layerTy sig self
    let t ← layerTy sig that
    some (s.provideMerge t)
  | .merge left right => do
    let a ← layerTy sig left
    let b ← layerTy sig right
    some (a.merge b)
  | .fresh inner => layerTy sig inner
  | .orDie inner => (layerTy sig inner).map LayerTy.orDie

/-- A layer is well-typed when `layerTy` answers. -/
def WellTypedLayer {Op : Type} (sig : Signature Op) (l : LayerTerm Op) : Prop :=
  (layerTy sig l).isSome = true

instance {Op : Type} (sig : Signature Op) (l : LayerTerm Op) : Decidable (WellTypedLayer sig l) := by
  unfold WellTypedLayer; infer_instance

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
(`Effect4/Codegen/Print.lean`) needs for the two-parameter `Effect.Effect<A, E>` spelling. -/
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

/-- The context a layer builds under a context; `none` is a leaf that did not build. -/
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

/-- **Build totality.** Under a typed leaf semantics, a well-typed layer builds under every
context satisfying its requirement row, and the built context satisfies its output row. -/
theorem build_total {Op : Type} (sig : Signature Op) (sem : LeafSem Op) (hsem : sem.Typed sig) :
    ∀ (l : LayerTerm Op) (t : LayerTy) (ctx : Ctx), layerTy sig l = some t →
      ctx.Satisfies t.requires → ∃ out, build sem l ctx = some out ∧ out.Satisfies t.out := by
  intro l
  induction l with
  | succeed key value =>
    intro t ctx ht _
    cases hv : litVal value with
    | none => simp [layerTy, hv] at ht
    | some v =>
      simp [layerTy, hv] at ht
      subst ht
      refine ⟨Context.empty.addV key v, ?_, satisfies_single_addV key v⟩
      simp [build, hv]
  | effect key body =>
    intro t ctx ht hsat
    cases hb : typeOf sig body with
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
  | effectDiscard body =>
    intro t ctx ht hsat
    cases hb : typeOf sig body with
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
  | provide self that ihs iht =>
    intro t ctx ht hsat
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
  | provideMerge self that ihs iht =>
    intro t ctx ht hsat
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
  | merge left right ihl ihr =>
    intro t ctx ht hsat
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
  | fresh inner ih =>
    intro t ctx ht hsat
    obtain ⟨out, hb, hout⟩ := ih t ctx ht hsat
    refine ⟨out, ?_, hout⟩
    simp [build, hb]
  | orDie inner ih =>
    intro t ctx ht hsat
    cases hi : layerTy sig inner with
    | none => simp [layerTy, hi] at ht
    | some i =>
      simp [layerTy, hi] at ht
      subst ht
      obtain ⟨out, hb, hout⟩ := ih i ctx hi hsat
      refine ⟨out, ?_, hout⟩
      simp [build, hb]

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

/-! ## `lower` — the refinement into the rc.112 Layer machine

A term lowers into a `LayerTable` (`Effect4/Machine/Layer.lean`) and the id of its root. The
leaves lower on the fragment the machine's `Construction` alphabet admits: a `succeed` is
`fromBuildUnsafe(succeed(context))` (`Layer.ts:1129-1130`, an `atom`), an `effect` is
`fromBuildMemo` (`:1481`, `memoized`) over a body that is one `perform` reading one service
(`Construction.fromService`), one literal (`succeedContext`), or one numeric `fail`
(`failWith`). `orDie` has no machine description at this pin (`Layer.ts:3327` is a
`catchCause` frame the `LayerDesc` alphabet lacks) and is refused; `mergeAll` and `merge`
are `LayerDesc.mergeAll`. -/

open Effect4.Machine.Layers (LayerTable LayerDesc LayerId Construction CombineMode ProgName)

/-- The construction a leaf body admits, if any. -/
def constructionOf {Op : Type} (sig : Signature Op) (key : ServiceKey) :
    Eff Op → Option Construction
  | .succeed (.lit value) => (litVal value).map fun v => Construction.succeedContext [(key, v)]
  | .fail (.lit (.nat n)) => some (Construction.failWith (Effect4.Machine.Env.Err.tag n))
  | .perform op _ =>
    match (sig.rowOf op).requires with
    | [input] => some (Construction.fromService input key)
    | _ => none
  | _ => none

/-- The construction a discarding body admits: no service is bound. -/
def discardConstructionOf {Op : Type} : Eff Op → Option Construction
  | .succeed (.lit value) => (litVal value).map fun _ => Construction.succeedContext []
  | .fail (.lit (.nat n)) => some (Construction.failWith (Effect4.Machine.Env.Err.tag n))
  | _ => none

/-- Lower a term into a table: the descriptions are appended, the root's id is answered. -/
def lowerInto {Op : Type} (sig : Signature Op) :
    LayerTerm Op → LayerTable → Option (LayerTable × LayerId)
  | .succeed key value, table =>
    (litVal value).map fun v =>
      (table ++ [LayerDesc.atom (Construction.succeedContext [(key, v)])], ⟨table.length⟩)
  | .effect key body, table =>
    (constructionOf sig key body).map fun c =>
      (table ++ [LayerDesc.memoized c], ⟨table.length⟩)
  | .effectDiscard body, table =>
    (discardConstructionOf body).map fun c => (table ++ [LayerDesc.memoized c], ⟨table.length⟩)
  | .provide self that, table => do
    let (table, t) ← lowerInto sig that table
    let (table, s) ← lowerInto sig self table
    some (table ++ [LayerDesc.provideWith s t CombineMode.provide], ⟨table.length⟩)
  | .provideMerge self that, table => do
    let (table, t) ← lowerInto sig that table
    let (table, s) ← lowerInto sig self table
    some (table ++ [LayerDesc.provideWith s t CombineMode.provideMerge], ⟨table.length⟩)
  | .merge left right, table => do
    let (table, a) ← lowerInto sig left table
    let (table, b) ← lowerInto sig right table
    some (table ++ [LayerDesc.mergeAll [a, b]], ⟨table.length⟩)
  | .fresh inner, table => do
    let (table, i) ← lowerInto sig inner table
    some (table ++ [LayerDesc.fresh i], ⟨table.length⟩)
  | .orDie _, _ => none

/-- The lowered table and root of a term, from the empty table. -/
def lower {Op : Type} (sig : Signature Op) (l : LayerTerm Op) : Option (LayerTable × LayerId) :=
  lowerInto sig l []

/-! ## Running a lowered term through the machine -/

/-- Run a program over a table on the sync scheduler, from the empty store and context. -/
def runOver (table : LayerTable) (program : ProgName) :
    Effect4.Machine.Layers.LayerMachine × Effect4.Machine.Env.ExitV :=
  Effect4.Machine.runSyncExit (Effect4.Machine.Layers.interp table) 512
    (Effect4.Machine.RunMachine.empty Effect4.Machine.Layers.St.empty)
    (Effect4.Machine.Layers.progOf table program) Context.empty

/-- The services a successful context answer holds, as (key name, value) pairs in insertion
order; `[]` for a failure. -/
def servicesOfExit : Effect4.Machine.Env.ExitV → List (Nat × Nat)
  | Exit.success value =>
    match decode value with
    | some ctx => ctx.entries.map fun s => (s.key.name.value, natOfVal 0 s.valueVal)
    | none => []
  | _ => []

/-- `Effect.scoped(Layer.build(l))` through the machine: the services the built context holds
(`CurrentMemoMap`, key `3`, trails every build — `Layer.ts:762`). -/
def buildServices {Op : Type} (sig : Signature Op) (l : LayerTerm Op) :
    Option (List (Nat × Nat)) :=
  (lower sig l).map fun (table, root) =>
    servicesOfExit (runOver table (ProgName.scoped (ProgName.build root))).2

/-- Whether `Effect.scoped(Layer.build(l))` succeeds through the machine. -/
def buildSucceeds {Op : Type} (sig : Signature Op) (l : LayerTerm Op) : Option Bool :=
  (lower sig l).map fun (table, root) =>
    match (runOver table (ProgName.scoped (ProgName.build root))).2 with
    | Exit.success _ => true
    | _ => false

/-- `Effect.provide(Effect.service(key), l)` through the machine (`internal/layer.ts:8-22`,
`local: true`): the value the program reads. -/
def provideThenService {Op : Type} (sig : Signature Op) (l : LayerTerm Op) (key : ServiceKey) :
    Option Effect4.Machine.Env.ExitV :=
  (lower sig l).map fun (table, root) =>
    (runOver table (ProgName.provideLayer root true (ProgName.service key))).2

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
    ⟨"makeDb", "makeDb", .call, [], .sync, .unit, .handle "Db", .never, [dbBinding], "docs app"⟩
  | .makeRate =>
    ⟨"makeRate", "makeRate", .call, [], .sync, .unit, .handle "RateLimit", .never, [rateBinding],
      "docs app"⟩
  | .insertFeedback =>
    ⟨"insertFeedback", "db.insertFeedback", .call, [], .sync, .nat, .unit, .never, [dbKey],
      "docs app"⟩
  | .rateCheck =>
    ⟨"rateCheck", "rateLimit.check", .call, [], .sync, .unit, .bool, .never, [rateKey], "docs app"⟩

def docsSig : Signature DocsOp := ⟨DocsOp.row, fun _ _ => none, scopeKey⟩

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

`Effect.scoped(Layer.build(l))` through the proved rc.112 machine: the produced context has
the keys the specification predicts (plus `CurrentMemoMap`, key `3`), the values flow from
the bindings to the services, and the sibling mistake dies with `serviceNotFound` — a defect,
never a typed error (`Layer.ts:807` through `internal/effect.ts:670-674`). -/

#guard buildSucceeds docsSig deploymentLayer = some true
#guard buildServices docsSig deploymentLayer = some [(20, 1), (21, 2), (10, 1), (11, 2), (3, 0)]
#guard buildSucceeds docsSig hiddenDeployment = some true
#guard buildServices docsSig hiddenDeployment = some [(10, 1), (11, 2), (3, 0)]
#guard buildSucceeds docsSig siblingMistake = some false

-- `Effect.provide(Effect.service(Db), deployment)` answers the binding's value, as the
-- specification says the service was built from it.
#guard provideThenService docsSig deploymentLayer dbKey = some (Exit.success (.nat 1))
#guard provideThenService docsSig hiddenDeployment rateKey = some (Exit.success (.nat 2))

/-! ### Order is invisible to the type and visible to the run (CE 5, lifted to layers) -/

def leftWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 1)) (.succeed dbKey (.nat 2))
def rightWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 2)) (.succeed dbKey (.nat 1))

#guard layerTy docsSig leftWins = layerTy docsSig rightWins
#guard buildServices docsSig leftWins = some [(10, 2), (3, 0)]
#guard buildServices docsSig rightWins = some [(10, 1), (3, 0)]
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

/-! ### Refusals are data -/

-- `orDie` has no machine description at this pin; the type still says `E := never`.
#guard lower docsSig (.orDie servicesLayer) = none
#guard (layerTy docsSig (.orDie servicesLayer)).map LayerTy.error = some Ty.never

-- A string literal is not a machine value, so a layer over one is refused by the typing.
#guard layerTy docsSig (.succeed dbKey (.str "db")) = none

end Witnesses

/-! ## Separation gates: everything here is first-order data -/

example : DecidableEq LayerTy := inferInstance
example : DecidableEq (LayerTerm DocsOp) := inferInstance
example : DecidableEq (App DocsOp) := inferInstance

end Effect4.Program.Provision
