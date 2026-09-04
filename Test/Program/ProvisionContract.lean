import Effect4.Program.Provision

/-!
# Provision contract — the requirement algebra and the layer signature, frozen

Plan: `docs/research/2026-09-04-provision-algebra.md` §2–§3, §9 (R2). The module under
contract is `Effect4/Program/Provision.lean` (spiked as `workshop/Provision/Provision.lean`).

Every obligation below is ascribed at its exact proposition and supplied by name with `@`
or with its type arguments fixed, so a declaration that keeps the frozen name but weakens
the statement fails here (`Test/Machine/Environment/ContextKeyContract.lean` is the model).
The executable receipts are `#guard`s in the idiom of `Test/Program/CompileContract.lean`:
a `#guard` that runs the Layer machine is a finite probe at one fuel and nothing more, and
the machine halves of the four register rows stay `#guard`s on purpose (a kernel `decide`
over a fuel-512 run is the cost `docs/research/2026-09-03-survey-lean-core.md` finding 22
measured). The typing halves are theorems by `decide`.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-PROV-CE-001` — `merge` provides a sibling's requirement. Refuted: the sibling shape
  types with the bindings still required, and the machine dies with `serviceNotFound`.
* `E4-PROV-CE-002` — the layer signature determines the built context. Refuted: `leftWins`
  and `rightWins` share a signature and build different contexts (CE 5 lifted).
* `E4-PROV-CE-003` — `Layer.orDie` is one more `LayerDesc`. Refuted: the lowering answers
  `none` while the typing answers `E := never`; the refusal is `PROV-FB-ORDIE-DESC`.
* `E4-PROV-CE-004` — a string literal is a layer value. Refuted by the typing
  (`PROV-FB-STRING-VALUE`): strings are not machine values on either route.
-/

set_option autoImplicit false

namespace Test.Program.ProvisionContract

open Effect4
open Effect4.Machine.Env (Requirement Ctx Context)
open Effect4.Program
open Effect4.Program.Provision

/-! ## D0 — `Row.diff`, at the requirement instance -/

section RowDiff

#check (Row.diff (α := ServiceKey) : Requirement → Requirement → Requirement)
#check (Row.mem_diff (α := ServiceKey) :
  ∀ (a : ServiceKey) (r s : Requirement), a ∈ Row.diff r s ↔ a ∈ r ∧ a ∉ s)
#check (Row.diff_subset (α := ServiceKey) :
  ∀ (r s : Requirement), Row.Subset (Row.diff r s) r)
#check (Row.diff_empty (α := ServiceKey) : ∀ (r : Requirement), Row.diff r Row.empty = r)
#check (Row.diff_self (α := ServiceKey) : ∀ (r : Requirement), Row.diff r r = Row.empty)
#check (Row.diff_eq_empty_iff_subset (α := ServiceKey) :
  ∀ (r s : Requirement), Row.diff r s = Row.empty ↔ Row.Subset r s)
#check (Row.diff_union_right (α := ServiceKey) :
  ∀ (r s t : Requirement), Row.diff r (Row.union s t) = Row.diff (Row.diff r s) t)
#check (Row.union_diff_distrib (α := ServiceKey) :
  ∀ (r s t : Requirement), Row.diff (Row.union r s) t = Row.union (Row.diff r t) (Row.diff s t))

end RowDiff

/-! ## D1 — the signature and the provision algebra -/

section Algebra

#check (@LayerTy : Type)
#check (@LayerTy.mk : Requirement → Ty → Requirement → LayerTy)
#check (@LayerTy.out : LayerTy → Requirement)
#check (@LayerTy.error : LayerTy → Ty)
#check (@LayerTy.requires : LayerTy → Requirement)
#synth DecidableEq LayerTy

#check (@LayerTy.provide : LayerTy → LayerTy → LayerTy)
#check (@LayerTy.provideMerge : LayerTy → LayerTy → LayerTy)
#check (@LayerTy.merge : LayerTy → LayerTy → LayerTy)
#check (@LayerTy.orDie : LayerTy → LayerTy)
#check (@LayerTy.Closed : LayerTy → Prop)

#check (@LayerTy.provide_out : ∀ (s t : LayerTy), (s.provide t).out = s.out)
#check (@LayerTy.provideMerge_out :
  ∀ (s t : LayerTy), (s.provideMerge t).out = Row.union s.out t.out)
#check (@LayerTy.provide_requires_subset :
  ∀ (s t : LayerTy), Row.Subset (s.provide t).requires (Row.union s.requires t.requires))
#check (@LayerTy.provide_discharges :
  ∀ (s t : LayerTy) (key : ServiceKey), key ∈ t.out → key ∉ t.requires →
    key ∉ (s.provide t).requires)
#check (@LayerTy.provide_closed :
  ∀ (s t : LayerTy), t.Closed → Row.Subset s.requires t.out → (s.provide t).Closed)
#check (@LayerTy.covers_of_provide_closed :
  ∀ (s t : LayerTy), (s.provide t).Closed → ∀ (key : ServiceKey), key ∈ s.requires → key ∈ t.out)
#check (@LayerTy.provide_provide_rows :
  ∀ (l d₁ d₂ : LayerTy),
    ((l.provide d₁).provide d₂).out = (l.provide (d₁.provideMerge d₂)).out ∧
      ((l.provide d₁).provide d₂).requires = (l.provide (d₁.provideMerge d₂)).requires)
#check (@LayerTy.merge_rows_comm :
  ∀ (a b : LayerTy), (a.merge b).out = (b.merge a).out ∧ (a.merge b).requires = (b.merge a).requires)
#check (@LayerTy.merge_requires :
  ∀ (a b : LayerTy) (key : ServiceKey), key ∈ a.requires ∨ key ∈ b.requires →
    key ∈ (a.merge b).requires)

end Algebra

/-! ## D2 — the adjunction and the references -/

section Adjunction

#check (@satisfies_iff_subset_keysRow :
  ∀ (ctx : Ctx) (r : Requirement), ctx.Satisfies r ↔ Row.Subset r ctx.keysRow)
#check (@satisfies_merge_left :
  ∀ (a b : Ctx) (r : Requirement), a.Satisfies r → (a.merge b).Satisfies r)
#check (@satisfies_merge_right :
  ∀ (a b : Ctx) (r : Requirement), b.Satisfies r → (a.merge b).Satisfies r)
#check (@satisfiesRefs_of_defaults :
  ∀ (refs : Refs) (ctx : Ctx) (r : Requirement),
    (∀ key, key ∈ r → (refs.default? key).isSome = true) → SatisfiesRefs refs ctx r)
#check (@satisfiesRefs_of_hard :
  ∀ (refs : Refs) (ctx : Ctx) (r soft : Requirement),
    (∀ key, key ∈ soft → (refs.default? key).isSome = true) →
      ctx.Satisfies (Row.diff r soft) → SatisfiesRefs refs ctx r)

end Adjunction

/-! ## D3 — the term, its typing, the app -/

section Term

#check (@LayerTerm : Type → Type)
#check (@LayerTerm.succeed : ∀ {Op : Type}, ServiceKey → Lit → LayerTerm Op)
#check (@LayerTerm.effect : ∀ {Op : Type}, ServiceKey → Eff Op → LayerTerm Op)
#check (@LayerTerm.effectDiscard : ∀ {Op : Type}, Eff Op → LayerTerm Op)
#check (@LayerTerm.provide : ∀ {Op : Type}, LayerTerm Op → LayerTerm Op → LayerTerm Op)
#check (@LayerTerm.provideMerge : ∀ {Op : Type}, LayerTerm Op → LayerTerm Op → LayerTerm Op)
#check (@LayerTerm.merge : ∀ {Op : Type}, LayerTerm Op → LayerTerm Op → LayerTerm Op)
#check (@LayerTerm.fresh : ∀ {Op : Type}, LayerTerm Op → LayerTerm Op)
#check (@LayerTerm.orDie : ∀ {Op : Type}, LayerTerm Op → LayerTerm Op)
#synth DecidableEq (LayerTerm DocsOp)

#check (@layerTy : ∀ {Op : Type}, Signature Op → LayerTerm Op → Option LayerTy)
#check (@App : Type → Type)
#check (@appTy : ∀ {Op : Type}, Signature Op → App Op → Option EffTy)
#check (@appTy_closed_iff :
  ∀ {Op : Type} (sig : Signature Op) (app : App Op) (l : LayerTy) (p : EffTy),
    layerTy sig app.layer = some l → typeOf sig app.program = some p →
      ((appTy sig app).map EffTy.requires = some Requirement.empty ↔
        (l.Closed ∧ Row.Subset p.requires l.out)))

end Term

/-! ## D4 — the specification and its totality -/

section Build

#check (@build : ∀ {Op : Type}, LeafSem Op → LayerTerm Op → Ctx → Option Ctx)
#check (@build_total :
  ∀ {Op : Type} (sig : Signature Op) (sem : LeafSem Op), sem.Typed sig →
    ∀ (l : LayerTerm Op) (t : LayerTy) (ctx : Ctx), layerTy sig l = some t →
      ctx.Satisfies t.requires → ∃ out, build sem l ctx = some out ∧ out.Satisfies t.out)

end Build

/-! ## The register rows -/

section Register

/-- `E4-PROV-CE-001`, the typing half: siblings under `merge` keep the bindings required. -/
theorem sibling_mistake_stays_open :
    (layerTy docsSig siblingMistake).map LayerTy.requires =
      some (Requirement.ofList [dbBinding, rateBinding]) := by decide

/-- `E4-PROV-CE-001`, the positive control: `provideMerge` closes the same two layers. -/
theorem deployment_closed :
    (layerTy docsSig deploymentLayer).map LayerTy.requires = some Requirement.empty := by decide

-- `E4-PROV-CE-001`, the machine half: the mistake dies, the deployment builds.
#guard buildSucceeds docsSig siblingMistake = some false
#guard buildSucceeds docsSig deploymentLayer = some true

/-- `E4-PROV-CE-002`, the typing half: one signature. -/
theorem order_invisible_to_type : layerTy docsSig leftWins = layerTy docsSig rightWins := by decide

-- `E4-PROV-CE-002`, the run half: two contexts, through the specification and the machine.
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 1))
#guard buildServices docsSig leftWins = some [(10, 2), (3, 0)]
#guard buildServices docsSig rightWins = some [(10, 1), (3, 0)]

/-- `E4-PROV-CE-003` (`PROV-FB-ORDIE-DESC`): typed, not lowered. -/
theorem orDie_typed_not_lowered :
    (layerTy docsSig (.orDie servicesLayer)).map LayerTy.error = some Ty.never ∧
      lower docsSig (.orDie servicesLayer) = none := by decide

/-- `E4-PROV-CE-004` (`PROV-FB-STRING-VALUE`): a string literal is refused by the typing. -/
theorem string_value_refused : layerTy docsSig (.succeed dbKey (.str "db")) = none := by decide

end Register

end Test.Program.ProvisionContract
