import Effect4.Program.Provision
import Effect4.Surface.Deploy

/-!
# Surface.Provision — a wrangler configuration is a closed layer

Landed 2026-09-04 from the `workshop/Provision` spike (lane A). Plan and grill:
`docs/research/2026-09-04-provision-algebra.md` §4; battery
`Test/Surface/ProvisionContract.lean`. The namespace is `Effect4.Program.Provision.Deploy`,
the join's home in the algebra; the file sits under `Surface/` because it is the one place
`Surface` imports `Program` (`docs/ARCHITECTURE.md`).

**The thesis, in one sentence.** A cloud deployment — the `Deployment` carrier of
`src/Effect4/Surface/Deploy.lean`, which is a wrangler configuration — *is* a closed layer: its
bindings are the platform's provisions (`Layer.succeed` leaves), its `provides` rows are
services built from those bindings (`Layer.effect` leaves that read one binding), the
deployment is `servicesLayer.pipe(Layer.provideMerge(bindingsLayer))`, and the string-level
deployment law `Deployment.satisfies` is a shadow of the row law `LayerTy.provide_closed`.

What this module adds, and what it deliberately reuses:

* **Reused, never re-declared.** Everything of `src/Effect4/Program/Provision.lean`: `LayerTy` and its
  provision algebra (`provide`, `provideMerge`, `merge`, `Closed`, `provide_closed`),
  `LayerTerm` and `LayerTerm.mergeAll`, `layerTy`, `bodyRequires`, `litVal`, the
  specification `build` with its `LeafSem` hook, `specKeys`, and the machine probes
  `lower`, `buildSucceeds`, `buildServices`, `provideThenService`. Everything of
  `src/Effect4/Surface/Deploy.lean`: `Deployment`, `Binding`, `builtinProvider`,
  `Deployment.bindingNames`, `Deployment.provided`, `Deployment.ProvidersKnown`,
  `Deployment.mountedRequirements`, `Deployment.RequirementsMet`, `Deployment.satisfies`
  and the `docs` fixture. Nothing here re-states a row law: `Row.diff`, `Row.union`,
  `Row.mem_diff`, `Row.diff_eq_empty_iff_subset` are the ones already proved.
* **A name table.** `ServiceKey` is a pair of `Nat`s (`src/Effect4/Machine/Key.lean`), and a
  wrangler binding is a `String`. `indexOf`/`keyOf` are the model's stand-in for rc.112's
  tag-string identity (`Context.ts:32-41`, `Context.Service("…")`, read off its uses at
  `internal/effect.ts:2069`): a name is a service exactly when the table lists it, and its
  key is its position. **The table's key is its index shifted past the machine's four
  well-known keys**, `⟨⟨i+4⟩, ⟨i+4⟩⟩`; see "Why the shift is four" below. The first
  consequence is `keyOf_ne_scopeKey`, which is what makes the effect leaf's requirement row
  a theorem rather than a hypothesis: a `Layer.effect` leaf's row is `Exclude<R,
  Scope.Scope>` (`Layer.ts:1438`), so a binding whose key *were* the scope key would be
  silently discharged by the layer's own scope and the closure theorem below would be
  vacuous at that binding.
* **The deployment alphabet.** One operation, `DeployOp.fromBinding`, whose row requires
  exactly the binding it reads: `Layer.effect` (`Layer.ts:1427`) over `Effect.service`
  (`internal/effect.ts:2069`). One operation is the whole alphabet a wrangler configuration
  needs, because `env.<NAME>` is the only capability a worker has that the configuration
  names.
* **The lowering.** `bindingsLayer`, `servicesLayer`, `deploymentLayer`, all in `Option`:
  a name the table does not know is `none`, which is the type refusing exactly what
  `Deployment.check`'s `providerUnknown` refuses.
* **`deploymentLayer_closed`**, the point of the module: a deployment whose providers are
  known lowers to a layer whose requirement row is empty. The route is
  `LayerTy.provide_closed` over `Row.diff_eq_empty_iff_subset`, with
  `Deployment.ProvidersKnown` supplying the subset.
* **`requirementsMet_row`**, the relation between the two laws: the string law
  (`Deployment.RequirementsMet`) implies the row law (the key is in the layer's output row).
  The converse fails, and the `#guard`s below exhibit the gap: it is exactly the bindings.

## Which law rc.112 would accept

A deployment whose mounted api requires the *binding* name `DB` is refused by
`Deployment.satisfies` with `requirementUnprovided`, because `DB` has no `provides` row —
yet the layer's output row contains `DB`'s key, because `Layer.provideMerge`
(`Layer.ts:2704`) keeps the dependency's outputs visible. **The row law is the faithful
one**: in the worker, `env.DB` *is* a service of the fiber's context, so a handler that
asks for it type-checks and runs; the string law is stricter than the row law by exactly the
bindings, and that strictness is a lint, not a soundness clause.

## Why the shift is four, and not one

Avoiding `scopeKey` alone needs only `i+1`. The machine reserves **four** key names —
`scopeKey` 0, `maxOpsKey` 1, `preventYieldKey` 2, `currentMemoMapKey` 3
(`src/Effect4/Machine/Context.lean:912-922`) — and at `i+1` the `docs` table below mints all
three of the others. That is not a naming clash; two of the three are live defects, and the
machine exhibits them:

* A binding at `maxOpsKey` whose value is `0` — the first binding of any deployment, at
  `i+1` — is read back by `budgetOf` as `MaxOpsBeforeYield := 0` (`Scheduler.ts:269-272`).
  `Layer.provideMerge` installs the built context into the dependent's build
  (`internal/effect.ts:2197`), so the services build yields before every step, the root never
  exits, and `runSyncExit` answers `Cause.die(AsyncFiberError)` (`:5543`). The `#guard`s in
  the witness section pin exactly that, both ways.
* A binding at `currentMemoMapKey` is overwritten by `Layer.build`'s trailing
  `Context.add(CurrentMemoMap, memoMap)` (`Layer.ts:762`).

So `keyOf` shifts by four. Nothing in the theorems depends on the size of the shift — only
`keyOf_ne_scopeKey` does, and `i+1` would already give that — but every machine receipt does,
and a model whose first binding silently starves the scheduler is not a model of a wrangler
configuration. The still-owed row is the general one: a `keyOf` that a *landing* could use
has to be given the reserved set rather than a hard-coded offset.

## Owed row: `Layer.empty` as the seed of the fold

`mergeLeaves` folds a non-empty leaf list with its own head, not with `emptyLayer`, and uses
`emptyLayer` only for the empty list. Seeding with `Layer.empty` is the same *type* (the
`#guard`s below show the seeded and unseeded folds agree on every row), but it costs one
extra memoized description and one extra `mergeAll` fork level per side, and the `docs`
fixture then does not finish inside the fixed 512-step budget of
`src/Effect4/Program/Provision.lean`'s `runOver` — `buildSucceeds` answers `some false` where the unseeded fold answers `some true`.
Both receipts are `#guard`s below. The unseeded fold is also the closer reading of
`Layer.mergeAll(l, …)` (`Layer.ts:1652`), whose first argument is a layer. Whether the
machine's build of the seeded fold merely needs more fuel, or is quadratic in the fold's
depth, is the owed row; this module measures, it does not diagnose.

Every rc.112 line named here is in `vendor/effect-4.0.0-rc.112/src/`.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision.Deploy

open Effect4
open Effect4.Machine.Env (Requirement Ctx Context scopeKey)

/-! ## Names to keys

The model's stand-in for rc.112's tag-string identity. `indexOf` is written out rather than
spelled `List.idxOf?` so that the recursion is the structural one the kernel reduces. -/

/-- The position of a name in the table, or `none`. -/
def indexOf : List String → String → Option Nat
  | [], _ => none
  | entry :: rest, name => if entry == name then some 0 else (indexOf rest name).map (· + 1)

/-- The number of key names the machine reserves: `scopeKey` 0, `maxOpsKey` 1,
`preventYieldKey` 2, `currentMemoMapKey` 3 (`src/Effect4/Machine/Context.lean:912-922`). -/
def reservedKeys : Nat := 4

/-- The key a name mints: its position **shifted past the reserved keys**, so no name can
mint `scopeKey`, the scheduler's two references, or the memo map. See the header. -/
def keyOf (names : List String) (name : String) : Option ServiceKey :=
  (indexOf names name).map fun i => ⟨⟨i + reservedKeys⟩, ⟨i + reservedKeys⟩⟩

/-- No name's key is the ambient scope's key: the shift, as a theorem. This is what makes
`Exclude<R, Scope.Scope>` (`Layer.ts:1438`) remove nothing from an effect leaf's row. -/
theorem keyOf_ne_scopeKey {names : List String} {name : String} {key : ServiceKey}
    (h : keyOf names name = some key) : key ≠ scopeKey := by
  unfold keyOf at h
  cases hi : indexOf names name with
  | none =>
    rw [hi] at h
    exact absurd h (by simp)
  | some i =>
    rw [hi] at h
    have he : (⟨⟨i + reservedKeys⟩, ⟨i + reservedKeys⟩⟩ : ServiceKey) = key := Option.some.inj h
    intro hcontra
    exact Nat.succ_ne_zero (i + 3) (congrArg (fun k => k.name.value) (he.trans hcontra))

/-! ## The alphabet: one operation, `env.<NAME>` -/

/-- The deployment alphabet. `fromBinding binding service` is the body of the
`Layer.effect` leaf that builds `service` by reading the platform's `binding`. -/
inductive DeployOp
  /-- Build a service from one binding of the deployment's environment. -/
  | fromBinding (binding service : ServiceKey)
deriving DecidableEq, Repr

/-- The row of the one operation: its `requires` is exactly the binding it reads. -/
def DeployOp.row : DeployOp → Row
  | .fromBinding binding _ =>
    ⟨"fromBinding", "fromBinding", .call, [], .sync, .unit, .unit, .never, [binding],
      "Layer.ts:1427 (Layer.effect) over internal/effect.ts:2069 (Effect.service)"⟩

/-- The signature: the one row, no pure atoms, the machine's ambient scope key. -/
def deploySig : Signature DeployOp := ⟨DeployOp.row, fun _ _ => none, scopeKey⟩

/-! ## The layers -/

/-- `Layer.empty` (`Layer.ts:1155`): provides nothing, requires nothing. It is the seed of
every fold below, so the empty deployment and the empty `provides` list are uniform. -/
def emptyLayer : LayerTerm DeployOp := .effectDiscard (.succeed (.lit .unit))

/-- The signature of `emptyLayer`. -/
def emptyLayerTy : LayerTy := ⟨Requirement.empty, Ty.never, Requirement.empty⟩

/-- One binding, as `Layer.succeed(key, value)` (`Layer.ts:1074`). The value is the
binding's index: the model's stand-in for the `env.<NAME>` object, as it is for every
host-minted object. -/
def bindingLeaf (key : ServiceKey) (index : Nat) : LayerTerm DeployOp :=
  LayerTerm.succeed key (Lit.nat index)

/-- A service the worker itself provides (`builtinProvider`): a value already in hand. -/
def builtinLeaf (service : ServiceKey) : LayerTerm DeployOp :=
  LayerTerm.succeed service Lit.unit

/-- A service built from one binding: `Layer.effect(key, Effect.service(binding))`. -/
def bindingServiceLeaf (binding service : ServiceKey) : LayerTerm DeployOp :=
  LayerTerm.effect service
    (Eff.perform (DeployOp.fromBinding binding service) (Term.lit Lit.unit))

/-- The binding leaves, in declaration order, with each binding's index as its value;
`none` when the table does not know a binding's name. -/
def bindingLeaves (names : List String) :
    Nat → List Surface.Binding → Option (List (LayerTerm DeployOp))
  | _, [] => some []
  | i, b :: rest => do
    let key ← keyOf names b.name
    let tail ← bindingLeaves names (i + 1) rest
    some (bindingLeaf key i :: tail)

/-- One `provides` row as a leaf. -/
def serviceLeaf (names : List String) (row : String × String) : Option (LayerTerm DeployOp) :=
  if row.2 = Surface.builtinProvider then
    (keyOf names row.1).map builtinLeaf
  else do
    let service ← keyOf names row.1
    let provider ← keyOf names row.2
    some (bindingServiceLeaf provider service)

/-- The service leaves, in `provides` order. -/
def serviceLeaves (names : List String) :
    List (String × String) → Option (List (LayerTerm DeployOp))
  | [] => some []
  | row :: rest => do
    let leaf ← serviceLeaf names row
    let tail ← serviceLeaves names rest
    some (leaf :: tail)

/-- `Layer.mergeAll(l, …)` (`Layer.ts:1652`), with `Layer.empty` for the empty list so the
function is total and the empty deployment still lowers. Seeding the *non-empty* fold with
`emptyLayer` gives the same rows and a build the machine does not finish inside `runOver`'s
fixed budget; see the header's owed row and the `#guard`s in the witness section. -/
def mergeLeaves : List (LayerTerm DeployOp) → LayerTerm DeployOp
  | [] => emptyLayer
  | l :: rest => LayerTerm.mergeAll l rest

/-- The platform layer: every binding, value in hand. -/
def bindingsLayer (names : List String) (dep : Surface.Deployment) :
    Option (LayerTerm DeployOp) :=
  (bindingLeaves names 0 dep.bindings).map mergeLeaves

/-- The services layer: every `provides` row, built from its provider. -/
def servicesLayer (names : List String) (dep : Surface.Deployment) :
    Option (LayerTerm DeployOp) :=
  (serviceLeaves names dep.provides).map mergeLeaves

/-- **The deployment as a layer**: `servicesLayer.pipe(Layer.provideMerge(bindingsLayer))`
(`Layer.ts:2704`). `provideMerge` rather than `provide` because the worker's `env` stays
ambient: a handler may read `env.DB` directly, so the bindings remain visible. -/
def deploymentLayer (names : List String) (dep : Surface.Deployment) :
    Option (LayerTerm DeployOp) := do
  let services ← servicesLayer names dep
  let bindings ← bindingsLayer names dep
  some (LayerTerm.provideMerge services bindings)

/-! ## The rows of a list of leaves, and the typing of the fold -/

/-- The union of the output rows of a list of leaves; `none` if one is ill-typed. -/
def outsOf : List (LayerTerm DeployOp) → Option Requirement
  | [] => some Requirement.empty
  | l :: rest => do
    let t ← layerTy deploySig l
    let o ← outsOf rest
    some (Row.union t.out o)

/-- The union of the requirement rows of a list of leaves. -/
def reqsOf : List (LayerTerm DeployOp) → Option Requirement
  | [] => some Requirement.empty
  | l :: rest => do
    let t ← layerTy deploySig l
    let r ← reqsOf rest
    some (Row.union t.requires r)

theorem outsOf_cons (l : LayerTerm DeployOp) (rest : List (LayerTerm DeployOp)) (t : LayerTy)
    (o : Requirement) (hl : layerTy deploySig l = some t) (ho : outsOf rest = some o) :
    outsOf (l :: rest) = some (Row.union t.out o) := by
  simp [outsOf, hl, ho]

theorem reqsOf_cons (l : LayerTerm DeployOp) (rest : List (LayerTerm DeployOp)) (t : LayerTy)
    (r : Requirement) (hl : layerTy deploySig l = some t) (hr : reqsOf rest = some r) :
    reqsOf (l :: rest) = some (Row.union t.requires r) := by
  simp [reqsOf, hl, hr]


/-- **The fold types, and its rows are the unions.** `Layer.mergeAll` is a left fold of
`merge` (`Layer.ts:1652-1658`) and `merge` unions every row (`:1751`), so the accumulator is
generalised and the induction is over the list. -/
theorem layerTy_mergeAll :
    ∀ (rest : List (LayerTerm DeployOp)) (first : LayerTerm DeployOp) (f : LayerTy)
      (o r : Requirement),
      layerTy deploySig first = some f → outsOf rest = some o → reqsOf rest = some r →
      ∃ t, layerTy deploySig (LayerTerm.mergeAll first rest) = some t ∧
        t.out = Row.union f.out o ∧ t.requires = Row.union f.requires r := by
  intro rest
  induction rest with
  | nil =>
    intro first f o r hf ho hr
    have ho' : Requirement.empty = o := Option.some.inj ho
    have hr' : Requirement.empty = r := Option.some.inj hr
    subst ho'
    subst hr'
    exact ⟨f, hf, (Row.union_empty_right f.out).symm, (Row.union_empty_right f.requires).symm⟩
  | cons l rest ih =>
    intro first f o r hf ho hr
    cases hl : layerTy deploySig l with
    | none => simp [outsOf, hl] at ho
    | some tl =>
      cases ho' : outsOf rest with
      | none => simp [outsOf, hl, ho'] at ho
      | some o' =>
        cases hr' : reqsOf rest with
        | none => simp [reqsOf, hl, hr'] at hr
        | some r' =>
          have hoo : Row.union tl.out o' = o := by
            have := outsOf_cons l rest tl o' hl ho'
            rw [this] at ho
            exact Option.some.inj ho
          have hrr : Row.union tl.requires r' = r := by
            have := reqsOf_cons l rest tl r' hl hr'
            rw [this] at hr
            exact Option.some.inj hr
          have hmerge : layerTy deploySig (LayerTerm.merge first l) = some (f.merge tl) := by
            simp [layerTy, hf, hl]
          obtain ⟨t, ht, htout, htreq⟩ :=
            ih (LayerTerm.merge first l) (f.merge tl) o' r' hmerge ho' hr'
          refine ⟨t, ht, ?_, ?_⟩
          · rw [htout, ← hoo]
            exact Row.union_assoc f.out tl.out o'
          · rw [htreq, ← hrr]
            exact Row.union_assoc f.requires tl.requires r'

/-! ## The leaf signatures -/

theorem layerTy_emptyLayer : layerTy deploySig emptyLayer = some emptyLayerTy := rfl

/-- **The fold of a leaf list types, and its rows are the unions of the leaves' rows.** -/
theorem layerTy_mergeLeaves (leaves : List (LayerTerm DeployOp)) (o r : Requirement)
    (ho : outsOf leaves = some o) (hr : reqsOf leaves = some r) :
    ∃ t, layerTy deploySig (mergeLeaves leaves) = some t ∧ t.out = o ∧ t.requires = r := by
  cases leaves with
  | nil =>
    have ho' : Requirement.empty = o := Option.some.inj ho
    have hr' : Requirement.empty = r := Option.some.inj hr
    subst ho'
    subst hr'
    exact ⟨emptyLayerTy, layerTy_emptyLayer, rfl, rfl⟩
  | cons l rest =>
    cases hl : layerTy deploySig l with
    | none => simp [outsOf, hl] at ho
    | some tl =>
      cases ho' : outsOf rest with
      | none => simp [outsOf, hl, ho'] at ho
      | some o' =>
        cases hr' : reqsOf rest with
        | none => simp [reqsOf, hl, hr'] at hr
        | some r' =>
          have hoo : Row.union tl.out o' = o := by
            rw [outsOf_cons l rest tl o' hl ho'] at ho
            exact Option.some.inj ho
          have hrr : Row.union tl.requires r' = r := by
            rw [reqsOf_cons l rest tl r' hl hr'] at hr
            exact Option.some.inj hr
          obtain ⟨t, ht, htout, htreq⟩ := layerTy_mergeAll rest l tl o' r' hl ho' hr'
          exact ⟨t, ht, by rw [htout, hoo], by rw [htreq, hrr]⟩

theorem layerTy_bindingLeaf (key : ServiceKey) (index : Nat) :
    layerTy deploySig (bindingLeaf key index) =
      some ⟨Requirement.single key, Ty.never, Requirement.empty⟩ := rfl

theorem layerTy_builtinLeaf (service : ServiceKey) :
    layerTy deploySig (builtinLeaf service) =
      some ⟨Requirement.single service, Ty.never, Requirement.empty⟩ := rfl

/-- Two distinct singletons: the difference is the left one. -/
theorem diff_single_ne (a b : ServiceKey) (hne : a ≠ b) :
    Row.diff (Requirement.single a) (Requirement.single b) = Requirement.single a := by
  apply Row.eq_of_mem_iff
  intro x
  rw [Row.mem_diff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun hs => ?_⟩
    have hxa : x = a := (Row.mem_singleton a x).mp h
    have hxb : x = b := (Row.mem_singleton b x).mp hs
    exact hne (hxa.symm.trans hxb)

/-- **A `fromBinding` leaf provides its service and requires its binding.** The `Exclude<R,
Scope.Scope>` of `Layer.ts:1438` removes only `scopeKey`, and `keyOf_ne_scopeKey` says the
binding is not that. -/
theorem layerTy_bindingServiceLeaf (binding service : ServiceKey) (hne : binding ≠ scopeKey) :
    layerTy deploySig (bindingServiceLeaf binding service) =
      some ⟨Requirement.single service, Ty.never, Requirement.single binding⟩ := by
  show some (⟨Requirement.single service, Ty.never,
      Row.diff (Requirement.single binding) (Requirement.single scopeKey)⟩ : LayerTy) = _
  rw [diff_single_ne binding scopeKey hne]

/-! ## The rows of the two generated leaf lists -/

/-- The binding leaves type, require nothing, and their output row holds the key of every
binding name the table knows. -/
theorem bindings_rows (names : List String) :
    ∀ (bs : List Surface.Binding) (i : Nat) (leaves : List (LayerTerm DeployOp)),
      bindingLeaves names i bs = some leaves →
      ∃ o, outsOf leaves = some o ∧ reqsOf leaves = some Requirement.empty ∧
        ∀ nm ∈ bs.map Surface.Binding.name, ∀ key, keyOf names nm = some key → key ∈ o := by
  intro bs
  induction bs with
  | nil =>
    intro i leaves h
    have hl : ([] : List (LayerTerm DeployOp)) = leaves := Option.some.inj h
    subst hl
    refine ⟨Requirement.empty, rfl, rfl, ?_⟩
    intro nm hnm
    simp at hnm
  | cons b rest ih =>
    intro i leaves h
    cases hk : keyOf names b.name with
    | none => simp [bindingLeaves, hk] at h
    | some kb =>
      cases ht : bindingLeaves names (i + 1) rest with
      | none => simp [bindingLeaves, hk, ht] at h
      | some tail =>
        have hleaves : bindingLeaf kb i :: tail = leaves := by
          have : bindingLeaves names i (b :: rest) = some (bindingLeaf kb i :: tail) := by
            simp [bindingLeaves, hk, ht]
          rw [this] at h
          exact Option.some.inj h
        subst hleaves
        obtain ⟨o', ho', hr', hmem⟩ := ih (i + 1) tail ht
        refine ⟨Row.union (Requirement.single kb) o', ?_, ?_, ?_⟩
        · exact outsOf_cons _ _ _ _ (layerTy_bindingLeaf kb i) ho'
        · rw [reqsOf_cons _ _ _ _ (layerTy_bindingLeaf kb i) hr']
          exact congrArg some (Row.union_empty_left Requirement.empty)
        · intro nm hnm key hkey
          rw [List.map_cons, List.mem_cons] at hnm
          rcases hnm with heq | hin
          · subst heq
            have hsame : key = kb := Option.some.inj (hkey.symm.trans hk)
            exact (Row.mem_union key _ _).mpr (Or.inl ((Row.mem_singleton kb key).mpr hsame))
          · exact (Row.mem_union key _ _).mpr (Or.inr (hmem nm hin key hkey))

/-- The service leaves type; their output row holds the key of every provided service name,
and every member of their requirement row is the key of a non-builtin provider. -/
theorem services_rows (names : List String) :
    ∀ (rows : List (String × String)) (leaves : List (LayerTerm DeployOp)),
      serviceLeaves names rows = some leaves →
      ∃ o r, outsOf leaves = some o ∧ reqsOf leaves = some r ∧
        (∀ row ∈ rows, ∀ key, keyOf names row.1 = some key → key ∈ o) ∧
        (∀ key, key ∈ r → ∃ row ∈ rows, row.2 ≠ Surface.builtinProvider ∧
          keyOf names row.2 = some key) := by
  intro rows
  induction rows with
  | nil =>
    intro leaves h
    have hl : ([] : List (LayerTerm DeployOp)) = leaves := Option.some.inj h
    subst hl
    refine ⟨Requirement.empty, Requirement.empty, rfl, rfl, ?_, ?_⟩
    · intro row hrow
      simp at hrow
    · intro key hkey
      exact absurd hkey (Row.not_mem_empty key)
  | cons row rest ih =>
    intro leaves h
    cases hleaf : serviceLeaf names row with
    | none => simp [serviceLeaves, hleaf] at h
    | some leaf =>
      cases htail : serviceLeaves names rest with
      | none => simp [serviceLeaves, hleaf, htail] at h
      | some tail =>
        have hleaves : leaf :: tail = leaves := by
          have : serviceLeaves names (row :: rest) = some (leaf :: tail) := by
            simp [serviceLeaves, hleaf, htail]
          rw [this] at h
          exact Option.some.inj h
        subst hleaves
        obtain ⟨o', r', ho', hr', hout', hreq'⟩ := ih tail htail
        by_cases hb : row.2 = Surface.builtinProvider
        · -- a builtin: a `Layer.succeed` leaf, requiring nothing
          cases hs : keyOf names row.1 with
          | none => rw [serviceLeaf, if_pos hb, hs] at hleaf; exact absurd hleaf (by simp)
          | some service =>
            have hform : leaf = builtinLeaf service := by
              rw [serviceLeaf, if_pos hb, hs] at hleaf
              exact (Option.some.inj hleaf).symm
            subst hform
            refine ⟨Row.union (Requirement.single service) o', Row.union Requirement.empty r',
              outsOf_cons _ _ _ _ (layerTy_builtinLeaf service) ho',
              reqsOf_cons _ _ _ _ (layerTy_builtinLeaf service) hr', ?_, ?_⟩
            · intro row' hrow' key hkey
              rcases List.mem_cons.mp hrow' with heq | hin
              · subst heq
                have hsame : key = service := Option.some.inj (hkey.symm.trans hs)
                exact (Row.mem_union key _ _).mpr
                  (Or.inl ((Row.mem_singleton service key).mpr hsame))
              · exact (Row.mem_union key _ _).mpr (Or.inr (hout' row' hin key hkey))
            · intro key hkey
              rcases (Row.mem_union key _ _).mp hkey with he | hin
              · exact absurd he (Row.not_mem_empty key)
              · obtain ⟨row'', hrow'', hne'', hk''⟩ := hreq' key hin
                exact ⟨row'', List.mem_cons_of_mem row hrow'', hne'', hk''⟩
        · -- a binding-backed service: a `Layer.effect` leaf requiring its provider
          cases hs : keyOf names row.1 with
          | none =>
            rw [serviceLeaf, if_neg hb, hs] at hleaf
            exact absurd hleaf (by simp)
          | some service =>
            cases hp : keyOf names row.2 with
            | none =>
              rw [serviceLeaf, if_neg hb, hs, hp] at hleaf
              exact absurd hleaf (by simp)
            | some provider =>
              have hform : leaf = bindingServiceLeaf provider service := by
                rw [serviceLeaf, if_neg hb, hs, hp] at hleaf
                exact (Option.some.inj hleaf).symm
              subst hform
              have hty := layerTy_bindingServiceLeaf provider service (keyOf_ne_scopeKey hp)
              refine ⟨Row.union (Requirement.single service) o',
                Row.union (Requirement.single provider) r',
                outsOf_cons _ _ _ _ hty ho', reqsOf_cons _ _ _ _ hty hr', ?_, ?_⟩
              · intro row' hrow' key hkey
                rcases List.mem_cons.mp hrow' with heq | hin
                · subst heq
                  have hsame : key = service := Option.some.inj (hkey.symm.trans hs)
                  exact (Row.mem_union key _ _).mpr
                    (Or.inl ((Row.mem_singleton service key).mpr hsame))
                · exact (Row.mem_union key _ _).mpr (Or.inr (hout' row' hin key hkey))
              · intro key hkey
                rcases (Row.mem_union key _ _).mp hkey with he | hin
                · have hsame : key = provider := (Row.mem_singleton provider key).mp he
                  exact ⟨row, List.mem_cons_self, hb, by rw [hp, hsame]⟩
                · obtain ⟨row'', hrow'', hne'', hk''⟩ := hreq' key hin
                  exact ⟨row'', List.mem_cons_of_mem row hrow'', hne'', hk''⟩

/-! ## The signature of a whole deployment -/

/-- Every provider of a deployment whose `providersKnown` clause holds is a binding name or
the builtin. This is `Deployment.provider_is_binding_or_builtin` read off the clause alone,
without the other nine clauses of `WellFormed`. -/
theorem provider_known (dep : Surface.Deployment)
    (h : Surface.Deployment.ProvidersKnown dep) (row : String × String)
    (mem : row ∈ dep.provides) :
    row.2 = Surface.builtinProvider ∨ dep.bindingNames.contains row.2 = true := by
  have hp : Surface.Deployment.providerKnown dep row.2 = true :=
    List.all_eq_true.mp h row mem
  rcases Bool.or_eq_true_iff.mp hp with hl | hr
  · exact Or.inl (eq_of_beq hl)
  · exact Or.inr hr

/-- **The shape of a lowered deployment.** Everything both theorems below need, proved once:
the layer types as `services.provideMerge bindings`, the bindings close, the services'
requirement row is a row of provider keys, and each layer's output row is what the two leaf
lists give. -/
theorem deploymentLayer_shape (names : List String) (dep : Surface.Deployment)
    (l : LayerTerm DeployOp) (h : deploymentLayer names dep = some l) :
    ∃ (ts tb : LayerTy) (so sr bo : Requirement),
      layerTy deploySig l = some (ts.provideMerge tb) ∧
        ts.out = so ∧ ts.requires = sr ∧ tb.out = bo ∧
        tb.requires = Requirement.empty ∧
        (∀ row ∈ dep.provides, ∀ key, keyOf names row.1 = some key → key ∈ so) ∧
        (∀ key, key ∈ sr → ∃ row ∈ dep.provides, row.2 ≠ Surface.builtinProvider ∧
          keyOf names row.2 = some key) ∧
        (∀ nm ∈ dep.bindingNames, ∀ key, keyOf names nm = some key → key ∈ bo) := by
  cases hsl : serviceLeaves names dep.provides with
  | none => simp [deploymentLayer, servicesLayer, hsl] at h
  | some sLeaves =>
    cases hbl : bindingLeaves names 0 dep.bindings with
    | none => simp [deploymentLayer, servicesLayer, bindingsLayer, hsl, hbl] at h
    | some bLeaves =>
      have hform : LayerTerm.provideMerge (mergeLeaves sLeaves) (mergeLeaves bLeaves) = l := by
        have : deploymentLayer names dep =
            some (LayerTerm.provideMerge (mergeLeaves sLeaves) (mergeLeaves bLeaves)) := by
          simp [deploymentLayer, servicesLayer, bindingsLayer, hsl, hbl]
        rw [this] at h
        exact Option.some.inj h
      subst hform
      obtain ⟨bo, hbo, hbr, hbmem⟩ := bindings_rows names dep.bindings 0 bLeaves hbl
      obtain ⟨so, sr, hso, hsr, hsout, hsreq⟩ := services_rows names dep.provides sLeaves hsl
      obtain ⟨tb, htb, htbout, htbreq⟩ := layerTy_mergeLeaves bLeaves bo Requirement.empty hbo hbr
      obtain ⟨ts, hts, htsout, htsreq⟩ := layerTy_mergeLeaves sLeaves so sr hso hsr
      exact ⟨ts, tb, so, sr, bo, by simp [layerTy, hts, htb], htsout, htsreq, htbout, htbreq,
        hsout, hsreq, hbmem⟩

/-! ## The closure theorem -/

/-- **A deployment whose providers are known is a closed layer.** `Layer<ROut, E, never>`:
nothing is left for the host to supply, which is the sentence `Effect.provide(program,
layer)` type-checks by and the sentence `wrangler deploy` is checked by. The route is
`LayerTy.provide_closed` (`src/Effect4/Program/Provision.lean`) over `Row.diff_eq_empty_iff_subset`, with
`Deployment.ProvidersKnown` putting every provider among the bindings. -/
theorem deploymentLayer_closed (names : List String) (dep : Surface.Deployment)
    (l : LayerTerm DeployOp) (h : deploymentLayer names dep = some l)
    (hknown : Surface.Deployment.ProvidersKnown dep) :
    (layerTy deploySig l).map LayerTy.requires = some Requirement.empty := by
  obtain ⟨ts, tb, so, sr, bo, hty, _, htsreq, htbout, htbreq, _, hsreq, hbmem⟩ :=
    deploymentLayer_shape names dep l h
  have hbclosed : tb.Closed := htbreq
  have hcovers : Row.Subset ts.requires tb.out := by
    intro key hkey
    rw [htsreq] at hkey
    obtain ⟨row, hrow, hne, hkeyof⟩ := hsreq key hkey
    have hbn : row.2 ∈ dep.bindingNames := by
      rcases provider_known dep hknown row hrow with hb | hc
      · exact absurd hb hne
      · exact List.mem_of_elem_eq_true hc
    rw [htbout]
    exact hbmem row.2 hbn key hkeyof
  have hclosed : (ts.provide tb).requires = Requirement.empty :=
    LayerTy.provide_closed ts tb hbclosed hcovers
  rw [hty]
  exact congrArg some hclosed

/-! ## The two deployment laws, related -/

/-- **The string law implies the row law.** Every requirement of every mounted api that the
deployment's `provides` rows meet is a key of the lowered layer's output row. -/
theorem requirementsMet_row (names : List String) (dep : Surface.Deployment)
    (reqs : List (String × List String)) (l : LayerTerm DeployOp)
    (h : deploymentLayer names dep = some l)
    (hmet : Surface.Deployment.RequirementsMet dep reqs) :
    ∀ service ∈ Surface.Deployment.mountedRequirements dep reqs,
      ∀ key, keyOf names service = some key →
        (layerTy deploySig l).map (fun t => decide (key ∈ t.out)) = some true := by
  obtain ⟨ts, tb, so, sr, bo, hty, htsout, _, _, _, hsout, _, _⟩ :=
    deploymentLayer_shape names dep l h
  intro service hservice key hkey
  have hc : dep.provided.contains service = true := List.all_eq_true.mp hmet service hservice
  have hmem : service ∈ dep.provided := List.mem_of_elem_eq_true hc
  obtain ⟨row, hrow, hrow1⟩ := List.mem_map.mp hmem
  have hkey' : keyOf names row.1 = some key := by rw [hrow1]; exact hkey
  have hin : key ∈ ts.out := by
    rw [htsout]
    exact hsout row hrow key hkey'
  rw [hty]
  exact congrArg some (decide_eq_true ((Row.mem_union key ts.out tb.out).mpr (Or.inl hin)))

/-! ## Witnesses on the `docs` fixture of the Surface plan's §13.3 -/

section Witnesses

/-- The name table: four bindings, then the two services they provide. -/
def docsNames : List String := ["RATE", "DB", "SITE_URL", "BUILD_COMMIT", "Db", "RateLimit"]

/-- The keys the table mints: its index shifted past the machine's four reserved names. -/
def rateBindingKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def dbBindingKey : ServiceKey := ⟨⟨5⟩, ⟨5⟩⟩
def siteUrlKey : ServiceKey := ⟨⟨6⟩, ⟨6⟩⟩
def buildCommitKey : ServiceKey := ⟨⟨7⟩, ⟨7⟩⟩
def dbServiceKey : ServiceKey := ⟨⟨8⟩, ⟨8⟩⟩
def rateLimitKey : ServiceKey := ⟨⟨9⟩, ⟨9⟩⟩

#guard docsNames.map (keyOf docsNames) =
  [some rateBindingKey, some dbBindingKey, some siteUrlKey, some buildCommitKey,
    some dbServiceKey, some rateLimitKey]
#guard keyOf docsNames "nope" = none
-- the shift: no name reaches the machine's four reserved key names
#guard (docsNames.map (keyOf docsNames)).all fun k =>
  match k with
  | some key => reservedKeys ≤ key.name.value
  | none => false
#guard keyOf docsNames "RATE" ≠ some scopeKey
#guard keyOf docsNames "RATE" ≠ some Effect4.Machine.Env.maxOpsKey
#guard keyOf docsNames "SITE_URL" ≠ some Effect4.Machine.Env.currentMemoMapKey

/-- The leaf semantics of the deployment alphabet, exactly `docsSem`'s shape: a body that
performs one row reads the row's one required service and binds it as the new service (the
machine's `Construction.fromService`); a literal body binds the literal. -/
def deploySem : LeafSem DeployOp where
  effect := fun _ body ctx =>
    match body with
    | .perform op _ =>
      match (DeployOp.row op).requires with
      | [input] => ctx.getV input
      | _ => none
    | .succeed (.lit value) => litVal value
    | _ => none
  discard := fun body _ =>
    match body with
    | .succeed (.lit _) => some ()
    | _ => none

/-- The `docs` deployment, lowered. -/
def docsLayer : Option (LayerTerm DeployOp) :=
  deploymentLayer docsNames Surface.docsDeployment

/-- The key names of a row, for a readable receipt. -/
def keyNames (r : Requirement) : List Nat := r.elems.map fun k => k.name.value

-- the lowering answers
#guard docsLayer.isSome

-- the type: closed, and providing all six keys
#guard (docsLayer.bind fun l => (layerTy deploySig l).map LayerTy.requires) =
  some Requirement.empty
#guard (docsLayer.bind fun l => (layerTy deploySig l).map LayerTy.out) =
  some (Requirement.ofList [rateBindingKey, dbBindingKey, siteUrlKey, buildCommitKey,
    dbServiceKey, rateLimitKey])
#guard (docsLayer.bind fun l => (layerTy deploySig l).map (fun t => keyNames t.out)) =
  some [4, 5, 6, 7, 8, 9]

-- the specification builds the six services, bindings first
#guard (docsLayer.bind fun l => specKeys deploySem l) = some [4, 5, 6, 7, 8, 9]
-- and each service holds its binding's index: `Db` from `DB` (index 1), `RateLimit` from
-- `RATE` (index 0)
#guard (docsLayer.bind fun l => (build deploySem l Context.empty).map fun c =>
    (c.getV dbServiceKey, c.getV rateLimitKey)) =
  some (some (.nat 1), some (.nat 0))

/-! ### The machine agrees on the finite probes

`Effect.scoped(Layer.build(l))` through the proved rc.112 machine: the produced context has
the keys the specification predicts, in the same order, plus `CurrentMemoMap` (key `3`,
`Layer.ts:762`) at the end, and each service's value is its binding's index. -/

#guard (docsLayer.bind fun l => buildSucceeds deploySig l) = some true
#guard (docsLayer.bind fun l => buildServices deploySig l) =
  some [(4, 0), (5, 1), (6, 2), (7, 3), (8, 1), (9, 0), (3, 0)]

-- `Effect.provide(Effect.service(Db), deployment)` answers `DB`'s value, as the
-- specification says the service was built from it
#guard (docsLayer.bind fun l => provideThenService deploySig l dbServiceKey) =
  some (Exit.success (.nat 1))
#guard (docsLayer.bind fun l => provideThenService deploySig l rateLimitKey) =
  some (Exit.success (.nat 0))

/-! ### The two measurements the header's rulings rest on

A probe alphabet over free keys: `fS i` builds service `i+10` from binding `i`, `fB i` is
binding `i` with value `i`. -/

def fS (i : Nat) : LayerTerm DeployOp := bindingServiceLeaf ⟨⟨i⟩, ⟨i⟩⟩ ⟨⟨i + 10⟩, ⟨i + 10⟩⟩
def fB (i : Nat) : LayerTerm DeployOp := bindingLeaf ⟨⟨i⟩, ⟨i⟩⟩ i

-- **Why the shift is four.** A binding at `maxOpsKey` whose value is `0` starves the
-- scheduler once `provideMerge` installs it; the same key with a large value is fine, and so
-- is a free key with value `0`. Two of the three are the same layer shape.
#guard buildSucceeds deploySig
    (LayerTerm.provideMerge (fS 1) (bindingLeaf Effect4.Machine.Env.maxOpsKey 0)) = some false
#guard buildSucceeds deploySig
    (LayerTerm.provideMerge (fS 1) (bindingLeaf Effect4.Machine.Env.maxOpsKey 5000)) = some true
#guard buildSucceeds deploySig (LayerTerm.provideMerge (fS 4) (fB 4)) = some true

-- **Why the fold is not seeded with `Layer.empty`.** The seeded and unseeded folds have the
-- same rows, and the seeded one does not finish inside `runOver`'s fixed 512-step budget.
#guard (layerTy deploySig (LayerTerm.mergeAll emptyLayer [fS 4, fS 5])).map LayerTy.out =
  (layerTy deploySig (mergeLeaves [fS 4, fS 5])).map LayerTy.out
#guard (layerTy deploySig (LayerTerm.mergeAll emptyLayer [fS 4, fS 5])).map LayerTy.requires =
  (layerTy deploySig (mergeLeaves [fS 4, fS 5])).map LayerTy.requires
#guard buildSucceeds deploySig (LayerTerm.provideMerge
    (LayerTerm.mergeAll emptyLayer [fS 4, fS 5])
    (LayerTerm.mergeAll emptyLayer [fB 4, fB 5])) = some false
#guard buildSucceeds deploySig
    (LayerTerm.provideMerge (mergeLeaves [fS 4, fS 5]) (mergeLeaves [fB 4, fB 5])) = some true

-- the empty deployment is `Layer.empty`, and it builds
#guard mergeLeaves [] = emptyLayer
#guard buildSucceeds deploySig emptyLayer = some true
#guard buildServices deploySig emptyLayer = some [(3, 0)]

/-! ### Refusals are data -/

/-- The typo of `Deployment.check`'s `providerUnknown` clause. -/
private def docsTypo : Surface.Deployment := { Surface.docsDeployment with provides := [("Db", "DBB")] }

-- the surface refuses it by a constructor
#guard Surface.Deployment.check docsTypo == .error (.providerUnknown "docs" "Db" "DBB")
-- and the lowering refuses it too, because the table does not know `DBB`
#guard deploymentLayer docsNames docsTypo = none
-- with `DBB` in the table it lowers, and the type carries the unmet requirement
#guard ((deploymentLayer (docsNames ++ ["DBB"]) docsTypo).bind fun l =>
    (layerTy deploySig l).map LayerTy.requires) =
  some (Requirement.ofList [⟨⟨10⟩, ⟨10⟩⟩])
#guard ((deploymentLayer (docsNames ++ ["DBB"]) docsTypo).bind fun l =>
    (layerTy deploySig l).map (fun t => keyNames t.requires)) = some [10]

/-! ### The string law is stricter than the row law by exactly the bindings

A mounted api that requires the *binding* name `DB` has no `provides` row, so
`Deployment.satisfies` refuses it — yet `DB`'s key is in the layer's output row, because
`Layer.provideMerge` keeps the bindings visible. In the worker `env.DB` is a service of the
fiber's context, so the row law is the faithful one; see the header. -/

/-- The requirement table that asks for a binding by name. -/
def bindingAsRequirement : List (String × List String) :=
  [("DocsApi", ["Db", "RateLimit", "DB"])]

#guard Surface.Deployment.satisfies Surface.docsDeployment bindingAsRequirement ==
  .error (.requirementUnprovided "docs" "DB")
#guard (docsLayer.bind fun l =>
    (layerTy deploySig l).map (fun t => decide (dbBindingKey ∈ t.out))) = some true
-- and the string law does hold of the table the plan's §13.3 actually gives
#guard Surface.Deployment.satisfies Surface.docsDeployment Surface.docsRequirements == .ok ()

end Witnesses

/-! ## Separation gate: everything here is first-order data -/

example : DecidableEq DeployOp := inferInstance
example : DecidableEq (LayerTerm DeployOp) := inferInstance

end Effect4.Program.Provision.Deploy
