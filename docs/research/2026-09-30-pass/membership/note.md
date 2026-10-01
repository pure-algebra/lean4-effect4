`typedState_load` (M5) is false as stated: the kernel refutes it for the checked one-line program `Ref.make(5)`, because `StrongValue` wants heap-length liveness that `storePost` never provides (`Gaps.lean` `typedState_load_false`), and the lift seat's capstone derivation assumes it; the proposed `Fits` removes that obstruction (`Walk.lean` `refProg_typedF`), and the whole slice-5 walk re-proves against `Fits` by replacing 58 of 882 copied lines with 20.

# Seat MEMBERSHIP: one membership judgment over the actual value encoding

Base `be15b062`, branch `refactor/phase1-phase3`. Research probes only. Nothing outside
`docs/research/2026-09-30-pass/membership/` was written. No git, make, lake build or generator
was run.

## 1. In short

- `Fits w v ty` is one recursion over the value shapes `Val.hasTy` reads. Each handle is checked
  against the world's declaration tables at the place where it sits. So a union takes one branch
  for both the shape and the handles, and products, Results, exits and snapshots check their
  contents. It is a fold (`fold_of` accepts it) and covers all 20 `Ty` constructors.
- Proved: `Fits` implies the shape check. The converse is false. `Fits` implies declared
  liveness, which equals `HandlesLive` under `WorldValid`. `Fits` is closed under `Ty.sub`. It
  is monotone under the host order, and exits come along for free, because an exit is a value.
- Ten controls separate the two judgments (G1–G10 below). G1–G6 are values the old judgment
  accepts and `Fits` refuses. G7 is a subsumption failure of the old judgment. G8 and G10 show
  that store-length liveness breaks `TypedProg` for a program that returns a fresh Ref, and that
  this makes the declared M5 obligation false. G9 is the pair program, which needs `Fits` to
  carry a fiber's declaration through `fst`.
- Migration, measured: 150 declarations name the strong judgments (90 in `src`, 60 in tests). I
  restated the 90 from `src` over `Fits`. Everything checks, including the stack walk, the hooks,
  saving, delivery, the typed state, the capture lookup and all seven obligation namespaces. Only
  8 declarations needed proof edits; the rest were renames. Three test consumers were re-proved:
  one got shorter, two kept their length.
- Four owner decisions (§7). My recommendation for each: invariance as `Ty.sub` reads it,
  native handle spellings read as declarations, liveness read from the tables, and `unknown`
  kept at the three table kinds for now.

## 2. The proposed definition (exact)

The probe has an `inv` parameter so that both invariance readings can be measured
(`Fits.lean:102`, `FitsInv`). The proposal fixes `inv := Equiv`. Written for `src`
(namespace `Effect4.Program.Typed`, beside `StrongValue`), it is `Fits.lean:36-177` with `Equiv`
substituted:

```lean
/-- Invariance as `Ty.sub` reads it (`Program/Ty.lean:452-454`): subtyping both ways. -/
def Equiv (declared t : Ty) : Prop := declared.sub t = true ∧ t.sub declared = true

def RefDeclared (w : World) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ Equiv t' t
def PromiseDeclared (w : World) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ Equiv a' a ∧ Equiv e' e
def FiberDeclared (w : World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ fty.answer.sub a = true ∧ fty.error.sub e = true

/-- Declared liveness: every cell, deferred and fiber handle the value names is in the tables. -/
def Live (w : World) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => (w.Ρ key).isSome = true
  | .promise key => (w.«Π» key).isSome = true
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- `Val.hasTy`'s `.handle` arm, with the native cell and deferred spellings read as declarations. -/
def HandleFits (w : World) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

/-- Membership at a service's static type (decision row 90): the table's types are flat. -/
def FlatFits (w : World) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target => match v with | .handle kind index => HandleFits w kind index target | _ => False
  | _ => False

def ServicesFit (w : World) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → nativeServiceTy key = some sty → FlatFits w sv sty

def CauseFits (member : Val → Prop) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ member v
  | .die _ _ | .interrupt _ _ => True

def Fits (w : World) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w kind index target
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .option a => match v with | .none => True | .some x => Fits w x a | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, Fits w (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, Fits w x a
    | _ => False
  | .prod a b => match v with | .list [x, y] => Fits w x a ∧ Fits w y b | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => Fits w err e
    | .ctor 1 [val] => Fits w val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Fits w x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => Fits w x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => Fits w x e) c
    | none => False
  | .fiberOf a e => match v with | Value.fiber index => FiberDeclared w ⟨index⟩ a e | _ => False
  | .union l r => Fits w v l ∨ Fits w v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t => match v with | Value.cell index => RefDeclared w ⟨index⟩ t | _ => False
  | .deferredOf a e =>
    match v with | Value.promise index => PromiseDeclared w ⟨index⟩ a e | _ => False
  | .var _ => False
  | .unknown => Live w v

/-- An exit is a value of `Exit<A, E>` (`reifyExitVal`, `Machine/Stores.lean:1637`). -/
def FitsExit (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  Fits w (reifyExitVal ex) (.exitOf ty.answer ty.error)

abbrev FitsCause (w : World) (errTy : Ty) (c : CauseV) : Prop := CauseFits (fun x => Fits w x errTy) c
```

It replaces `StrongValue w ty v` with `Fits w v ty`, `StrongExit` with `FitsExit`,
`StrongCause` with `FitsCause`, and `ServicesOk` with `ServicesFit`. `ValueOk` (the shape check)
stays. It is still what the runtime checks, and `Fits` implies it.

Per constructor (the contract's §4 matrix), with the old judgment's difference:

| `Ty` | `Fits` | Old `StrongValue` |
| --- | --- | --- |
| `never`, `int`, `var` | no value | same |
| `unit`, `nat`, `string`, `bool`, `lit` | the scalar shape (`lit`: that exact string) | same |
| `handle t` | cell: `t` is `Ref.Ref<number>` and the cell is declared ≡ `nat`; deferred: `t` is `Deferred<number, number>` and it is declared ≡ `(nat, nat)`; scope; external: `t` is external and `allocated[i] = t`; otherwise a context whose services fit their static types and whose handles are declared | cell and deferred by kind only (G6) |
| `option a` | `none`, or `some x` with `x` fitting | same recursion |
| `list a` | every element of the one decoded view `Val.asList?` fits, ordinary lists and snapshots alike (`fits_list_iff`, `Fits.lean:1152`) | snapshot skipped (G5) |
| `prod a b` | the two-cell list, both columns | skipped (G1) |
| `except e a` | the chosen arm | skipped (G2) |
| `exitOf a e` | success: the value fits; failure: the cause decodes and its typed failures fit `e` | success skipped (G3) |
| `causeOf e` | decodes; typed failures fit `e` | same (causes carry no handle) |
| `fiberOf a e` | the fiber is declared below `(a, e)` (covariant) | same |
| `union l r` | one branch, shape and handles together | branches split (G4) |
| `refOf t` / `deferredOf a e` | declared at a type equivalent under `Ty.sub` | exact spelling (G7) |
| `unknown` | declared liveness | heap-length liveness (G8, G10) |

## 3. Findings, with evidence

Every theorem named below is kernel-checked at `[propext, Quot.sound]` or less (§9 gives the
axiom lines). World constructions are small explicit records in `Gaps.lean:217-251`.

**F1. The valid direction, and the converse fails.** `fits_hasTy` (`Fits.lean:247`): for every
reading `inv`, every `ty` and `v`, `FitsInv w inv v ty → Val.hasTy v ty w.state.externals.allocated`.
Converse refuted: `converse_false` (`Gaps.lean:287`). The value is fiber 1 at
`fiberOf nat never`, in a world that declares fiber 1 at `string`.

**F2. The six value gaps (proved).** For each one there are three theorems: `gN_old`, where
`StrongValue` accepts; `gN_refused`, where `Fits` refuses in the same world; and `gN_control`,
where `Fits` accepts once the declaration fits (`Gaps.lean:299-362`).
- G1: a product (a two-cell list, while `HandlesFit` looks for `.pair`).
- G2: a Result's success arm.
- G3: a successful exit.
- G4: a union whose shape evidence and handle evidence come from different branches.
- G5: a fiber snapshot.
- G6 (new): the native cell spelling `Ref.Ref<number>` on a cell declared `bool`. `HandlesFit`'s
  `.handle` arm types contexts only (`Typed/Admission.lean:57`). So under the old judgment, M6
  could not type a native `Ref.get` through a variable: nothing links the handle to a `nat`
  declaration.

**F3. Equality invariance breaks subsumption (proved).** `refOf nat` and `refOf (union nat nat)`
are subtypes of each other (`sub_ref_equiv`, `Gaps.lean:377`).
- `strongValue_not_closed_under_sub` (`:399`) and `fitsEq_not_closed_under_sub` (`:403`): the
  equality reading loses the value when the type is re-spelled.
- `fits_sub` (`Fits.lean:870`): `Fits` is closed under `Ty.sub`. The proof follows `Ty.sub`'s own
  arms (`fun_induction`), as `cata_admits_sub` does.
- M6 will need subsumption wherever the laws use `hasTy_sub` today: eleven call sites in
  `Laws/Program/{Typed,Template,TypeAlgebra,LoopSound,MeaningSound}.lean` and
  `Laws/Schema/Codec.lean`.
- So `Fits` and `StrongValue` are incomparable. `natCell_equiv_spelling` (`:413`) gives the
  direction that `Fits` accepts and `StrongValue` refuses; G1–G6 give the other direction.

**F4. Liveness read from the store breaks `TypedProg` for fresh Refs (proved).**
- `TypedProg` types each continuation at every later world the post admits
  (`Typed/Residual.lean:189-192`). `storePost (.refMake _)` names the new key's declaration
  (`:58`). `HandlesLive` asks for the heap length (`Typed/Admission.lean:23`). A world that
  declares cell 0 without growing the heap is later than the initial world
  (`w0_order`, `Gaps.lean:433`).
- G8, generic cell: `refReturn_untypable` (`:440`). No `TypedProg` types
  `Ref.make(true)`-then-return at the initial world. `refReturn_fits` (`:452`) shows the same
  continuation fits under `Fits` at every such world.
- G10, a real program: `refProg := .perform .refMake (.lit (.nat 5))` checks at
  `Ref.Ref<number>` (`refProg_checks`, `decide +kernel`, `:515`). Its loaded code is the store
  step followed by the answer (`loaded_root`, by `rfl`, `:519`).
- `refProg_untypable` (`:524`): no typed derivation at any world with an empty heap and cell 0
  undeclared. `WorldValid` forces both of these for the loaded machine.
- `typedState_load_false` (`:547`): the instance of `M3bAssembly.typedState_load`
  (`Typed/Assembly.lean:148-150`) at this program, fuel 20, is false.
- `refProg_typedF` (`Walk.lean:1246`): under `Fits` the same loaded code is typed at every world.
- The lift seat derives the repaired capstone from `typedState_load`
  (`2026-09-30-pass/lift/note.md:1`, `Lift.lean:985-1032`). That derivation is correct as an
  implication, but its premise fails for Ref programs under today's `StrongValue`.

**F5 (G9). The pair program needs the amendment (proved; finite checks).**
- Finite checks (`#guard`, `Gaps.lean:478-480`): `pairProgram` checks at `nat`, runs to 7, and
  its pair has static type `prod (fiberOf nat never) unit`.
- `pair_builds` and `fst_projects` (`:482-486`, by `rfl`): the pair atom builds the two-cell list
  and `fst` returns the handle.
- `strongValue_no_fst` (`:488`): the old judgment holds of the pair where fiber 1 is declared
  `string`, yet fails for its first component. So no `fst` step can carry the declaration.
- Under `Fits`: `fits_pair`, `fits_fst` and `await_fits` (`Fits.lean:1110-1139`) are exactly the
  three steps M6 needs to type this program.

**F6. Monotonicity (the law exists and is declared).**
- `M3bWorld.strongValue_mono` and `M3bWorld.strongExit_mono` (`Typed/Residual.lean:424-428`) are
  `#proof_wanted` (`:456-457`, ceiling 3). Their docstring says slice 5's stack and delivery need
  them.
- No landed proof uses them: the inventory's walk set does not contain them, and the landed walk
  works at one world. M6's `StepPreserves` (`∃ w', w.leHost w' ∧ …`) will need them.
- For `Fits`: `fits_mono` (`Fits.lean:851`). It is one instance of the transport lemma
  `fitsInv_map` (`:749`), which also gives `fitsEq_fits`. `fitsExit_mono` (`:1088`) is `fits_mono`
  at the exit type.
- For the old judgment: both obligations are true, proved in `OldMono.lean:95-113`. So they were
  unproved, not false.

**F7. The connection to the old judgment.**
- Under `WorldValid`, the equality reading implies all three conjuncts of `StrongValue`
  (`fitsEq_strongValue`, `Fits.lean:1073`).
- The `Ty.sub` reading implies the shape check (`fits_hasTy`) and liveness
  (`fits_live`, `:501`; `live_iff_handlesLive`, `:630`).
- `Fits` and `FitsEq` are the same recursion; they differ only at invariant handles. So, as a
  reading (not a theorem), under `WorldValid` `Fits` implies `StrongValue` except where a cell or
  deferred is declared at an equivalent but different spelling (F3).

## 4. The migration, measured

**Restated and checked (`Walk.lean`).** `walk_baseline.py` copies 18 exact line ranges of
`Typed/Admission.lean`, `Typed/Residual.lean`, `Typed/Stack.lean` and `Typed/Assembly.lean`, and
renames only. Together these ranges hold every declaration of the four modules in the migration
set, including the seven obligation namespaces. That gives 882 non-blank lines. `Walk.lean` is that
copy, edited until it checks over `Fits`.

- `diff -B` (`walk.diff`): 58 lines replaced by 20, in 8 declarations. They are the four exit
  laws (`strongExit_success`, `strongExit_of_clean`, `cleanExit_of_never`,
  `strongExit_failure_of_error`), `strongValue_bool_true`, `strongExit_bool`, `settling_fork`
  (13 lines of key bookkeeping become 1), and `popR_typed` (two uses of `hex.2.1 v rfl` become
  `hex`).
- Unchanged apart from renaming:
  - `TypedProg`, its inversions, `Ψ_S`, `Ψ_F` and the hook protocols;
  - `HookLaws`, `hookLaws_interpR`, `popR_typed_interpR`, `saveAnswerR_typed`, `deliver_active`;
  - `preds`, `TypedState`, `AnswerOk`, `QueueOk`, `StepPreserves`, `envTyped_append`,
    `capture_lookup`;
  - all obligation statements.

**Consumers re-proved (`Walk.lean:1183-1251`).**
- `fork_admitted`: 11 lines of key bookkeeping become 1.
- `lookup_typed`: same length. It reads the service through `flatFits_fitsInv`.
- `service_admitted`: same length. It reads through `fits_context_services`.
- `refProg_typedF`: new, 5 lines.
- Proof search with the `Effect4.TypedState` bank (`Fits.lean:1207-1232`) closes four goals the
  migration produces:
  - the heap-extension goal behind `refProg_untypable`. It needs the bank: its red control makes
    no progress without it.
  - fiber-declaration transport.
  - `fits_mono` from its statement, given `fitsInv_map` as a rule.
  - the value half of `settling_fork`.

**Inventory (`Inventory.lean`, a reading of the kernel environment of `Test.All`;
`inventory.log`).**
- Direct mentions:
  - `StrongValue` 39 declarations;
  - `HandlesFit` 16;
  - `ValueOk` 38;
  - `StrongExit` 56;
  - `StrongCause` 21;
  - the helpers `HandlesLive` 16 and `ServicesOk` 5.
  Names are listed by module in `inventory.log` §1.
- Textual occurrences of the five names, by file (174 in all):
  - `Typed/Residual.lean` 40, `Typed/Stack.lean` 28, `Typed/Admission.lean` 23,
    `Typed/World.lean` 15, `Typed/Validity.lean` 8, `Typed/Assembly.lean` 8,
    `Typed/ForkSource.lean` 1 (a comment);
  - `AsyncHookContract` 13, `TypedResidual` 10, `TypedWorldValidity` 10, `StrongExitDefect` 7
    (a local binder name only), `TypedControl` 4, `TypedStack` 2, `InterruptDelivery` 2
    (comments), `Test/Audit/TypedStateDecl` 2 (an unrelated string), `LoadedAdmission` 1.

| Migration set (names or reaches the strong judgments) | src | tests |
| --- | --- | --- |
| to redefine (defs, inductives) | 30 | 7 |
| to restate (theorem statements) | 60 | 53 |
| per module | Admission 12, Assembly 31, Residual 30, Stack 17 | AsyncHookContract 18, TypedControl 11, TypedResidual 10, LoadedAdmission 9, TrivialPosts 6, TypedStack 5, AdmissionCensus 1 |

- The inventory does not separate a renamed theorem from one whose proof changes. `Walk.lean`
  does: only 8 of the 90 `src` declarations changed their proofs.
- Of the 60 test declarations, about 20 build or project the old conjuncts. That is a reading of
  the direct mentions (`inventory.log` §1); only three of them were re-proved here.
- 129 declarations reach only `ValueOk`: `World` 49, `Validity` 48, `TypedWorldValidity` 18,
  and 14 others. They are unchanged.
- Walk set: the slice-5 walk and delivery theorems depend on 36 declarations of the migration set
  (`inventory.log`, last line of §2). Their value parts are `StrongValue`, `StrongExit`,
  `StrongCause`, `HandlesFit`, `HandlesLive`, `ServicesOk`, `EnvTyped`, `PointTyped` and
  `BodyTyped`. The lemmas the walk applies to them are `strongExit_of_clean`,
  `strongExit_failure_of_error`, `TypedProg.pure_inv`, `unguard_payload_inv` and `walk_saved`,
  plus the success projection `hex.2.1`. Those are exactly the places `walk.diff` touches in
  `popR_typed` and the exit laws.

**Estimate.**
- (1) Land the new module beside the old one: definitions, the `fold_of` line and the laws. That
  is `Fits.lean` minus the `FitsEq` parts and the search examples, about 1,000 lines as written in
  the probe. It could shrink if the laws are stated as algebra conditions over `Fits.alg`, as
  `Laws/Program/Admits.lean` does for `hasTy`.
- (2) Cut over the four modules. This is measured above: renames plus 8 proof edits. It turns
  `M3bWorld` from ceiling 3 into ceiling 1 (`typedProg_mono` stays open).
- (3) Cut over 60 test declarations, about 20 of them with small proof edits.
- (4) Retire the six old definitions.
- Steps 1–3 are two or three slices. Step 2 is mechanical.

## 5. What is proved, what is finite, what is a reading

- **Proved** (kernel), `Fits.lean`: `fits_hasTy`, `fits_live`, `live_iff_handlesLive`,
  `fitsInv_map`, `fits_mono`, `fitsEq_fits`, `fits_sub`, `fitsEq_handlesFit`,
  `fitsEq_strongValue`, `fitsExit_mono`, `fitsExit_sub`, `fits_pair`, `fits_fst`, `await_fits`,
  `fits_list_iff`, and the four `search_*`.
- **Proved**, `Gaps.lean`: `converse_false`, G1–G6 (18 theorems), `strongValue_not_closed_under_sub`,
  `fitsEq_not_closed_under_sub`, `natCell_equiv_spelling`, `refReturn_untypable`,
  `refReturn_fits`, `strongValue_no_fst`, `refProg_checks`, `refProg_untypable`,
  `typedState_load_false`.
- **Proved**, `Walk.lean`: 21 theorems with an axiom line (every other declaration in the file
  checks too). These include `popR_typedF`, `hookLaws_interpRF`,
  `popR_typed_interpRF`, `saveAnswerR_typedF`, `deliver_activeF`, `capture_lookupF`,
  `service_admittedF` and `refProg_typedF`.
- **Proved**, `OldMono.lean`: the old `strongValue_mono` and `strongExit_mono`.
- **Finite checks:** the three `#guard`s of G9 (`Gaps.lean:478-480`).
- **Readings:**
  - the inventory counts;
  - the walk set;
  - "about 20 test declarations change proofs";
  - the size estimate;
  - the claim that no landed proof uses the `M3bWorld` obligations, which comes from the walk set.

## 6. Proposals

1. **Land `Fits` beside `StrongValue`** as in §2, in a new `Laws/Program/Typed/Membership.lean`
   imported by `Admission.lean`. Add `fold_of Effect4.Program.Typed.Fits` to
   `Laws/Program/Folds/Ty.lean`. The probe's `fold_of` run gives
   `FitsInv.eq_cata : FitsInv w inv v a = (cata_ty (FitsInv.alg w inv) a).snd v`, a paramorphism
   with carrier `Ty × (Val → Prop)`.
2. **Carry the laws with it**, with these signatures (as proved in the probe, `inv` fixed):

```lean
theorem fits_hasTy (w : World) : ∀ ty v, Fits w v ty → Val.hasTy v ty w.state.externals.allocated = true
theorem fits_live (w : World) : ∀ ty v, Fits w v ty → Live w v
theorem live_iff_handlesLive (valid : WorldValid rootTy w m) (v : Val) : Live w v ↔ HandlesLive w v
theorem fits_sub (w : World) {a b : Ty} (hsub : Ty.sub a b = true) : ∀ v, Fits w v a → Fits w v b
theorem fits_mono (ordered : w.leHost w') (h : Fits w v ty) : Fits w' v ty
theorem fitsExit_mono (ordered : w.leHost w') (h : FitsExit w ty ex) : FitsExit w' ty ex
theorem fitsExit_success_iff : FitsExit w ty (.success v) ↔ Fits w v ty.answer
theorem fitsExit_failure_iff : FitsExit w ty (.failure c) ↔ FitsCause w ty.error c
theorem fitsExit_of_clean (h : cleanExit (.failure c) = true) : FitsExit w ty (.failure c)
theorem fitsExit_failure_of_error (herr : tin.error = tout.error)
    (h : FitsExit w tin (.failure c)) : FitsExit w tout (.failure c)
theorem fits_fst (h : Fits w v (.prod a b)) (hr : NativeAtom.eval .fst [v] = some r) : Fits w r a
theorem await_fits (h : Fits w (Val.fiber id) (.fiberOf a e)) (ordered : w.leHost w')
    (declared : w'.Γ id = some ty) (hex : FitsExit w' ty ex) (req) : FitsExit w' ⟨a, e, req⟩ ex
```

3. **Cut over by renaming**, following `Walk.lean`. Close `M3bWorld.strongValue_mono` and
   `strongExit_mono` with `fits_mono` and `fitsExit_mono`.
4. **Register the counterexamples** when the declarations change. My proposed ids: the next free
   `E4-TYPED-CE` numbers for G1–G6 as one packet, G7 (subsumption), and G8/G10 (`typedState_load`
   at `Ref.make(5)`). The ids themselves are for the coordinator to assign.
5. **Re-check the M5/M6 plan.** The lift seat's capstone stands on `typedState_load`, and today
   that premise is false for a program that returns a fresh Ref (proved for `Ref.make(5)`). The
   same argument applies to a fresh Deferred through `deferredMake`'s post (a reading, not
   proved). The repair is decision D3 below.

## 7. Decisions for the owner (with my recommendation)

- **D1. Invariance reading at `refOf`/`deferredOf`.**
  - Option `Equiv` (subtyping both ways): matches `Ty.sub`'s arms, keeps subsumption.
    Recommended.
  - Option equality: `HandlesFit`'s reading, and the contract's words "exact invariant declared
    type". It loses subsumption on re-spelled types (F3), unless every world and checker type is
    kept in normal form. On normal forms the two agree (`sub_antisymm_normal`,
    `Laws/Program/TypeAlgebra.lean:618`).
- **D2. Native handle spellings.**
  - Recommended: read `Ref.Ref<number>` as a cell declared ≡ `nat`, and
    `Deferred<number, number>` as a deferred declared ≡ `(nat, nat)`. Without this, M6 cannot
    type a native Ref or Deferred operation reached through a variable (G6).
  - When generic cells land (decisions 42–43), the spellings may become plain aliases of
    `refOf nat` and `deferredOf nat nat`.
- **D3. Where liveness is read.**
  - Recommended: from the tables (`Live`). It equals `HandlesLive` under `WorldValid`, and it
    makes fresh Refs typable (F4).
  - The alternative keeps store liveness and adds `key.index < w'.state.refs.length`
    (respectively the deferred length) to the `refMake`, `deferredMake` and `memoBuild` posts.
    That should also repair G10 (a reading; not probed), but it keeps the judgment tied to store
    layout.
- **D4. `unknown`.** `Live` checks cells, deferreds and fibers, as `HandlesLive` does. Should
  external, scope and memo-map handles also have to exist (`Handle.existsIn`), and should
  unregistered kind bytes be refused? The contract asks for this at the external boundary (§3).
  Recommended: leave the internal judgment as it is now, and refuse at the boundary.

## 8. Open questions

- `M3bWorld.typedProg_mono` is not attempted. It now needs only the transport of the
  preconditions (`EnvTyped`, `PointTyped`, `BodyTyped`, `ServicesFit`), which follows from
  `fits_mono`, plus an induction on `TypedProg`.
- Does `typedState_load` hold under `Fits`? Not proved. Only the G10 obstruction is shown gone.
- In `ServicesFit`, services under keys with no static type are only required to be declared-live
  (through the context clause's `Live`). Should decision row 90 refuse them?
- The runtime check stays `Val.hasTy`, and deciding `Fits` for a host reply needs the registry's
  declarations (path B). `Fits` is a `Prop`; a Boolean checker with a reflection lemma belongs to
  the registry slice.
- `Fits` at `nat` means exact naturals. The OCaml target's intermediate bounds are the numbers
  seat's concern, not this one's.

## 9. Commands run and results

All Lean runs used the lock, from the repository root:
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <file>`.

| File | Exit | Time | Axiom lines | Outside `[propext, Quot.sound]` |
| --- | --- | --- | --- | --- |
| `Fits.lean` | 0 | 6 s | 20 | none (`search_heap_extends`: no axioms) |
| `Gaps.lean` | 0 | 4 s | 32 | none (`pair_builds`, `fst_projects`: `[propext]`) |
| `Walk.lean` | 0 | 3 s | 21 | none |
| `OldMono.lean` | 0 | 3 s | 2 | none |
| `Inventory.lean` | 0 | 26 s | 0 (a report, no theorems) | n/a |

The logs are `fits.log`, `gaps.log`, `walk.log`, `oldmono.log` and `inventory.log` in this folder.

- `python3 walk_baseline.py <repo root> > baseline.lean`, then
  `diff -B baseline.lean <restated section of Walk.lean>`: diff exit 1 (differences found),
  58 lines removed, 20 added, 11 hunks. Saved as `walk.diff`.
- `python3 prelude_check.py check Fits.lean Gaps.lean Walk.lean`: exit 0. The three shared
  blocks are identical (sha256 prefix `c6f205c95f7f9cf7`).
- Scratch runs of the aesop goals and the loaded-code checks were done in the session scratchpad
  and are not evidence. Their results are in `Fits.lean`'s `search_*` and `Gaps.lean`'s
  `loaded_root`.
