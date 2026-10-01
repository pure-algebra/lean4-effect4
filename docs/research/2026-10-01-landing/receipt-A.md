# Seat A receipt: values in the checker's order, the signature as data, inhabitance at admission

Written 2026-10-01 by seat A (Opus) in `/Users/pooks/Dev/lean4-effect4-seat-A`, branch `seat/A`.
Brief: `docs/research/2026-10-01-landing/brief-A.md` with its amendments, and the coordinator's
messages (the tracked port for step 1; rows 137 and 149; the inventory first; the positive control
through `typedStateF_load`; the merge instruction and its later withdrawal).

## The one thing first

This branch is **not merged** with `refactor/phase1-phase3`. The permission system denied
`git merge refactor/phase1-phase3` in this worktree, and, as the coordinator's later message asks,
no other route was tried. The branch is green on its own base (`lake build Effect4.Laws Test.All`,
713 jobs, exit 0, the axiom gate included), but it will **not** build merged as it stands, by
reading of seat B's files at `af3799f9`: `completionOk_of_fitsExit` is declared twice (this
branch's `Membership.lean:1340` and seat B's `Typed/Adequacy.lean:247`, same namespace; keep this
branch's, which is B's at any requirement, and delete B's), and ten token sites in B's files
need the checker's order and the world order's new conjunct (listed exactly under "Integration":
three `fits_sub` → `fits_subN` in `Adequacy.lean`, `rfl` appended to five order constructions,
`Residual.lean:56` to `subN`, and `Residual.lean:633`'s `servicesFit_map` call gains its
lookup premise). Also before merging: runner admission (`admitProgram`) still admits
E4-TYPED-CE-015's empty columns. The column check is landed, located and proved, but its refusal
`AdmitRefusal.emptyColumn` is an input of the generated runner group and the brief runs no
generator, so that wiring is held at the boundary with its exact hunk (decision D-A1 below).

## Base, head, commits

Base `bb269fde`. Head: the commit that adds this file; its parent `7ac4d4fc` is the last code
commit. Commits, in order (each built before it was made; step 1 committed red by design):

| Commit | What |
| --- | --- |
| `2a6886bf` | Step 1: `FitsOrder` battery, E4-TYPED-CE-009 on the tree |
| `bbed898d` | Step 2: row 137 (a), `Fits` in the checker's order |
| `26c00954` | Step 3: M5's first positive control |
| `55fe8043` | Row 137 at `World.lean:81` (`CompletionOk.ofRefGet` in `subN`) |
| `ea77af5f` | The positive control through `ValueMembership.typedStateF_load` |
| `372a5092` | Step 4: TY-07 term soundness, TY-08 |
| `f920d4e8` | Step 5.1: shape A, the inventory measured |
| `d905ea53` | Step 5.2: Σ_app as data and its extension |
| `3e2f3fe8` | Step 5.3: C3's reflection by one generic fold congruence |
| `ed7fad06` | Step 5.4: lawful signatures on the source |
| `61e47b08` | Step 5.5: row 116's positive control |
| `31596c4e` | Step 6.1: TY-05, the invented key deleted |
| `de926765` | Step 6.2: inhabitance agrees with membership; the column check located |
| `816b901b` | Step 7: TY-15's comment |
| `7ac4d4fc` | `fits_nat_irrel` (seat B's item 4) |

## Every changed path (`git diff --stat bb269fde 7ac4d4fc`: 22 files, +4720 −80)

Mine by the brief: `src/Effect4/Laws/Program/Typed/Membership.lean`,
`src/Effect4/Laws/Program/TypeAlgebra.lean`, `src/Effect4/Laws/Program/Typed/World.lean`
(the `serviceTy` field, its order lemmas, `:81`), `src/Effect4/Program/Admission.lean`,
`src/Effect4/Laws/Program/Signature.lean` (new), `src/Effect4/Laws/Program/Template.lean` (the
comment), and the batteries `Test/Counterexamples/Machine/Semantics/FitsOrder.lean`,
`Test/Program/TermFits.lean`, `Test/Program/SignatureControls.lean`,
`Test/Program/TypedProgRows.lean`, `Test/Program/AdmissionColumns.lean` (all new).

Mine by implication: `src/Effect4/Laws/Program/Typed/Admission.lean` (`ProgramSource` and
`EnvTyped` live there: the lawfulness field, `evalTerm_fits`, and `π` moved there for the import
order). `Typed.lean` was not changed (TY-07's law cannot live there; step 4).

Roots, at their anchors: `src/Effect4/Laws.lean` (one import after `Typed.Assembly`),
`Test/All.lean` (five imports after `ValueMembership`).

Dependents repaired, outside the named list: `src/Effect4/Laws/Program/CheckedTyping.lean`
(`admitProgram_eq_ok`) and `src/Effect4/Laws/Run.lean` (`admitProgram_certificate`), both because
step 6.1 restructures `admitProgram`; `Test/Audit/TypedStateDecl.lean`,
`Test/Counterexamples/Machine/Semantics/M6Capstone.lean` (one projection each),
`Test/Counterexamples/Machine/Semantics/TrivialPosts.lean`,
`Test/Counterexamples/Machine/Semantics/ValueMembership.lean`,
`Test/Program/LoadedAdmission.lean`, `Test/Program/TypedWorldValidity.lean`.

## Evidence words

**proved**: a kernel theorem compiled in this worktree, axioms printed. **tested**: a `#guard`, a
`#guard_msgs` fixture or a command run here. **reading**: code or notes read, not run.
**assumed**: not checked.

## Step 1: the counterexample re-established (`2a6886bf`)

New battery `Test/Counterexamples/Machine/Semantics/FitsOrder.lean`, imported from
`Test/All.lean` beside `ValueMembership`: the synthesis seat's tracked port
(`ports-at-dceae006/HeadM5Fits.lean`, 13 theorems) plus probe A's three red controls on `Fits`,
restated in the battery's namespace. It proves M5 false against the then-raw judgment (the
brief's "committed red").
Command: `LEAN_NUM_THREADS=4 lake env lean -M6144 -DwarningAsError=true
Test/Counterexamples/Machine/Semantics/FitsOrder.lean` (exit 0), then `lake build` of the module
(381 jobs, exit 0). After step 2 the refutations are historical (below).

## Step 2: row 137 (a), `Fits` in the checker's order (`bbed898d`)

**Statements changed** (`src/Effect4/Laws/Program/Typed/Membership.lean`):

| Declaration | Old (at `bb269fde`) | New |
| --- | --- | --- |
| `Equiv` (`:32`) | `declared.sub t = true ∧ t.sub declared = true` | `Ty.subN declared t = true ∧ Ty.subN t declared = true` |
| `FiberDeclared` (`:44`) | `… fty.answer.sub a = true ∧ fty.error.sub e = true` | `… Ty.subN fty.answer a = true ∧ Ty.subN fty.error e = true` |
| `RefDeclared`, `PromiseDeclared` | read `Equiv` | text unchanged; read the new `Equiv` |
| `fits_sub` (`:857`) | statement unchanged | handle cases by `Ty.subN_trans` and `Ty.sub_le_subN` |
| `await_fits` (`:1261`) | statement unchanged | `fitsExit_subN` |

Unchanged as the brief asks: `HandleFits`, `FlatFits`, `Live`, `CauseFits`, `Fits`'s own arms (its
`fold_of` connector elaborates as before). `ServicesFit` changed later, in step 5.1 (shape A).

**New, all proved** (axioms printed in the batteries, all `[propext, Quot.sound]` except
`causeFits_iff`, none):

- `TypeAlgebra.lean`: `Ty.subN` (def, `:1067`), `subN_refl` (`:1069`), `subN_trans` (`:1071`),
  `sub_le_subN` (`:1076`), `subN_normalize_left` (`:1079`), `subN_normalize_right` (`:1083`),
  `subN_equiv_iff` (`:1088`), `ofRaw_eq_iff` (`:1099`), `subN_join_left` (`:1105`),
  `subN_join_right` (`:1110`). TY-17 (the verifier saw `subN_refl` with no axioms printed): now
  printed, `[propext, Quot.sound]`.
- `Membership.lean`: `exists_mem_singleton_iff` (`:972`), `fits_ofMembers` (`:977`),
  `fits_members` (`:995`), `fits_factors` (`:1030`), `fits_normalizeRow` (`:1037`),
  `fits_prod_iff` (`:1048`), `fits_productMembers` (`:1058`), `causeFits_iff` (`:1073`),
  `fiberDeclared_normalize` (`:1078`), `equiv_normalize` (`:1084`), **`fits_normalize`**
  (`:1089`), **`fits_subN`** (`:1195`), **`fits_join_left`** (`:1200`), **`fits_join_right`**
  (`:1204`), `fitsExit_subN` (`:1229`): the verifier's `verify-AmendedFitsProbe.lean` argument on
  the production judgment.

**Dependents repaired** (all Test): `ValueMembership.lean`'s `g6_refused` (`:759`, a `change` to
the raw form), `natCell_equiv_spelling` (`:820`, `Ty.sub_le_subN`), `getProg_typedF` (`:936`,
`fits_subN`). No Laws dependent broke: `Ty.sub_refl _` elaborates at a `Ty.subN t t = true` goal by
unfolding `subN` (tested on the four shapes `RefDeclared`, `FiberDeclared`, `Equiv`, `subN t t`
in a probe; this is why seat B's and seat C's `Ty.sub_refl` sites need no change). Built: the
reverse import closure of `Membership` (twelve Test modules, 561 jobs) and `TypeAlgebra`'s direct
importers (280 jobs), exit 0.

**The battery restated.** The step-1 refutations are of the old judgment, so they live in
`FitsOrder.Reviewed` over a local copy of the pre-137 `Fits` (its four declaration arms raw):
`Reviewed.not_fits_fiber_normal` (`:212`), `Reviewed.not_fits_cell_raw` (`:226`),
`Reviewed.not_fits_join` (`:236`), `Reviewed.leaf_false` (`:385`), `Reviewed.m5_false`
(`:398`), `Reviewed.typedState_load_false` (`:404`), `Reviewed.capstone_false` (`:440`), the last
three under the hypothesis `RawLeaf` (`:375`; the production leaf implied the raw one before 137).
On the production judgment: `fits_fiber_normal` (`:246`), `fits_cell_raw` (`:250`), `fits_join`
(`:255`) (the three controls flipped), `m5_forces_leaf` (`:314`), `leaf_holds` (`:369`),
`rawLeaf_false` (`:380`, the hypothesis is now false), `rreachable_load` (`:425`),
`capstone_implies_load` (`:430`). Two `#guard_msgs (error)` red controls pin that the old
refutation proofs no longer close (the pinned message is the mismatch
`… .subN T.normalize = true` against `T.sub T.normalize = true`).

## Step 3: M5's first positive control (`26c00954`, `55fe8043`, `ea77af5f`)

In `FitsOrder.lean`, all proved, `[propext, Quot.sound]`: `child_check` (`:480`, the child checks
at `certT` by `check_complete` of the kernel fact), `fiber_subN_root` (`:485`), `prog3_typedF`
(`:491`, the loaded code typed at every world: the guard at `midTy`, the fork by `TypedProg.fiber`
with `BodyTyped.at_`, `unguard` carrying `FiberDeclared` by `Ty.subN_refl`, the run arm's answer
by `fits_mono` then `fits_subN`), **`prog3_loads_typed`** (`:524`:
`∃ w, TypedState src rootTy3 w (loadR prog3 100 100)`, the instance `Reviewed.m5_false`
refuted), `prog3_leaf` (`:528`).

Coordinator corrections applied here: **`CompletionOk.ofRefGet` in `subN`** (`World.lean:81`;
old `∃ ty, w.Ρ cell = some ty ∧ ty.sub types.1 = true`, new `… ∧ Ty.subN ty types.1 = true`;
`ref_completion_inv` (`:197`) and its `WorldWanted` obligation changed the same way; repair:
`TypedWorldValidity.lean`'s `dangling_completion_shape`). **The positive control goes through
`ValueMembership.typedStateF_load`** (`:989`), now stated at every source and budget (its two old
callers pass `20 20`); the battery's own copy of the argument (`typedState_load_of_code`) is
deleted. The build after `55fe8043` was the full default target set (712 jobs, exit 0, the gate
included), because a helper passed no target to `lake build` on its first run.

## Step 4: TY-07 term soundness, TY-08 (`372a5092`)

**Where it lives, and why not where the brief said.** `Laws/Program/Typed.lean` is upstream of
`Fits` (`World.lean` imports it), so it cannot state the law. It is `evalTerm_fitsAll`
(`Membership.lean:2082`; its `Ty` cases are the projection and the template widening, which row
132 puts there) and, in the `EnvTyped` form the synthesis names, **`evalTerm_fits`**
(`Typed/Admission.lean:81`): `EnvTyped w env vals → termTy sig env t = some ty → evalTerm vals t
= some v → Fits w v ty`, under `sig.atomOf = nativeAtomTy` and `sig.constAtom = nativeConstAtom`
(true by `rfl` for every native and source signature; `evalTerm_fits_native` (`:88`) is the
instance).

**Theorems, all proved, `[propext, Quot.sound]` unless noted** (printed in
`Test/Program/TermFits.lean`): `TypeAlgebra.lean`: `Ty.WidensSub` (`:1125`), `.refl`, `.trans`,
`infer_widensSub` (`:1138`, `fun_induction infer`), `matchTemplate_widensSub` (`:1169`),
`matchTemplateArgs_widensSub` (`:1178`), `valueVarsAlg`/`valueVars` (`:1197`, `:1220`, a fold),
`instantiate_of_noVars` (`:1223`, `[propext]`). `Membership.lean`: inversions `fits_unit_inv`
(`:1364`) … `fits_option_inv` (`:1388`); `FitsAll` (`:1420`) and its laws;
`fitsAll_of_pointwise` (`:1508`); `fits_instantiate_widens` (`:1526`); `FitsAll.instantiate`
(`:1642`); `AtomFits` (`:1661`) and `atomFits_of_mono` … `_shape` (`:1665`–`:1725`);
`projectProduct_fits` (`:1780`); `queryTag_bool` (`:1818`) … `queryError_fits` (`:1880`);
**`atomFits`** (`:1897`, all 33 atoms); `fits_lit` (`:2065`); **`evalTerm_fitsAll`**,
**`evalTerms_fitsAll`** (`:2082`, `:2106`). TY-08: `heapTable_of_fits` (`:1333`),
`completionOk_of_fitsExit` (`:1340`). The promise half reads `CompletionStrong` in seat C's
`Assembly.lean` (below).

Battery `Test/Program/TermFits.lean`: `pair_fits` (`:51`), `fst_union_fits` (`:76`), the red
control `widens_needs_valueVars` (`:89`, proved: at `refOf (var 0)` a widening loses the cell, so
`valueVars` is a necessary premise).

## Step 5.1: shape A; the audit's inventory measured (`f920d4e8`)

| Declaration | Old | New |
| --- | --- | --- |
| `Typed.World` (`World.lean:52`) | fields `Γ`, `Π`, `Ρ`, `Θ` | adds `serviceTy : ServiceKey → Option Ty := nativeServiceTy` (`:62`) |
| `World.le` (`:137`) | last conjunct `∀ id, TableExtends (w.Θ id) (newer.Θ id)` | then `∧ newer.serviceTy = w.serviceTy` |
| `ServicesFit` (`Membership.lean:83`) | `… → nativeServiceTy key = some sty → …` | `… → w.serviceTy key = some sty → …` |
| `servicesFit_map` (`:733`), `fits_map` (`:742`) | premises `hPi hRho halloc` (and `hΓ`) | add `hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty` |

New: `le_serviceTy` (`World.lean:417`), `serviceTy_of_le` (`Membership.lean:843`); `order_refl`,
`order_trans`, `park_extension`, `fork_extension`, `refMake_extension`, `promise_extension`
re-proved with `rfl` appended (statements unchanged).

**The inventory, measured by compiling** (the audit's §3, 27 sites): World and order 8 (as
listed); Membership 4 (+1 lemma); initialization **0** (the field's default keeps `initialWorld`
and both `initial_world_valid`); existing tests **5** (`TypedStateDecl.lean:294`,
`ValueMembership.lean`'s order construction, `TypedWorldValidity.lean:33`, `M6Capstone.lean:783`,
`LoadedAdmission.lean:119`); source route in 5.4; the source/world tie is seat C's. Repairs:
`.2.2.2.2.2` → `.2.2.2.2.2.1` at two token projections; `rfl` appended to two order
constructions; `lookup_typed` and `service_admitted` take `hkey : w.serviceTy natKey = some .nat`,
and `service_admitted_initial` discharges it at `initialWorld`.

**The interim.** Until seat C ties `w.serviceTy` to the source in `TypedState`, the typed state's
world may choose its service table. No proved theorem reads the stronger reading (the build is
green); C's tie should land with or before this branch.

## Step 5.2: the signature as data and its extension (`d905ea53`)

New `src/Effect4/Laws/Program/Signature.lean`, imported from `Laws.lean` after `Typed.Assembly`.
All proved (axioms in `SignatureControls.lean`): `argTy_congr` (`:45`) … `termTy_congr` (`:59`),
`causeTy_congr`; `SigExtends` (`:78`) with `refl`, `trans`, `termTy`, `causeTy`, `bodyRequires`;
the monotone family `hasTy_ext` (`:117`, one mutual block over the six judgments, the layer arms
for item G's three premises), `check_ext` (`:223`), `effTy_ext` (`:227`), `typeOfProgram_ext`
(`:231`), `checkLayer_ext` (`:239`), `rows_append` (`:247`); `SigApp` (`:264`) with `codeTy`,
`builtinCodeTy`, `serviceTy` (per code, row 113), `signature`, `serviceTy_nil` (`:295`) and
`signature_nil` (`:299`) by `rfl`, `serviceTy_code` (`:303`), `SigApp.rows_append`, `FreshCode`
(`:320`), `SigApp.services_append`. `π` (`restrictWorld`, `servicesFit_restrict`, `fits_restrict`)
moved to `Typed/Admission.lean` (`:155`, `:159`, `:177`) in 5.4. Red controls
`prepend_not_extends` (`SignatureControls.lean:48`), `shadow_not_extends` (`:72`),
`shadow_not_fresh` (`:81`), `one_code_two_carriers` (`:110`); positive `append_keeps_call`
(`:56`), `greet_extends` (`:95`), `per_code_one_carrier` (`:117`).

## Step 5.3: C3's reflection by one generic fold congruence (`3e2f3fe8`)

`EffAlgebra.AgreeOn` (`Signature.lean:379`, 64 fields: equality at every field that carries no
operation or service key, guarded equality at `eff_perform`, `eff_service`,
`eff_provideService`, `layer_succeed`, `layer_effect`), `readsAlg` (`:447`), **`cata_eff_congr_on`**
(`:518`) and its six siblings (one mutual structural recursion; its 66 cases generated by a
script from `Program/Fold.lean`'s `cata_*` arms; **no axioms**); `SigOkOp` (`:773`), `SigOkKey`
(`:776`), **`SigProgram`** (`:780`), `term?_ext` (`:784`), `check_alg_agreeOn` (`:793`),
**`check_restrict`** (`:876`: on a Σ-program the checker answers the same under every extension,
refusals included, at every environment and path), `effTy_restrict` (`:883`). Battery:
`badCall_same_refusal` (`:131`) and the red control `reflection_needs_sigProgram` (`:152`).
`check_restrict` replaces R2Probe §E's hand induction (`hasTy_restrict_looped`).

## Step 5.4: lawful signatures travel on the source (`ed7fad06`)

`ProgramSource` is in `Typed/Admission.lean`; for it to carry `LawfulSig`, `Signature.lean` no
longer imports the typed state, and `π` moved down. **Definitions and theorems** (`Signature.lean`):
`RowReason` (`:899`), `rowChecks` (`:921`, sixteen local checks: external, async, no built-in
collision, value-row trailing, no `int` per column, no internal handle in answer and error (row
97), `admitColumn` per column (row 127), template admissible per column, well scoped),
`ServiceReason` (`:940`), `flatCarrierAlg`/`flatCarrier` (a fold), `serviceChecks` (`:976`),
`firstFailing`, `firstIndexed`, `firstDup` with their `_eq_none_iff` laws, `SigRefusal`
(`:1047`), `sigRefusal?` (`:1056`), `admitSig` (`:1067`), **`LawfulSig`** (`:1073`: rows local,
row keys distinct, declarations local, codes distinct (row 113), every required key served),
**`sigRefusal?_eq_none_iff`** (`:1086`), **`admitSig_ok_iff`** (`:1111`), a `Decidable` instance,
`SigApp.lawful_empty` (`:1122`), **`lawful_append`** (`:1129`, C6). `Program/Admission.lean`:
`inhabitedAlg` (`:53`), `inhabited` (`:76`), `admitColumn` (`:82`).

| Declaration | Old | New |
| --- | --- | --- |
| `ProgramSource` (`Typed/Admission.lean:99`) | `program`, `table := []` | adds `services : List (ServiceKey × Ty) := []`, `lawful : LawfulSig ⟨table, services⟩ := by exact SigApp.lawful_empty` |
| — | — | `ProgramSource.sig` (`:108`), `ProgramSource.signature` (`:112`) |
| `PointTyped` | reads `nativeSignature src.table` | **unchanged** (the switch is joint with seat C's `capture_lookup`; below) |

Every statement over `ProgramSource` (M5, M6's ledger and capstone, `TypedState`) now ranges over
lawful sources without a change of text (row 114). Dependents: one build of the 222-module reverse
closure; two Test failures repaired (`TrivialPosts.lean` built a source on an unlawful table, now
`hostTable` with `hostTable_lawful` by `decide +kernel`; `SignatureControls` needed an import).
Battery: one `#guard` per refusal clause, three admitted, `one_code_twice_not_lawful` (`:187`),
`empty_request_not_lawful` (`:192`), `rowA_lawful` (`:196`).

## Step 5.5: row 116's positive control (`61e47b08`)

`Test/Program/TypedProgRows.lean`: `AsyncRowOnly` (`:34`) and **the tripwire** `asyncRowOnly_now`
(`:42`, `Iff.rfl` today; it stops elaborating when the domain bit lands in `asyncPre`),
`typedProg_not_table_monotone_of` (`:67`) and its instance `typedProg_not_table_monotone` (`:89`);
`AsyncEntryRows` (`:102`), `bitEntry`, `bitEntry_rows_append` (`:114`), and
**`typedProg_rows_append`** (`:192`, under `AsyncEntryRows`, by induction on `TypedProg`). 11
theorems, `[propext, Quot.sound]`.

## Step 6.1: TY-05, admission's located refusal is complete (`31596c4e`)

`src/Effect4/Program/Admission.lean`, all proved:

| Theorem | Line | Axioms |
| --- | --- | --- |
| `Table.findDup_eq_none_iff` (`findDup keys = none ↔ keys.Nodup`) | `:220` | `[propext]` |
| `Table.lawful_eq_true_iff` (the three conditions as a proposition) | `:233` | `[propext, Quot.sound]` |
| **`Table.checkLawful_eq_none_iff`** (`checkLawful t = none ↔ lawful t = true`) | `:254` | `[propext, Quot.sound]` |
| **`Table.checkLawful_of_not_lawful`** (TY-05: `lawful t = false → checkLawful t ≠ none`) | `:291` | `[propext, Quot.sound]` |

**Statement changed.** `admitProgram` (`:331`): old, `if hlawful : Table.lawful table = true then
(checkTable …) else match Table.checkLawful table with | … | none => .error (.duplicateKey ("",
[]))`; new, `match hlawful : Table.checkLawful table with` the three located refusals, and at
`none` the certificate takes `lawful` from `(Table.checkLawful_eq_none_iff table).mp hlawful`.
**The invented key is deleted.** Refusal order and results are unchanged (by the theorem).

**Dependents repaired:** `CheckedTyping.lean`'s `admitProgram_eq_ok` (three `split` arms close by
the theorem) and `Run.lean`'s `admitProgram_certificate` (the aesop call's simp set takes
`Table.checkLawful table = none`, named as a hypothesis since aesop's clause takes no applied
term). Built: `Program.Admission`, `Api`, `CheckedTyping`, `Folds.Ty`, `Signature`, `Codegen.Checked`,
`Laws.Run`, and the seven Test modules that evaluate or unfold `admitProgram` (419 jobs, exit 0).
Battery `Test/Program/AdmissionColumns.lean` (new, imported from `Test/All.lean`): the duplicate
key is located and reported (`#guard`s), `dupTable_located` (proved).

## Step 6.2: inhabitance agrees with membership; the column check, located (`de926765`)

**The fold and its laws** (`Membership.lean`, the one module that cases on `Ty`; all proved;
axioms printed in `AdmissionColumns.lean`):

| Theorem | Line | Axioms | What |
| --- | --- | --- | --- |
| `inhabited_of_fits` | `:2151` | `[propext, Quot.sound]` | sound against `Fits` |
| `inhabited_of_hasTy` | `:2187` | same | sound against DI-67's `Val.hasTy` (TY-14) |
| `handleFreeAlg`, `handleFree` (defs, a fold) | `:2227`, `:2250` | — | the data fragment |
| `fits_of_inhabited_handleFree` | `:2253` | same | complete on the data fragment, one witness for every world |
| `FreshFrom`, `Grows` (structures) | `:2321`, `:2327` | — | keys fresh from `n`; `fits_map`'s premises bundled |
| `Grows.refl`, `Grows.trans` | `:2334`, `:2337` | `[propext]` | |
| `Grows.fits` | `:2342` | same | membership survives growth |
| `FreshFrom.addFiber`, `.addRef`, `.addPromise`, `.allocExternal` | `:2348`–`:2391` | `[propext]` | a fresh declaration grows the world and keeps the keys above fresh |
| `fits_handle_fresh` | `:2397` | `[propext, Quot.sound]` | every `handle` target, in a grown world |
| **`fits_of_inhabited_fresh`** | `:2434` | same | **one world for several handles, by fresh keys** |
| `initialWorld_freshFrom` | `:2501` | none | |
| **`inhabited_iff_fits`** | `:2511` | `[propext, Quot.sound]` | **row 127's agreement, on every type** |
| `inhabited_iff_handleFree` | `:2521` | same | probe B's statement |
| `fiber_inhabited`, `cell_inhabited`, `promise_inhabited` | `:2533`–`:2543` | same | the three handle witnesses, in `subN` |
| `handle_inhabited` | `:2550` | same | the verifier's statement, as a corollary |
| `inhabited_sub`, `inhabited_subN` | `:2555`, `:2560` | same | closure under both orders |
| **`inhabited_normalize`** | `:2566` | same | `inhabited (normalize t) = inhabited t` |
| `inhabited_join` | `:2575` | same | |
| `admitColumn_iff` | `:2582` | same | the column check read through membership |
| `admitColumn_normalize` | `:2588` | same | |
| `prod_never_nat_empty`, `except_never_never_empty` | `:2594`, `:2597` | same | CE-015's columns have no member in any world |
| `prod_never_nat_no_hasTy`, `except_never_never_no_hasTy` | `:2601`, `:2607` | same | nor under any allocation table |
| **`admitColumn_prod_never_nat`**, **`admitColumn_except_never_never`** | `:2614`, `:2617` | same | **the column check refuses both** |

`inhabited_sub`, `inhabited_subN`, `inhabited_normalize` and `inhabited_join` follow from the
agreement and membership's own laws (`fits_sub`, `fits_subN`, `fits_normalize`), so probe B's
16-case `fun_induction Ty.sub` proof is not landed: one fewer induction over the order.

**The located column check** (`Program/Admission.lean`, core): `emptyColumnAt` (`:158`),
`findEmptyColumnInTable` (`:164`: every row's request, answer and error, by position),
`findEmptyColumnInEffTy` (`:175`: the program's inferred answer and error), with
`emptyColumnAt_eq_none_iff` (`:178`), `findEmptyColumnInTable_go_eq_none_iff` (`:185`),
**`findEmptyColumnInTable_eq_none_iff`** (`:198`), **`findEmptyColumnInEffTy_eq_none_iff`**
(`:205`), all `[propext, Quot.sound]`. The signature check refuses the same rows at the row and
column (`RowReason.emptyColumn`, 5.4). Names per row 149: the frozen `AdmitRefusal.uninhabited at`
stays the `int` scan's; the emptiness check is `emptyColumn at`.

**Held at the boundary: runner admission does not call the scan yet.** Its refusal
`AdmitRefusal.emptyColumn` is a new constructor of an input of the generated runner group
(`src/Effect4/Api/RunnerDerived.lean`'s exhaustive `toVal`/`ofVal` would stop compiling), and the
brief says "No generator". Decision D-A1 below has the options and the hunk. A tripwire `#guard`
in `AdmissionColumns.lean` pins today's behaviour (CE-015's host table is admitted) and fails
when the wiring lands.

**Battery** (`AdmissionColumns.lean`): the scans locate CE-015's three columns (a host-row
answer, a host-row request, a program answer) and leave `never`, `list never`, `option never`
alone (`#guard`s); two refusals, not one (TY-13: the `int` scan refuses `list int`, which has a
member, and misses `prod never nat`, which has none; `#guard`s); `admitSig` refuses the same rows
(`#guard`s); `ce015_table_refused`, `ce015_program_refused` (proved, `decide +kernel`); red
controls **`shared_key_not_fits`** (proved: a pair naming cell 0 twice fits
`prod (refOf nat) (refOf string)` in no world, so completeness needs fresh keys) and the CE-015
table's old acceptance under `#guard_msgs (error)`; `two_cells_inhabited` (the same type,
inhabited by the agreement). Command: `lake env lean -DwarningAsError=true
Test/Program/AdmissionColumns.lean`, 47 axiom lines, all at or below `[propext, Quot.sound]`.

Also in this commit: `Signature.lean`'s hand lemma `option_or_eq_none_iff` was core's
`Option.or_eq_none_iff`; removed, its four uses renamed.

## Step 7: TY-15 (`816b901b`)

`Template.lean:332-335`, the comment in `sub_not_complete`. Old: "`decide` cannot do this:
`Ty.sub` is a well-founded recursion and the kernel does not reduce it." New: plain `decide` gets
stuck (the elaborator does not unfold the well-founded recursion); the kernel reduces it, so
`decide +kernel` closes the fact (TY-15); the proof keeps the view's lemmas. **Tested** on the
exact proposition: `decide +kernel` closes it, plain `decide` fails with "did not reduce to
`isTrue` or `isFalse`". DI-15's sentence is proposed below.

## Seat B's item 4: `fits_nat_irrel` (`7ac4d4fc`)

`Membership.lean:1400`, `fits_nat_irrel (w) (n m : Nat) : ∀ t, Fits w (Val.nat n) t → Fits w
(Val.nat m) t`, one induction over the judgment, proved, `[propext, Quot.sound]` (printed in
`TermFits.lean`). Seat B's `fits_nat_val` and `fits_unit_val` (`Typed/Adequacy.lean:135`, `:142`)
are this file's `fits_nat_inv` (`:1370`) and `fits_unit_inv` (`:1364`), same statements, same
namespace: their move is the deletion hunk under "Integration".

## Final checks

- **The final build**, once: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` at `7ac4d4fc`:
  `Build completed successfully (713 jobs)`, 8 min 30 s, exit 0. The gate's lines: "library-root
  gate: 134 API/utility modules, 213 Laws-only modules; every library source is reachable;
  Effect4 never reaches Laws"; "checked 496 modules and 70101 declarations; semantic/test axioms
  are [propext, Quot.sound]; exact implementation boundary (15 module(s), 23 declaration(s))
  additionally allows Classical.choice".
- **The ledger at head** (same build): `M4Handshake` 1 open of 1, `M3bWorld` 1 of 3,
  `M3bAssembly` 1 of 2, `M6Ledger` 20 of 20, `Test.IndexedColumnDraft` 1 of 8; every other scope
  0 open. This seat opened and closed no obligation.
- **Row 132's census, rerun** (`lake env lean -M6144` in this worktree, exit 0 each):
  - `organization/probes/TyCasesInTyped.lean`: red control true; `Effect4.Laws.Program.Typed`: 3
    (`projectProduct_typed` and two compiler helpers of it, there at the formal pass);
    `Typed.Membership`: 62.
  - `organization/verify-TyCasesDeep.lean` (transitive): red controls true and true;
    `Typed`: 8 hits, 1 person-written (`projectProduct_typed`, as at the formal pass);
    `Typed.Admission`: 3 hits, 1 (`ProgramSource.mk.sizeOf_spec`, compiler-made, as at the formal
    pass); `Typed.Membership`: 80 hits, 20 person-written (64 and 9 at the formal pass).
  - The same probe widened to this seat's other modules (a scratch copy with the module filter
    extended): `Laws.Program.Signature`: 3 hits, 1 (`SigApp.mk.sizeOf_spec`, compiler-made);
    `Program.Admission`: 11 hits, 3 (`AdmittedProgram.mk.sizeOf_spec`,
    `AdmittedStraightProgram.mk.sizeOf_spec`, and `findInt`, the `int` scan, there at the base).
  So no person-written case analysis on `Ty` was added outside `Membership.lean` (tested).
  Membership's 20: `Fits`, `Fits.eq_def`, `Fits.hom`, `FlatFits`, `fits_factors`, `fits_hasTy`,
  `fits_instantiate_widens`, `fits_live`, `fits_map`, `fits_members`, `fits_nat_irrel`,
  `fits_normalize`, `fits_of_inhabited_fresh`, `fits_of_inhabited_handleFree`,
  `fits_queryReasons`, `flatFits_fits`, `flatFits_map`, `inhabited_of_fits`,
  `inhabited_of_hasTy`, `projectProduct_fits`.
- `make check-cases`: **not run**, no match on a policy family was added (reading of the diff
  under `src`: the new `match`es are on `Option`, `List` and `Bool`; `rowChecks` compares `RowKind`,
  `RowShape`, `Registration` with `==`, in Laws, outside the audit's `Effect4` import).
- No generator was run.

## Integration with `refactor/phase1-phase3` (to apply at integration; all by reading at `af3799f9`)

The merge was denied in this worktree (the one thing first). Files changed on both sides:
`Test/All.lean` and `src/Effect4/Laws.lean` (imports added at different anchors on each side:
keep both), `M6Capstone.lean` (this branch's one projection at the old `:783`; seat B's three
lambda binders near `:1235`, `:1753`, `:1793`: disjoint), `TrivialPosts.lean` (this branch's
`hostTable` near `:115`; seat B's `modify_typed` near `:63`: disjoint). The semantic hunks, in
seat B's files:

1. **A duplicate declaration (hard error).** `Typed/Adequacy.lean:246-255` declares
   `Effect4.Program.Typed.completionOk_of_fitsExit` (at `Env.Requirement.empty`); this branch's
   `Membership.lean:1340` declares the same name at any requirement. Delete B's theorem and its
   docstring; its one use (`completionOk_of_fitsExit strong.1`, `:637`) reads this branch's.
2. **One home for the value facts (row 132, seat B's item 4).** Delete `fits_nat_val` and
   `fits_unit_val` with their docstrings (`Adequacy.lean:134-146`; keep the section header, the
   `modify_nat` facts follow it) and rename the uses: `fits_nat_val` → `fits_nat_inv` (`:176`),
   `fits_unit_val` → `fits_unit_inv` (`:881`, `:889`, `:897`, `:905`, `:913`, `:921`, `:929`).
3. **`Equiv` in `subN` (seat B's item 1).** `Adequacy.lean:176`:
   `obtain ⟨n, rfl⟩ := fits_nat_inv (fits_subN w equiv.1 a fa)` (with item 2's rename);
   `:469` and `:484`: `exact fits_sub w equiv.2 _ trivial` → `exact fits_subN w equiv.2 _ trivial`
   (`fits_subN` has `fits_sub`'s argument order: `w`, the order fact, the value, the membership).
   `ProtocolPosts.lean`'s `refModify_pre_refuses` and `refModifySome_pre_refuses` (`:368`, `:377`)
   need no edit: `sub` becomes `Ty.subN Ty.bool Ty.nat = true`, and the same
   `absurd sub (by decide +kernel)` refutes it (tested here on exactly that term).
4. **The world order's new conjunct (seat B's item 2).** Append `, rfl` after
   `fun _ _ _ h => h` in the `World.le` tuple at `Adequacy.lean:93`, `:287`, `:351`
   (`fun _ _ _ h => h⟩, ext⟩` → `fun _ _ _ h => h, rfl⟩, ext⟩`) and at `FramesNotKripke.lean:85`,
   `:655` (`fun _ _ _ h => h⟩, fun _ _ h => h⟩` → `fun _ _ _ h => h, rfl⟩, fun _ _ h => h⟩`). Every
   world there is a record update, so `rfl` closes `newer.serviceTy = w.serviceTy`. No projection
   in B's files reads the token conjunct by `.2.2.2.2.2` (the `storePre_mono`/`fiberPre_mono`
   projections `ord.1.2.1`, `.2.2.1`, `.2.2.2.1` are unchanged).
5. **`servicesFit_map`'s lookup premise (seat B's item 3).** `Residual.lean:633`:
   `exact servicesFit_map hPi hRho ord.2 h` →
   `exact servicesFit_map hPi hRho ord.2 (serviceTy_of_le ord.1) h`.
6. **`deferredCompleteWith`'s reference arm (seat B's item 6, with `World.lean:81`).**
   `Residual.lean:56`: `| .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub a = true` →
   `… ∧ t.subN a = true`; then `storePre_mono`'s arm and `Adequacy.lean:638`'s `exact strong`
   read it unchanged.
7. **A repeated inversion.** `FitsOrder.lean:283` keeps a local `fiber_inv` (kept local because
   `Residual.lean` is seat B's file); B landed `TypedProg.fiber_inv` (`Residual.lean:269`), the
   same statement over any source. Delete the local one and call `TypedProg.fiber_inv` at `:324`, `:356`,
   `:359`, `:362` (no clash meanwhile: the names live in different namespaces).
8. **Batteries of this branch that case-split seat B's definitions.** `TypedProgRows.lean`'s
   `storePre_rows_append`, `asyncPre_rows_append`, `fiberPre_rows_append` and
   `typedProg_rows_append`: by reading, B changed `storePre`'s arms (the new ones read no source,
   so the catch-all `exact h` covers them), not `asyncPre`'s external arm, not the `TypedProg`
   constructors; expected to build unchanged.
9. `Ty.sub_refl _` sites on the integration branch (`FramesNotKripke.lean:92`, `:371`, `:723`,
   `Residual.lean:467`, `H2PartOne.lean:160`, `:192`, `TrivialPosts.lean:46`,
   `M6Capstone.lean:168`, `:182`): no edit. Some prove raw-order facts (a certificate, or seat C's
   `RacePayload` comparisons today), the rest `subN` facts, and the term elaborates at both by
   unfolding `subN` (tested on the pattern).

**Statements of this branch that read the typed state seat C restates** (`TypedState` without its
queue argument, `J = MachineTyped`, `I = ConfigTyped`, `Preds.ScopeExitOk`), to restate at
integration with C's result:

- `Test/Counterexamples/Machine/Semantics/ValueMembership.lean:989`, `typedStateF_load` (now at
  every source and budget; it builds every `TypedState` component at `initialWorld`), and its
  instances `typedStateF_load_ref` (`:1033`), `typedStateF_load_get` (`:1038`).
- `FitsOrder.lean`: `m5_forces_leaf` (`:314`, destructures `TypedState`'s fiber, saved-position
  and stack components), `prog3_loads_typed` (`:524`), `prog3_leaf` (`:528`), and the historical
  `Reviewed.m5_false` (`:398`), `Reviewed.typedState_load_false` (`:404`),
  `capstone_implies_load` (`:430`), `Reviewed.capstone_false` (`:440`) (statements over
  `∃ w, TypedState root rootTy w m`). `rreachable_load` (`:425`) reads `RReachable` only.
- No statement of this branch reads `Preds.ScopeExitOk`, `MachineTyped` or `ConfigTyped`.

## For seat B (beyond the integration hunks)

1. **Row 116's domain bit** in `asyncPre`'s external arm is not on `af3799f9` (reading). The ruled
   entry is `bitEntry` (`TypedProgRows.lean`): `(nativeSignature root.table).dom op = true ∧`
   the row's columns below the certificate. When it lands, `asyncRowOnly_now` stops elaborating
   (the tripwire); replace it, prove `AsyncEntryRows` from `bitEntry_rows_append`, and
   `typedProg_rows_append` holds outright (it can then move beside `typedProg_mono` in
   `Residual.lean`).
2. **`fits_nat_irrel`** (`Membership.lean:1400`) is landed for the six `f.total` ref rows of
   `M3bAdequacy` (with B's proposed `cases f` lemma on `FnName.total`/`partialUpdate` and
   `poke_world`).
3. Row 137 (a)'s text puts the protocol entries that compare a declared type with a certificate
   in `subN`; B's review (its `asyncPre` docstring) keeps `asyncPre`, `awaitAll` and `raceAll` in
   `Ty.sub`, the certificate being the derivation's choice and `fits_normalize` the bridge.
   Nothing in this branch depends on either reading; the coordinator's call.
4. The joint switch below (`storePre`'s `memoGet` and `asyncPre`'s external arm read
   `root.signature`).

## For seat C (exact statements)

1. **Row 137** (the coordinator's assignment): `Assembly.lean:40`,
   `| .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true` →
   `… ∧ Ty.subN t ty.answer = true` (matches `CompletionOk.ofRefGet` and B's `Residual.lean:56`);
   `Scheduler.lean:55` (`FiberColumnsBelow`), `:67` (`RacePayload.live`), `:69`
   (`RacePayload.programs`): `x.sub y = true` → `Ty.subN x y = true`, if C keeps these as
   declaration comparisons (B's review keeps certificate comparisons raw; these three compare a
   declared fiber type with a result type, which is row 137's case).
2. **The source/world tie (row 112)**, a conjunct of `TypedState` (or of C's `MachineTyped`):
   `w.serviceTy = root.sig.serviceTy`. At load, `initialWorld` must then set
   `serviceTy := root.sig.serviceTy`; for `services = []` this is the default by
   `SigApp.serviceTy_nil` (`rfl`), so `typedStateF_load` is unchanged for every source in the
   tree (all have `services = []`).
3. **The joint switch to the source's signature** (with seat B): `PointTyped`
   (`Typed/Admission.lean:116`), `CaptureTyped` (`Assembly.lean:45`, two
   `nativeSignature root.table`), `storePre`'s `memoGet`, `asyncPre`'s external arm:
   `nativeSignature src.table` → `src.signature`. Equal today for every source with no
   declarations (`SigApp.signature_nil`, `rfl`), so the switch is a no-op until a source declares
   services; it must be made in one commit because `capture_lookup` reads `PointTyped`'s checker
   call against `CaptureTyped`'s.
4. **M5's and M6's premise** reads the source's signature: the ledger's
   `Api.typeOf root.program root.table = some rootTy` (`Assembly.lean:263`, and M6's) becomes
   `typeOfProgram root.signature root.program = some rootTy`, equal to it for every source with
   no declarations (`SigApp.signature_nil`).
5. **TY-08's promise half**: the coarse `PromiseTable` column from `preds.PromiseCell`'s strong
   leaf, through `completionOk_of_fitsExit` (`Membership.lean:1340`) and the `.ofRefGet` arm in
   `subN`; then `WorldValid.cells` can be dropped (a `Validity.lean` field).
6. **M5's reduction lemma**: `ValueMembership.typedStateF_load` (`:989`) is the statement to move
   beside `typedState_load` (Assembly), restated for C's split:
   `(closed : ClosedEff ty) (noMarker : raceRegistrationR (denoteR root.program root.program
   (rootPoint compileFuel)) = none) (code : ∀ w, TypedProg root w ty (denoteR root.program
   root.program (rootPoint compileFuel))) : ∃ w, TypedState root ty w (loadR root.program fuel
   compileFuel)`. It reduces M5 at a source to the loaded code's typing.

## Lines proposed for the coordinator's files

**`docs/core/decisions.md`** (one sentence each, for the rows' status cells):

- Row 96: "D1 as amended by row 137: 'exactly the declared type' is equality of normal forms;
  `Equiv` compares in `Ty.subN` both ways (`Ty.subN_equiv_iff`), landed by seat A (`bbed898d`)."
- Row 111: "Σ_app landed in Laws (`Laws/Program/Signature.lean`, seat A): `SigApp`, `SigExtends`;
  C3 both halves (`check_ext`, `check_restrict` through one generic fold congruence
  `cata_eff_congr_on`), C5 (`restrictWorld`, `servicesFit_restrict`, `fits_restrict`), C6
  (`LawfulSig`, `admitSig_ok_iff`, `lawful_append`), C4's append direction under row 116's entry
  (`typedProg_rows_append`, a battery); C1 trivial; C2, C7, C8 open."
- Row 112: "Shape A landed (seat A, `f920d4e8`): `World.serviceTy`, fixed by `World.le`, read by
  `ServicesFit`; the tie to the source is seat C's; until it lands the typed state's world chooses
  its table."
- Row 113: "Per-code carriers landed: `SigApp.serviceTy`, `serviceTy_code`; red control
  `one_code_two_carriers`."
- Row 114: "`LawfulSig` (local clauses, pairwise distinct keys and codes, served keys) travels on
  `ProgramSource.lawful` (default `SigApp.lawful_empty`); `admitSig_ok_iff` is its located
  refusal; M5 and M6 range over lawful sources."
- Row 115: "An appended row extends the signature (`SigApp.rows_append`; `rows_append` at
  `nativeSignature`), lawfulness composes over an append (`lawful_append`), and a prepended or
  shadowing row is not an extension (`prepend_not_extends`, `shadow_not_extends`, proved)."
- Row 116: "The positive control is proved under the entry's transport (`typedProg_rows_append`,
  `TypedProgRows.lean`); the domain bit in `asyncPre` is still owed (seat B's file); a tripwire
  marks it."
- Row 127: "`inhabited` (a `TyAlgebra` fold, `Program/Admission.lean`) agrees with `Fits` on every
  type (`inhabited_iff_fits`, one world for several handles by fresh keys) and is sound against
  `Val.hasTy`; `admitColumn` refuses `prod never nat` and `except never never`
  (`admitColumn_prod_never_nat`, `admitColumn_except_never_never`); located by
  `findEmptyColumnInTable`/`findEmptyColumnInEffTy` and in `admitSig`; runner admission's wiring
  waits on D-A1 (the generator)."
- Row 137: "Landed at `Membership.lean`'s handle arms (`bbed898d`) and `World.lean:81`
  (`55fe8043`), seat A; `Residual.lean:56` at integration (seat B's token); `Assembly.lean:40`,
  `Scheduler.lean:55`, `:67`, `:69` are seat C's."
- Row 149: "The emptiness check is named `emptyColumn` (`RowReason.emptyColumn`, the scans);
  `AdmitRefusal.uninhabited` stays the `int` scan's; `AdmitRefusal.emptyColumn` waits on D-A1."

**`docs/DESIGN-ISSUES.md`**: DI-15, the identity sentence: "Identity of types is equality of
normal forms, the kernel of `Ty.subN` (`Ty.subN_equiv_iff`, `Ty.ofRaw_eq_iff`)." DI-67: "Decided
by `inhabited`, a fold that agrees with `Fits` on every type (`inhabited_iff_fits`) and is sound
against `Val.hasTy` (`inhabited_of_hasTy`); admission refuses an empty column that is not `never`
as `emptyColumn at`; `uninhabited at` stays the `int` scan's (row 149)."

**The contract line** (`Test/contracts/foundation-wave2.contract.md:217-219`): none (row 149 (a):
no revision). TY-14's citation of both agreement theorems there waits for a reconciliation the
owner has not asked for.

**`Test/Counterexamples/REGISTER.md`** (seat F's register):
E4-TYPED-CE-009: "REPAIRED 2026-10-01 (seat A, `bbed898d`, `55fe8043`, `ea77af5f`): `Fits` and
`CompletionOk` compare declarations in the checker's order; `FitsOrder.lean`:
`prog3_loads_typed` (the refuted instance loads typed), `rawLeaf_false`; historical
`Reviewed.m5_false`, `Reviewed.typedState_load_false`, `Reviewed.capstone_false`; the protocol
entries' declared-type comparisons at `Residual.lean:56` (B), `Assembly.lean:40`, `Scheduler`
(C) complete it." E4-TYPED-CE-006: append "`Equiv` compares in `Ty.subN` since 2026-10-01 (row
137); `natCell_equiv_spelling` through `Ty.sub_le_subN`." E4-TYPED-CE-015: "REPAIRED at the
column and the signature (seat A, `de926765`): `admitColumn_prod_never_nat`,
`admitColumn_except_never_never`, `findEmptyColumnInTable`, `admitSig`'s `emptyColumn`; runner
admission still admits (D-A1; tripwire in `AdmissionColumns.lean`)."

**`docs/core/host-boundary.md` §4.4**: "exactly" reads "equal normal forms" (row 137).
**`docs/core/system-map.md`**, the type row: types up to `≡N` (equal normal forms) are the
checker's types, `Ty/≡N ≅ CTy`; the order is `Ty.subN`.

## Decisions for the coordinator

**D-A1. Runner admission's emptiness refusal needs the generator.** Options: (a) authorize
regenerating the `derived` family (`python3 scripts/generate.py --only derived`, or the Runner
command in `RunnerDerived.lean`'s header) and apply the hunk below; (b) keep runner admission as
is and let `LawfulSig` (source admission) carry row 127 alone; (c) defer to wave 2. Recommended:
(a), since row 127 is ruled and CE-015 names runner admission. The hunk (`Program/Admission.lean`):

```lean
-- AdmitRefusal, after `internalHandle`:
  /-- A request, answer or error column of the table, or the program's answer or error
  column, is empty and is not `never` (rows 127, 149). -/
  | emptyColumn («at» : Path)
-- AdmittedProgram, after `intFreeType`:
  columnsTable : findEmptyColumnInTable table = none
  columnsType : findEmptyColumnInEffTy ty = none
-- admitProgram, the last arm (after `checkTable`):
          | none =>
            match hcolumns : findEmptyColumnInTable table with
            | some pos => .error (.emptyColumn pos)
            | none =>
              match hcolType : findEmptyColumnInEffTy typing.ty with
              | some pos => .error (.emptyColumn pos)
              | none => .ok ⟨typing, (Table.checkLawful_eq_none_iff table).mp hlawful, hrunnable,
                  htable, hinternal, hprogram, htype, hcolumns, hcolType⟩
```

Placed last, so `admitProgram_table_int`, `_table_internal`, `_program_int`, `_type_int` keep
their statements. Dependents: `admitProgram_eq_ok` (two more `split` arms closed by the new
fields), `admitProgram_certificate` (two more simp facts) and `admitted_unique` (two more `_` in
each pattern), the hand-built certificates `Test/Run/RunContract.lean:97` and
`Test/Api/HostSessionContract.lean:18` (two fields `:= by decide +kernel` each), the generated
`RunnerDerived.lean` (one constructor at index 7), the module docstring's list of admission
requirements (a sixth: every column inhabited or `never`), and the tripwire in
`AdmissionColumns.lean` (delete; add the refusal `#guard`). Not compiled (assumed).

**D-A2. Template parameters in row columns.** `inhabited (var i) = false` agrees with `Fits` (a
parameter has no member), so `admitColumn` refuses a templated column such as `var 0`, and with it
`LawfulSig` (and, once wired, runner admission) would refuse a well-scoped polymorphic host row
(`request := var 0, answer := var 0`). No row in the tree has a parameter today (every native row
is closed, `NativeOp.row_closed`; no test source declares one), so nothing is refused now (tested
by the green build). Options: (a) check row columns with parameters read as inhabited (the fold
with `ty_var := true`), leaving instances to the program's own columns; (b) refuse templated rows
until rows 42–43 land; (c) check closed columns only. Recommended: (a), when rows 42–43 make rows
templated.

**D-A3. `serviceTy` interim** (row 112): merge seat C's tie with or before this branch.

## Owed, and why

- The integration (the one thing first); this receipt names its hunks, none compiled merged.
- D-A1's wiring (the generator), with CE-015's runner half.
- Row 116's domain bit (seat B's file) and the tripwire's flip.
- The joint switch to `src.signature` (seats B and C) and C's tie, premise, TY-08 half and M5's
  reduction lemma (above).
- `evalTerm_fits` is consumed by no theorem yet: owed consumption by M5's denotation lemma and
  the command proofs (wave 2).
- C2, C7, C8 of Σ_app; C4's iff (only the append direction, under the entry, is proved).

## Plan §5

1. **Repeated proofs that disappeared.** `typedState_load_of_code` folded into the generalized
   `typedStateF_load` (one proof); C3's reflection by one generic congruence
   (`cata_eff_congr_on`, 66 generated cases, no axioms) replaces R2Probe §E's hand induction;
   `inhabited_sub`, `_subN`, `_normalize`, `_join` read membership's own laws through the
   agreement, so probe B's 16-case induction over `Ty.sub` is not written; `option_or_eq_none_iff`
   removed for core's lemma. At integration (hunks 1, 2, 7): B's `completionOk_of_fitsExit`,
   `fits_nat_val`, `fits_unit_val` and this branch's local `fiber_inv`.
2. **Program-to-execution connections closed.** M5 at the TY-01 program: the checker-certified
   program loads into a typed state (`prog3_loads_typed`), the first positive control after M5
   was proved false. Term soundness from checker typing to runtime membership
   (`evalTerm_fits`). The checker's answer is invariant under signature extension on Σ-programs
   (`check_restrict`). Inhabitance at admission agrees with runtime membership
   (`inhabited_iff_fits`). The ledger's open counts are unchanged by this seat (M6Ledger 20 of 20).
3. **The eventual claim.** M7 covers the frame machine at the empty host table, on answer-free
   tapes, with observation `obs` (row 138). This seat's work is part of its typing side: values
   in the checker's order, the lawful signature as data, inhabited columns. Nothing here is
   "verified lowering" or host safety; the source-with-services case and runner admission's
   emptiness refusal are outside what is proved.
