# Seat D2 receipt: M5's denotation lemma (`denoteR_typed`, decisions row 148)

Seat D2 of the 2026-10-01 landing, wave 2. Brief: `docs/research/2026-10-01-landing/brief-D2.md`
with its "Amendments at dispatch" (base `bd5462df`), and the coordinator's mid-task message
(reference-to-reference chains, `E4-TYPED-CE-020`, decisions row 170). Plan: `plan.md` (§4 rules,
§5 measure). Worktree `/Users/pooks/Dev/lean4-effect4-seat-D2`, branch `seat/D2`. Evidence words:
**proved** (a kernel theorem compiled here, axioms printed), **reproduced** (another seat's proved
fact compiled again here), **tested** (a finite check run here: a build's report, a `#guard`, a
`decide`, a `grep`), **assumed** (not run here; a reading names the lines read).

This file is written incrementally: a stop at any point leaves a true record of what was done up
to that point.

## The one thing first

This branch changes four statements other seats read, and D4 merges first: `PointTyped`
(`Typed/Admission.lean:136`, a fourth conjunct: the point's completed view typed at the world,
row 175), `DenotesTyped` (`Typed/Assembly.lean:889`, the premise `layerRefsWF`, row 170, and the
world's service table tied to the source's, row 175), `machineTyped_load` (`:928`, its `code`
premise at the initial world only) and `loadsTyped_of_denotesTyped` (`:1013`, which threads all
three); `capture_lookup` (`:823`, and its `M3bAssembly` goal at `:1472`) gained the view premise.
`git merge-tree --write-tree f4881f74 HEAD` is textually clean (tested), but the four statements
must be reconciled by hand against D4's. M5 itself is **not** closed: `denoteR_typed` stays open
(`M3bAssembly` 3 open, 1 proved, 4 total, as at the base; tested). Groups 1–3 of its arms are
proved (terms, sequencing and handlers, every fiber row); groups 4–6 and the layer family are owed,
stopped by the owner's instruction of 2026-10-01, each written below with its exact obstacle.

## Base and head

Base: `bd5462df` (`refactor/phase1-phase3` after seats J and D1 and probe S). Head: the commit
that adds this receipt, on top of `95a75fed` (the last code commit). Commits, in order:
`55be93a6` (the statement repairs, rows 170/175, and the battery), `2929983a` (group 1),
`82110a5c` (group 2), `5f8cbe18` (group 3), `95a75fed` (the Membership template bridge, row 183),
then this receipt (`git add -f`).

## Work log (incremental)

- Read in full: `brief-D2.md` with its amendments, `plan.md`, `brief-G.md`'s "Rules", receipts E,
  I, I2 and D1, decisions rows 117, 136, 148, 151, 152, 153, 156 (`docs/core/decisions.md`,
  read-only, main checkout), the algebra note's A3/A4 and its fundamental-property paragraph
  (`docs/research/2026-10-01-formal-pass/algebra/note.md:240-298`, `:349-358`), Codex's
  `codex-second-eyes/2016-d1-review.md`.
- Read the sources the proof rests on: `Typed/Assembly.lean` (M5 section, ledger),
  `Typed/Residual.lean` (all), `Typed/Admission.lean` (all), `Typed/Seq.lean`, `DenoteR.lean`
  (all), `Program/Checker.lean` (all), `Typing/CheckInversion.lean`, `ReferenceTyping.lean`,
  `Program/Refs.lean`, `Typed/Membership.lean` (definitions), `Program/Compile.lean` (`Point`),
  `Test/Program/LayerRefs.lean`, `ScopePresence.lean`.
- The clone is current: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly
  Test.Program.LayerRefs Test.Program.TypedCorpus` replayed 392 jobs in 0.8 s (tested).
- Coordinator's mid-task message 1 (reference chains, row 170) received after the reading above:
  measure Codex's candidate first, then apply row 170 if it holds.
- Measured (proved, scratch probe `scratchpad/d2/Chain6.lean`, then landed): see "The statement
  repairs" below. While measuring I found two more refutations of `DenotesTyped` that survive row
  170 (the completed view; the service table), proved both on probes, and a third gap by reading
  (built contexts); I sent them to the coordinator (one message) before going on.
- Coordinator's mid-task message 2: ruled option (a) for the completed view and the service table
  (decisions row 175; ids `E4-TYPED-CE-021`, `-022`); assemble under `DenotesTyped` itself; finish
  the built-context refutation through the memo-hit path (`E4-TYPED-CE-023` if it holds), no
  `Fits` arm and no memo post changed without the owner; keep `PointTyped`'s new conjunct one
  hunk and list every site that builds a `PointTyped`.
- Commit `55be93a6`: the statement repairs (rows 170, 175) and the three witnesses.
- Coordinator's messages 3 and 4: granted `fits_flatFits` and `fits_tagPayload` in one end section
  of `Typed/Membership.lean`, and the Signature import (option (i)). Commit `2929983a` (group 1).
- Commit `82110a5c` (group 2).
- Coordinator's message 5: granted `fiberTy_eq_some` in the same section (the seven fiber arms read
  the checker's `fiberTy`; no shape hypothesis in a landed arm statement). Commit `5f8cbe18`
  (group 3).
- Group 4: the host-row arm does not close at template rows without a bridge (reading); sent to the
  coordinator with options (A) a membership bridge, (B) a named open goal. Coordinator's message 6:
  (A) granted (`fits_instantiate`, `valueVars_normalize`, `valueVars_of_noInternalHandle`), and the
  finding recorded as decisions row 183, its text, control, reopened proofs and estimate owed here.
- Coordinator's messages 7 and 8 (the owner's instruction): no new steps; commit the Membership
  additions if they build alone, no further arms, no roots build; the receipt with the merge notes
  against `f4881f74`. Commit `95a75fed` (the bridge). Group 4's arms were drafted (scratchpad, not
  compiled) and are not in the tree.

## The statement repairs (rows 170 and 175), measured facts first

All three witnesses are kernel-checked in `Test/Program/TypedDenotation.lean` (commit `55be93a6`),
every theorem printed at `[propext, Quot.sound]` or `[propext]` (36 lines, `lake env lean
-DwarningAsError=true`, exit 0; tested).

**`E4-TYPED-CE-020` (Codex's candidate; row 170).** Root `.bind (.provideLayer (.succeed K (.nat
7)) false U) (.bind (.provideLayer (.ref [0, 0]) false U) (.provideLayer (.ref [1, 0, 0]) false
U))`, `U = .succeed (.lit .unit)`, `K = Test.Program.TypedSplit.key`. Measured, in the order the
coordinator asked:
1. `chain_not_wf : chainRoot.layerRefsWF = false` (proved, `decide +kernel`); and
   `chain_refused : Program.typeOfProgram chainSrc.signature chainRoot = none` (proved): the load's
   checker premise refuses the program.
2. `chain_point : PointTyped chainSrc w chainPoint (EffTy.pure .unit)` at every world, `chainPoint
   = ⟨[1, 1], [], 5, [], [], 0⟩` (proved; the expansion's rounds resolve the chain to the layer at
   `[0, 0]`, `chain_check` by `decide +kernel`).
3. `chain_build : denoteLayer chainRoot (.ref [1, 0, 0]) q m scope = .pure badShapeExit` at every
   point with fuel (proved, `denoteLayer_ref_succ` and `target_is_ref`).
4. `old_chain_refuted : ¬ OldDenotesTyped chainSrc` (proved): the inversion closes in 15 steps
   (suspend, construction, the layer scope's allocation at a world whose store holds scope 0, the
   `onExit` body, the build guard's body, the context read, the memo fork, `buildWithMemoMapR`'s
   context read and set, the region's `onExit` body, the build guard's body, `unguard badShapeExit`).
   The world has the default service table and the empty context's membership holds at every
   table (`emptyCtx_fits`), so this witness does not lean on row 175.
   `OldDenotesTyped`/`OldPointTyped` are local copies of the statements at the base.
Repair: `chain_denotes : DenotesTyped chainSrc` (proved; the premise fails, `chain_not_wf`).
**Seeded and repaired**: the register's `E4-TYPED-CE-020` is seeded by `old_chain_refuted` and
repaired by row 170 (`chain_denotes`; `layerRefsWF_of_typeOf` discharges the premise at the load).

**`E4-TYPED-CE-021` (row 175).** The typed corpus's `awaitFiber.value` (`bind (fork (succeed 1))
(awaitFiber (var 0) awaitValue)`, well formed: `await_wf`). Point `viewPoint = ⟨[1], [fiber 1], 5,
[], [(1, success "x")], 0⟩` (the bind's continuation point, constructed with a completed view the
world does not type), world `w1` with `Γ 1 = pure nat`. `view_point_old` (proved): the base point
typing admits it at `pure (exitOf nat never)`. `old_view_refuted : ¬ Row170DenotesTyped awaitSrc`
(proved): `denoteR_awaitFiber` answers `.pure (success (exitOk "x"))`, which does not fit.
Repair: `view_point_refused : ∀ ty, ¬ PointTyped awaitSrc w1 viewPoint ty` (proved).

**`E4-TYPED-CE-022` (row 175).** `.service ⟨4, 4⟩` (native carrier `nat`, well formed:
`service_wf`), world `w2` with `serviceTy := fun _ => none`. `service_point_old` (proved);
`strCtx_fits` (proved): a context holding `str "x"` under the key fits `Ty.context` at `w2`;
`old_table_refuted : ¬ Row170DenotesTyped serviceSrc` (proved). Repair:
`table_world_excluded : w2.serviceTy ≠ serviceSrc.sig.serviceTy` (proved).

**What changed in `src/`** (commit `55be93a6`):
- `Typed/Assembly.lean`: `DenotesTyped root := root.program.layerRefsWF = true → ∀ w,
  w.serviceTy = root.sig.serviceTy → ∀ p e ty, … → PointTyped root w p ty → TypedProg …` (the
  tie spelled as `MachineTyped.services` spells it); `layerRefsWF_of_typeOf` (new, proved);
  `machineTyped_load`'s `code` at `initialWorld rootTy root.sig.serviceTy` only (proof unchanged
  but for `code _` → `code`); `typedState_load_of_code` passes `code _` (statement unchanged);
  `loadsTyped_of_denotesTyped` threads the premise, the tie (`rfl` at the initial world) and the
  empty view; `capture_lookup` and its `M3bAssembly` goal take `hview` (the view the release is
  constructed with). Docstrings of `DenotesTyped`, the M5 section, `machineTyped_load`.
- `Typed/Admission.lean`: `PointTyped`'s fourth conjunct `∀ q ∈ point.completed, ∃ fty, w.Γ q.1 =
  some fty ∧ ExitOk w fty q.2` (one hunk with its docstring paragraph).
- `Typed/Residual.lean` (consequential, measured: two lemmas): `pointTyped_mono` transports the
  view (`ord.1.2.1` on `Γ`, `strongExit_mono`); `pointTyped_rows_append` passes it through.

**Every site that builds a `PointTyped`, and its discharge** (tested: the typed cone built; for
seat D3's merge):

| Site | Discharge |
| --- | --- |
| `Typed/Residual.lean` `pointTyped_mono` | the view transported (`ord.1.2.1`, `strongExit_mono`) |
| `Typed/Residual.lean` `pointTyped_rows_append` | passed through (`hview`) |
| `Typed/Assembly.lean` `capture_lookup` | the new premise `hview` (the `construction` post at `denoteFin`'s `foreign` arm) |
| `Typed/Assembly.lean` `loadsTyped_of_denotesTyped` | `fun _ h => nomatch h` (root point, empty view) |
| `ScopePresence.point_admitted` | `fun _ h => nomatch h` |
| `ScopePresence.forkAfterMake_typed` (the `forkIn` child) | the `construction` post, named `view` |
| `LayerRefs.root_typed`, `TrivialPosts.hostBody_admitted`, `FitsOrder.prog3_typedF`, `AwaitLoad.fork_typed`'s body, `LoadedAdmission` (5 sites) | `fun _ h => nomatch h` (points under a root point) |

Destructuring sites took one more binder (`-`): `FitsOrder.lean:319`, `ProtocolPosts.lean:927`,
`AwaitLoad.cert_of_bodyTyped`, `ScopePresence.forkAfterMake_denotes`. `machineTyped_load`'s callers
pass the code at the initial world: `AwaitLoad.loadsTyped` (`code_typed _`), `FitsOrder` (two,
`prog3_typedF _`). A command proof that builds a `PointTyped` for a body at a point built by a
`construction` reads the post; at a point under a root point the view is empty.

**Builds** (tested): `lake build` of `Typed.Assembly`, `Seq`, `Adequacy`, `ExitConnector`,
`ForkSource` exit 0 (Admission, Residual, Seq, Adequacy, Stack, Assembly rebuilt); the 25 test
modules of `Typed.Admission`'s reverse import cone (`scratchpad/d2/tools/cone.py`): first run
failed at the sites above, then `LoadedAdmission` (five sites), then exit 0 (586 jobs), no
`sorryAx` in the final log; `lake build Test.Program.TypedDenotation Effect4.Laws` exit 0 (543
jobs). Ledger unchanged by this commit: `M3bAssembly` 3 open, 1 proved, 4 total.

## Group 1: the tools and the term arms (commit `2929983a`)

- **Membership additions (approved by the coordinator on 2026-10-01, the brief's file list
  extended for pure additions):** `fits_flatFits` and `fits_tagPayload`, one end section of
  `Typed/Membership.lean`, and `import Effect4.Laws.Program.Signature` as the last header line
  (option (i) of my request; `flatCarrier` is Signature's). Cost (tested): Membership's import
  cone grows from 174 to 180 modules (`scratchpad/d2/tools/fwd.py`); `lake build
  Effect4.Laws.Program.Typed.Membership` exit 0, 364 jobs, Membership alone rebuilt; its reverse
  cone (36 modules) rebuilt green (37 built, 589 jobs). Proposed cleanup for the coordinator's
  list: `flatCarrier` is a predicate on `Ty`, so its home is beside `Ty`, with `Signature.lean`
  importing it from there; not this seat's change.
- **`Typed/Seq.lean`** (proved): `guardBind_typed` (the general guard compatibility lemma),
  `seqGuard_typed`, `catchGuard_typed`, `allGuard_typed`, `exitOk_widen` and its two halves,
  `typedProg_widen`, `exitOk_restore`, `finalizer_typed`, `onExit_typed`; `seq_typed` re-proved
  as `seqGuard_typed`'s instance (statement unchanged; its consumers built unchanged).
- **`Typed/Denotation.lean`** (new; imported by `Typed/Assembly.lean` as its last import, so
  `Assembly`'s cone grows by `Seq`, `Denotation`, `Laws/Program/Decision`, `Laws/Program/Residual`
  and `Admit`, measured with `fwd.py`): the expansion's rounds commute with the constructors
  (`Eff.expandIn_bind` …, 17 lemmas, `rfl` per round); `node_at_child`, `pointTyped_child`,
  `serviceTy_leHost`, `completed_mono`; term progress at a world's allocation table
  (`atom_progress`, `evalTerm_progress`, `evalTerms_progress`, `evalTerm_progress_env`,
  `causeOf_progress`, `valOfErr_errOf_fits`, `shapeFree_die_of_fits`): the coarse
  `evalTerm_isSome` reads `Val.hasTy` at the empty allocation table, where no external handle has
  a type, so progress is re-derived at membership; `pending_typed`, `suspendR_typed`,
  `constructR_typed`; arms `denoteR_zero_typed`, `succeed_arm`, `fail_arm`, `failCause_arm`,
  `sync_arm`, `yieldNow_arm`. `envTyped_nil` and `envTyped_append` moved here from
  `Assembly.lean` (same names; `Assembly` imports this module; one copy, not two).
- Axioms (tested, scratch `AxG1.lean`): 55 theorems, 37 `[propext, Quot.sound]`, 18 `[propext]`.
- Builds (tested): `lake build Effect4.Laws.Program.Typed.Denotation
  Effect4.Laws.Program.Typed.Assembly` exit 0 (389 jobs; `M3bAssembly` 3 open, 1 proved, 4
  total); the typed cone (Membership's reverse cone) exit 0, 590 jobs, no `sorryAx`.

## Group 2: bind, select and the scoped shapes (commit `82110a5c`)

- **The induction's interface** (`Typed/Denotation.lean`): `ChildDenotes root f c path`, the
  induction read at one child (every world `J` ranges over, every point with fuel `f` at the
  child's path that the point typing admits); `child_fuel_eq`, `childWith_fuel_eq`. Every arm that
  denotes a child takes the child's `ChildDenotes` as a hypothesis, so the arms do not depend on
  the induction's form; a continuation a guard runs is typed at a later world, so the child is
  used at the world its point is built at, with the point's environment and view moved there
  (`envTyped_mono`, `completed_mono`, `serviceTy_leHost`).
- **Arms** (proved): `bind_arm` (`seqGuard_typed`), `suspend_arm`, `select_arm` (with
  `decide_fits`, the membership form of `Decision.decide_typed`: a tag hit's payload fits the
  payload type by `fits_tagPayload`, a miss is a member of `Ty.diffTag`; `BoundFits`,
  `envTyped_bound`, `childBind_path/env/completed`), `catchCause_arm` (`catchGuard_typed`, the
  caught cause bound at `Cause<E>`: `fits_exitErr_causeOf`), `matchCause_arm` (`allGuard_typed`),
  `onExit_arm` (`onExit_typed`), `scoped_arm`, `gen_arm`, `iterate_arm`, `uninterruptible_arm`,
  `interruptible_arm` (`actionAt` at the mask, `denoteAction_of`), `acquireRelease_arm` (the
  context read then `Body.acquireIn`: `getContext_typed`, `fits_context_inv`), `catchIf_arm`
  (`catchIf_miss_fits`, the membership form of `catchIf_miss_error_admits`, with
  `fitsCause_of_firstErrorValue_none` and `firstErrorValue?_of_caught`; `subN_catchIfError`).
- `denoteR`'s own equation lemmas are the only interface used (`denoteR_bind` …); no proof
  unfolds `denoteRWith`.
- Axioms (tested, scratch `AxG2.lean`, re-run after group 3): 30 theorems, 23 `[propext,
  Quot.sound]`, 5 `[propext]`, 2 none (`childBind_path`, `childBind_completed`).

## Group 3: the fiber rows (commit `5f8cbe18`)

- **A third Membership addition (requested and granted 2026-10-01, same end section, same
  conditions):** `fiberTy_eq_some : fiberTy t = some pair → t = .fiberOf pair.1 pair.2`
  (`Typed/Membership.lean`, end section; `[propext]`). Seven arms read the checker's
  `fiberTy handle = some pair` (awaitFiber in both modes, runIn, interrupt, interruptScoped,
  interruptAll, awaitAll, awaitAllFailFast) and need the handle's shape to read the term's value as
  a fiber; the lemma is the one case analysis on `Ty` they need (row 132).
  `Typing/CheckInversion.lean:32-38` holds the same shape lemma for `listOf?` and `exitOf?`; the
  coordinator keeps the cleanup that moves the three beside each other. No census pin reads the
  file (the traversal census prints the tree's rows and asserts only its fixture; a theorem is no
  row). Membership's direct dependents rebuilt green (`ExitConnector`, `Admission`; the test
  `AdmissionColumns` exit 0).
- **Arms** (proved): `awaitFiber_arm` (a completed target answers from the point's view, typed at
  the fiber's declared type by row 175, `view_exitOk`, `awaitExit_join`, `awaitExit_value`; a
  running target is the await row, whose post is below the handle's columns: `await_fits` for a
  join, `subN_exitOf` for an await by value) and the sixteen actions, dispatched by
  `withFiber_arm`: `fork_arm`, `forkIn_arm`, `forkScoped_arm` (the ambient scope's read,
  `ambientScope_typed`, then `forkIn`), `runIn_arm`, `interrupt_arm`, `interruptScoped_arm`,
  `interruptAll_arm`, `awaitAll_arm`, `awaitAllFailFast_arm`, `snapshotChildren_arm`,
  `awaitNewChildren_arm`, `raceAll_arm`, `setContext_arm`, `getContext_arm`, `getId_arm`,
  `closeScope_arm` (`exitOfVal_of_fits`). `actionAt`'s refusals are excluded by term progress at
  the checker's types (the refusal's pre is `False`); a list of fibers decodes by its two shapes
  (`fibers_of_fits`, `mapM_fibers`, `mapM_fibers_eq`).
- **Raw-order entries.** `fiberPre`'s `awaitAll`, `awaitAllFailFast` and `raceAll` arms compare in
  raw `Ty.sub` (row 137), and the checker's types are joins (normalized), which raw `sub` does not
  place a type below. The certificate is a raw union of the declared columns (the targets' from
  `Γ`, the entrants' checked types): every column is raw-below it (`sub_union_self_left/right`
  through `Ty.OrderProof.sub_iff_members`; `sub_unionFold`), and it lies below the checker's
  columns in `subN` (`subN_union_le` through `sub_normalize_union_le`; `unionFold_subN`,
  `awaitAllCert`, the private `raceEntrants_typed`). The post is then widened to the checker's
  type (`fits_subN` with `subN_listExitOf`; `exitOk_widen`). No pre or post changed.
- **Other changes:** `node_at_child` takes any parent node (an action's child is a program); the
  race's spine rounds are private (`effsRounds`, `Eff.expandIn_raceAll`), since `Effs.expandIn` is
  no definition of the tree.
- Axioms (tested, scratch `AxG3.lean`): 38 theorems, 36 `[propext, Quot.sound]`, 2 `[propext]`
  (`fiberTy_eq_some`, `node_at_child`).
- Builds (tested): `lake build Effect4.Laws.Program.Typed.Membership` exit 0 (364 jobs); `lake
  build Effect4.Laws.Program.Typed.Denotation` exit 0 (373 jobs); `lake build
  Effect4.Laws.Program.Typed.ExitConnector Effect4.Laws.Program.Typed.Admission
  Effect4.Laws.Program.Typed.Assembly` exit 0 (392 jobs); `lake env lean -DwarningAsError=true
  Test/Program/AdmissionColumns.lean` exit 0. Name clash check (tested, `grep -w` over `src` and
  `Test`): only `fiber_of_fits` also names `AwaitLoad`'s own lemma, in its own namespace, which
  name resolution prefers there (assumed, from reading Lean's `resolveGlobalName`: the current
  namespace is searched before open declarations; the coordinator's roots build at the merge
  tests it, since this seat runs none).

## The template bridge in Membership (commit `95a75fed`; requested and granted 2026-10-01)

While writing group 4's host-row arm I found (reading, then sent to the coordinator) that
`bitEntry` reads the row's template while the checker types the node at the row's instance (row
183, below). The coordinator granted option (A): three pure additions to the same end section of
`Typed/Membership.lean`, no existing statement touched, private helpers in the same hunk.

| Lemma | Line | Axioms (tested, scratch `AxBridge.lean`) | What it serves |
| --- | --- | --- | --- |
| `fits_instantiate` | 2799 | `[propext, Quot.sound]` | membership at a `valueVars` template is membership at each instance (a parameter has no member) |
| `valueVars_normalize` | 2974 | `[propext, Quot.sound]` | normalization keeps parameters under value formers (both halves of `Ty.valueVarsAlg`) |
| `valueVars_of_noInternalHandle` | 3041 | `[propext]` | a column `findInternalHandle` passes (a lawful row's answer and error, `rowChecks`) is `valueVars` |

Private helpers (same hunk): `valueVarsAlg_ofMembers`, `valueVarsAlg_members`,
`valueVarsAlg_factors`, `valueVarsAlg_normalizeRow`, `valueVarsAlg_union_normalize`,
`valueVarsAlg_prod_normalize`, `valueVarsAlg_fst_and`, `valueVarsAlg_snd_and`,
`orElse_eq_none_parts`. Build (tested): `lake build Effect4.Laws.Program.Typed.Membership` exit 0
(364 jobs), then `lake build Effect4.Laws.Program.Typed.ExitConnector
Effect4.Laws.Program.Typed.Assembly` exit 0 (392 jobs; log
`scratchpad/d2/build-assembly-head.log`). The three are proved and **not yet read** by any landed
proof: the host-row arm that reads them is owed (group 4).

## Every Membership addition (the brief's file list extended by the coordinator)

All in one end section, `src/Effect4/Laws/Program/Typed/Membership.lean:2706` ("Flat carriers, tag
payloads, fiber handles, templates (granted 2026-10-01, seat D2)"), plus one header line
(`import Effect4.Laws.Program.Signature`, the last import, granted with option (i)):

| Lemma | Line | Granted | Axioms (tested) | Read by |
| --- | --- | --- | --- | --- |
| `fits_flatFits` | 2717 | 2026-10-01, message 3 | `[propext, Quot.sound]` | owed `provideService_arm` |
| `fits_tagPayload` | 2736 | 2026-10-01, message 3 | `[propext, Quot.sound]` | `decide_fits` (`select_arm`) |
| `fiberTy_eq_some` | 2784 | 2026-10-01, message 5 | `[propext]` | the seven fiber arms (group 3) |
| `fits_instantiate` | 2799 | 2026-10-01, message 6 | `[propext, Quot.sound]` | owed `external_arm` |
| `valueVars_normalize` | 2974 | 2026-10-01, message 6 | `[propext, Quot.sound]` | owed `hostRow_valueVars` |
| `valueVars_of_noInternalHandle` | 3041 | 2026-10-01, message 6 | `[propext]` | owed `hostRow_valueVars` |

Cone cost (tested with `scratchpad/d2/tools/fwd.py` at group 1): Membership's import cone grew from
174 to 180 modules by the Signature import. No census count reads the file (the traversal census
prints the tree's definitions and asserts only its fixture; a theorem is no row; reading).
Proposed cleanups for the coordinator's list (not this seat's change): `flatCarrier` is a predicate
on `Ty`, so its home is beside `Ty`, with `Signature.lean` importing it from there; and
`fiberTy_eq_some` beside `CheckInversion.lean:32-38`'s `listOf?_eq_some` and `exitOf?_eq_some`.

## The arms proved, with file and line (`src/Effect4/Laws/Program/Typed/Denotation.lean`)

Every arm is proved (kernel, `lake env lean -DwarningAsError=true`, then `lake build`), each at
`[propext, Quot.sound]` or below (tested: scratch `AxG1.lean`, `AxG2.lean`, `AxG3.lean`). An arm
reads its children only through `ChildDenotes root f c path` (`:826`), the induction at one child.

| Node | Arm | Line |
| --- | --- | --- |
| no fuel | `denoteR_zero_typed` | 739 |
| `succeed`, `fail`, `failCause`, `sync`, `yieldNow` | `succeed_arm`, `fail_arm`, `failCause_arm`, `sync_arm`, `yieldNow_arm` | 745, 757, 775, 786, 800 |
| `bind`, `suspend`, `select` | `bind_arm`, `suspend_arm`, `select_arm` | 846, 976, 992 |
| `catchCause`, `matchCause`, `onExit`, `catchIf` | `catchCause_arm`, `matchCause_arm`, `onExit_arm`, `catchIf_arm` | 1083, 1105, 1137, 1372 |
| `scoped`, `gen`, `iterate` | `scoped_arm`, `gen_arm`, `iterate_arm` | 1158, 1172, 1182 |
| `uninterruptible`, `interruptible`, `acquireRelease` | `uninterruptible_arm`, `interruptible_arm`, `acquireRelease_arm` | 1198, 1216, 1235 |
| `awaitFiber` (both modes) | `awaitFiber_arm` | 1657 |
| `withFiber` (16 actions) | `withFiber_arm` (dispatch) over `fork_arm` 1714, `forkIn_arm` 1734, `forkScoped_arm` 1761, `runIn_arm` 1788, `interrupt_arm` 1814, `interruptScoped_arm` 1835, `interruptAll_arm` 1858, `awaitAll_arm` 1916, `awaitAllFailFast_arm` 1952, `snapshotChildren_arm` 1989, `awaitNewChildren_arm` 2006, `raceAll_arm` 2038, `setContext_arm` 2064, `getContext_arm` 2083, `getId_arm` 2097, `closeScope_arm` 2115 | 2137 |

Tools (proved; same file): the expansion's rounds commute with the constructors
(`Eff.expandIn_bind` … `:114-188`, the race's spine privately at `:93-108`, `:194`); `pointTyped_child`
(`:261`), `node_at_child` (any parent, `:241`), `serviceTy_leHost` (`:248`), `completed_mono`
(`:253`); term progress at a world's allocation table (`atom_progress` `:373`, `evalTerm_progress`
`:517`, `evalTerm_progress_env` `:573`, `causeOf_progress` `:603`); `decide_fits` (`:881`, the
membership form of `Decision.decide_typed`); `catchIf_miss_fits` (`:1308`); the fiber helpers
(`fiber_of_fits` `:1422`, `view_exitOk` `:1454`, `subN_exitOf` `:1466`, `fibers_of_fits` `:1572`,
`exitOfVal_of_fits` `:1599`); the raw-union certificate (`sub_union_self_left/right` `:1486-1490`,
`subN_union_le` `:1496`, `sub_unionFold` `:1501`, `unionFold_subN` `:1512`, `awaitAllCert` `:1522`,
the private `raceEntrants_typed` `:1617`). In `Typed/Seq.lean`: `guardBind_typed` (`:89`) and its
shapes `seqGuard_typed` (`:105`), `catchGuard_typed` (`:121`), `allGuard_typed` (`:137`);
`exitOk_widen` (`:79`), `typedProg_widen` (`:160`), `finalizer_typed` (`:200`), `onExit_typed`
(`:217`); `seq_typed` (`:150`) re-proved as `seqGuard_typed`'s instance, statement unchanged.

## What is owed, with the exact obstacles (stopped by the owner, 2026-10-01)

The owner's instruction (relayed by the coordinator): no new steps; commit what builds; describe
the rest. Nothing below is in the tree.

**Group 4 (store rows, services, `exit`): owed, no obstacle found by reading.** A draft (not
compiled, not evidence, outside the tree in the session scratchpad, `scratchpad/d2/group4.lean`)
has these statements; each is a proof plan, not a claim:
- `fits_refTy_inv`, `fits_deferredTy_inv` (a member of the native cell/deferred type is a declared
  cell/deferred; case analysis on the value and the handle kind only), `refRead_nat`;
  `syncRow_typed root req (hk : NativeOp.kind op = .sync) (hfit : Fits w v (NativeOp.row op).request)
  : ∃ o, NativeOp.syncOpOf op v = some o ∧ TypedProg root w ⟨(row op).answer, (row op).error, req⟩
  (.vis (.inl o) fun v => .pure (.success v))`, one case per sync row (the certificates: `nat` for
  `refMake`, `(nat, nat)` for `deferredMake`, `()` elsewhere; reads through `Equiv`'s two halves);
  `nativeRowOf_builtin`, `builtinPerform_inv` (`rowTy_closed_some`, `NativeOp.row_closed`),
  `syncPerform_arm` (`denoteR_perform_sync`, widened by `subN_normalize_right` twice);
  `deferredAwait_arm` (certificate the deferred's declared columns, `asyncPre` by reflexivity);
  `sleep_arm` (no time: the yield; a positive time: the timer at `(unit, never)`).
- the host row: `exitOk_instantiate` (from `fits_instantiate`), `hostRow_valueVars` (from
  `LawfulSig.rows` at `rowChecks`' indices 7 and 8, `valueVars_of_noInternalHandle`,
  `valueVars_normalize`), `external_arm` (certificate the row's template columns, `bitEntry` by
  reflexivity; the continuation typed at the instance), `perform_arm` (dispatch).
- `serviceTy_flat` (a lawful signature's carriers are flat: the reserved `Scope` carrier, a
  declaration's `serviceChecks` index 1, a built-in code by `decide`), `servicesFit_mono` (from
  `servicesFit_map`), `setContext_typed`, `service_arm` (`ServicesFit` and the tie; a missing key
  is `missingService`, which part one admits), `provideService_arm` (`updateContextR`: the context
  read, the set context whose new binding fits by `fits_flatFits` and
  `Env.Context.getV_addV_same/other`, then `onExit_typed` with the restoring set).
- `inlineYield_typed` (by induction on fuel: `succeed`/`fail`/`failCause` by progress; `perform`
  never inlines at a checked node, by progress at every row kind; `awaitFiber` from the view as in
  `awaitFiber_arm`; `exit` by the induction; `provideService` never inlines, by progress) and
  `exit_arm` (`allGuard_typed`; the inline case by `inlineYield_typed`).

**Group 5 (the layer family, `provideLayer`): owed; obstacle row 176 (by reading; the memo-hit
refutation was not finished).** `provideLayerR` (`DenoteR.lean:526-555`) reads the build's answer
with `Env.decode`, whose `none` branch is `badShapeExit`; a build answers a services spine
(`Env.encode`, constructor 5: `denoteLayer_succeed`, `bindServiceR`, `addCurrentMemoMapR`,
`combineWithR`, `mergeContextsR`), which fits no `Ty` but `unknown`; the memo rows declare a built
context at `Ty.context` (`storePost`'s `memoGet` arm, `Residual.lean:104-105`), whose members are
fiber-context images (`fits_context_inv`), which `Env.decode` refuses. The planned control
(`E4-TYPED-CE-023`, not seeded): `.provideLayer (.effect K (.succeed (.lit (.nat 7)))) false U` at a
world whose memo deferred is declared at `(Ty.context, never)`; the memo hit's await answers a
`Val.context` at `Ty.context`, and `addCurrentMemoMapR`'s `Env.decode` of it is `none`, so a typed
point denotes `badShapeExit`. A second obstacle by reading: `BodyTyped.layerBuild` needs
`PointTyped` at a layer node, but `PointTyped` demands an `.eff` node (`Node.at_ … = some (.eff e)`),
so the merge forks' `Body.layerBuild` pre is unsatisfiable (`mergeTwoR`, `mergeAllR`).

**Group 6 (the assembly): owed; no obstacle beyond group 5.** `denoteR_typed` by induction on fuel:
zero by `denoteR_zero_typed`; at `f + 1`, cases on the node, each arm above with every
`ChildDenotes` discharged by the induction hypothesis at `f`. Planned landing while the layer
family is open: `denotesTyped_of_provideLayer : ProvideLayerArm root → DenotesTyped root` and the
named open goal `M3bAssembly.denoteR_typed_provideLayer` (proved arms listed in its docstring); M5
for layer-free programs (`Eff.layerPaths [] = []`); `evalTerm_fits` closed by the adapter `fun table
_ _ _ _ _ _ hty henv hev => evalTerm_fits_native table henv hty hev` (the statement matches
`TermFits` up to the order of the `termTy` and `EnvTyped` premises; reading). The battery's controls
that wait on it: the typed corpus at a starting world, `AwaitLoad.loadsTyped` and ScopePresence's
controls as one-line corollaries, CE-021/022's flips to `DenotesTyped awaitSrc`/`serviceSrc`, and
the first `LoadsTyped` of a program with a layer reference through D1's lemma.

## The ledger, before and after

Tested (the `#typed_state_obligations` reports printed by `lake build
Effect4.Laws.Program.Typed.Assembly`): at the base and at head `95a75fed` alike, `M3bAssembly` 3
open, 1 proved, 4 total (ceiling 3; `denoteR_typed`, `evalTerm_fits`, `typedState_load` open,
`capture_lookup` proved with its new view premise); `M3bAdequacy` 2 open, 72 proved, 74 total;
`M6Ledger` 20 open, 20 total; `M6Edits` 6 open, 7 proved, 13 total; `M7` 4 open, 4 total. This seat
closed no ledger line and opened none; the eighteen-command ledger is untouched. The whole tree's
count was not measured here (no roots build, by the coordinator's instruction); main's count after
D3's merge is D3's (21 open of 484, main's log at `7d50cfe6`; reading).

## Decisions rows: proposed text

**Row 170 (landed on this branch).** "M5's denotation lemma takes the reference-formation premise:
`DenotesTyped root := root.program.layerRefsWF = true → …` (`Typed/Assembly.lean:889`), discharged
at the load from the checker's verdict by `layerRefsWF_of_typeOf` (`:998`); the premise never enters
`ProgramSource`. Refutation of the old statement `old_chain_refuted : ¬ OldDenotesTyped chainSrc`
(`Test/Program/TypedDenotation.lean:200`; with `chain_not_wf`, `chain_refused`, `chain_point`,
`chain_build`); repair `chain_denotes : DenotesTyped chainSrc` (`:240`). Landed `55be93a6` (seat
D2)."

**Row 175 (landed on this branch).** "`PointTyped` carries the completed view: its fourth conjunct
`∀ q ∈ point.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2`
(`Typed/Admission.lean:136-141`), the `construction` post's clause, monotone (`pointTyped_mono`);
`DenotesTyped` ranges over worlds whose service table is the source's (`w.serviceTy =
root.sig.serviceTy`, spelled as `MachineTyped.services` spells it); `machineTyped_load`'s `code` is
read at the initial world only. Refutations: `old_view_refuted : ¬ Row170DenotesTyped awaitSrc`
(`TypedDenotation.lean:295`) and `old_table_refuted : ¬ Row170DenotesTyped serviceSrc` (`:360`);
repairs: `view_point_refused` (`:305`, the witness point is typed at no type) and
`table_world_excluded` (`:371`, the witness world is outside the range). Landed `55be93a6`."

**Row 176 (open; measured by reading only).** "A layer build answers a services spine
(`Env.encode`) while the memo rows declare a built context at `Ty.context`, whose members are
fiber-context images that `Env.decode` refuses, so `provideLayer` and every `denoteLayer` arm have no
`TypedProg` derivation under the current `Fits` and posts (reading; `E4-TYPED-CE-023` planned through
the memo-hit path, not seeded). Options: (a) a services-spine arm in `Fits` at the memo row's
declared type (or a new carrier for spines): moves `Fits`' context arm (Membership), the `memoGet` and
`memoBuild` posts, every reader of `Ty.context` membership (`fits_context_inv` and its users), and
gives `Ty.context` two images; `Env.decode` and the OCaml face unchanged. (b) builds answer the
fiber-context image (`Val.context`, `ctxImage`): moves `bindServiceR`, `addCurrentMemoMapR`,
`combineWithR`, `mergeContextsR`, `provideLayerR`'s read (to `Val.context?`), their `Compile.lean`
twins and the `DenoteR`/`Compile` agreement proofs, and the faces that encode a built context; the
posts stay. Recommended: (b), one type with one image (a built context is a context's services; the
coherence principle's one representation per sort), at the cost of the layer protocol's six
helpers and their agreement proofs. Independently of (a)/(b), `BodyTyped.layerBuild` needs a
point typing at a layer node (today `PointTyped` demands an `.eff` node), else the merge forks stay
untypable."

**Row 183 (open; my refinement of the coordinator's text, with the control owed).** "The checker
types `perform (.external i) r` at the row's instance at the request (`rowTy`), but `asyncPre`'s
external arm (`bitEntry`) demands the certificate raw-above the template columns; raw `sub` never
places `var i` below a closed type, so a certificate that types the program is the template itself
(or holds `unknown`, whose post gives only `Live`). At the template, a host success is admitted
only if its value occupies no parameter's position. Correction to the row's example: `A → A` is no
lawful row (`rowChecks`' `admitColumn` refuses a request or answer column `var 0`, which has no
member); a lawful witness is a row with request `List<A>` and answer `Option<A>`, where the template
certificate admits the success `none` and refuses `some 1`, which the instance `Option<number>`
admits (`CompletionStrong`/`AnswerOk`, reading; control owed). Repair, recommended: `bitEntry`
reads the row's instance at the request (∃ request type and match, the instance's columns below the
certificate), so the certificate is the checked type, M5's host-row arm needs no bridge, and a host
answer at a template row is admissible by membership. Proofs it reopens (reading, `git grep` at
`f4881f74`): `bitEntry` and `bitEntry_rows_append`, `asyncPre_mono`, `asyncPre_rows_append`
(`Typed/Residual.lean:628-803`), `Test/Program/TypedProgRows.lean`'s row-116 battery (its iff
statements pin `bitEntry`'s shape), and the host-answer side that reads the token's certificate
(`AnswerOk`, M6c/M7). Estimate: half a day for a seat; the bridge lemmas of `95a75fed` stay correct
either way."

**Row 148 (status line).** "M5's denotation lemma, in progress: statement repaired (rows 170, 175);
groups 1–3 of the arms proved on `seat/D2` (`Typed/Denotation.lean`); groups 4–6 and the layer
family owed (row 176); `denoteR_typed` open."

## Register lines (proposed; the register is the coordinator's)

- `E4-TYPED-CE-020`: REPAIRED by row 170 on `seat/D2` (`55be93a6`): history
  `old_chain_refuted` (proved, `Test/Program/TypedDenotation.lean:200`), repair `chain_denotes`
  (`:240`); the coordinator's seed line reads "reading, not compiled", which is now proved.
- `E4-TYPED-CE-021`: REPAIRED by row 175 (`55be93a6`): `old_view_refuted` (`:295`), repair
  `view_point_refused` (`:305`).
- `E4-TYPED-CE-022`: REPAIRED by row 175 (`55be93a6`): `old_table_refuted` (`:360`), repair
  `table_world_excluded` (`:371`).
- `E4-TYPED-CE-023`: not seeded (the memo-hit refutation was stopped before it compiled).

## Merge notes against main's head `f4881f74`

- Textual: `git merge-tree --write-tree --name-only f4881f74 HEAD` printed only a tree id, no
  conflict (tested, at head `95a75fed`). Main changed `Typed/Assembly.lean` since the base (D3's
  ledger lines moved to `Typed/Commands/*.lean` and `Edits.lean`; `QueueOk.links` reads
  `Stores.ScopeLive`), `World.lean` (`ScopeLive` restated through `Stores.ScopeLive`) and
  `Scheduler.lean`; none of those hunks overlaps this branch's (reading the diff).
- Semantic, for the D4 merge first: the statements this branch changes are `PointTyped`
  (`Admission.lean:136`), `DenotesTyped` (`Assembly.lean:889`), `machineTyped_load` (`:928`),
  `typedState_load_of_code` (`:988`, statement unchanged, passes `code _`),
  `loadsTyped_of_denotesTyped` (`:1013`), `capture_lookup` and `M3bAssembly.capture_lookup`
  (`:823`, `:1472`, the new `hview`), and `pointTyped_mono`/`pointTyped_rows_append`
  (`Residual.lean:571`, `:767`). `envTyped_nil` and `envTyped_append` moved from `Assembly.lean` to
  `Denotation.lean` (same names, one copy), and `Assembly.lean` imports `Typed.Denotation` last.
  `git grep` at `f4881f74` finds no `src` site outside these three files that builds a
  `PointTyped`; D3's command modules do not construct one (reading).
- Every site that builds a `PointTyped` and its one-line discharge is the table under "The statement
  repairs" above.
- `Test/All.lean`: one line, `import Test.Program.TypedDenotation`, right after
  `import Test.Program.H2PartOne`.
- `ScopeLive`'s restatement on main is definitional (`w.state.ScopeLive sc` unfolds to the old
  body); this branch reads it only through lemmas (`fits_scope_inv`, `scopeLive_mono`) and the
  battery's `w0_live` (by `decide +kernel`, whose `Decidable` instance main restated through
  `Stores.ScopeLive`); not built against main here.

## Builds run by this seat (all narrow; tested)

`lake build` of: `Effect4.Laws.Program.Typed.Assembly` and the typed cone at each commit (logs in
`scratchpad/d2/`), `Effect4.Laws.Program.Typed.Membership` (364 jobs) after each Membership
addition, `Effect4.Laws.Program.Typed.Denotation` (373 jobs), `Effect4.Laws.Program.Typed.ExitConnector
Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Typed.Assembly` (392 jobs, group 3),
`Effect4.Laws.Program.Typed.ExitConnector Effect4.Laws.Program.Typed.Assembly` (392 jobs, head);
`lake env lean -DwarningAsError=true` on `Test/Program/TypedDenotation.lean` (exit 0, 36 axiom lines)
and `Test/Program/AdmissionColumns.lean` (exit 0). Not run: the roots build (`lake build
Effect4.Laws Test.All`), `make check`, any generator (the coordinator's instruction). Bounded or
host-only evidence: none; every claim marked proved is a kernel theorem compiled here.

## Permissions, deviations, rules

- No permission was refused. Permissions asked and granted (coordinator, 2026-10-01): the
  Membership end section (`fits_flatFits`, `fits_tagPayload`), the Signature import, `fiberTy_eq_some`,
  the three template-bridge lemmas.
- One deviation, early in the seat: I wrote one temporary file to `/tmp/x.txt` instead of the
  scratchpad, and deleted it at once; every later scratch file is in the session scratchpad.
- Rules kept (reading the diff): no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`,
  `extern`, `implemented_by`; no `simp_all`, `first`, `try` in any landed proof under `src/`; every
  hand `simp` is `simp only`; no case analysis on `Ty` outside `Membership.lean`; commits by explicit
  paths on `seat/D2`; no `git merge`, `checkout`, `reset` or `push`; nothing in the main checkout
  touched; `README.md`, `AGENTS.md`, `docs/core/decisions.md`, `docs/STATE.md`,
  `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md`, `lakefile.toml`, D3's files and the
  `M6Ledger`/`M6Edits`/`M7` lines untouched.
