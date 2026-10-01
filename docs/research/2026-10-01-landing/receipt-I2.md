# Seat I2 receipt: seat A integrated on seat I's union (and step 10, row 156)

Seat I2 of the 2026-10-01 landing. Brief: `docs/research/2026-10-01-landing/brief-I2.md` (main
checkout, read-only here) with its "Amendments" section (base named; step 10, decisions row 156);
plan: `plan.md` (§4 rules, §5 measure). Worktree `/Users/pooks/Dev/lean4-effect4-seat-I2`, branch
`seat/I2`. Evidence words: **proved** (a kernel theorem compiled here, axioms printed),
**reproduced** (another seat's or Codex's proved fact compiled again here), **tested** (a finite
check run here: a build's report, a `#guard`, a `grep`), **assumed** (not run here; a reading names
the lines read).

## The one thing first

**Before merging: shared shapes changed, so a branch in flight that builds these by hand needs
an argument or a field.** Step 10 (row 156): `TypedProg.scopeExit` takes `live : ScopeLive w sc`
first; `StoreTyped` has a fifth field `memo : w.state.MemoValid` (re-established by
`syncOpStep_memoValid … store.memo step`, whose premise is now the memo clause it always read: 12
lines in `Machine/StoresLaws.lean`, the one repair outside the brief's list, measured below);
`HandleFits`' scope arm is `target = Ty.scopeTarget ∧ ScopeLive w index` (a split there reads
`.1`) and `handleFits_map`, `flatFits_map`, `servicesFit_map`, `fits_map` take the scope transport
`hscope` before `hsvc`; the five scope-handle posts are `Fits w' ans Ty.scope` (read back with
`fits_scope_inv`, built with `fits_scopeHandle`); `MachineLive` lost `ambientScopes` (now the
theorem `ambientScope_live`, from `J`) and `machineLive_of_quiet` its contexts premise. Steps 4–7:
`MachineTyped` has a second field `services`; `initialWorld` takes the service table (default
unchanged); the M5–M7 premises read `typeOfProgram root.signature`; `asyncPre`'s external arm is
`bitEntry`; `AdmitRefusal` has `emptyColumn` and `AdmittedProgram` two more fields. A trial merge
with the integration branch head `bff50631` (`git merge-tree --write-tree refactor/phase1-phase3
HEAD`, run in this worktree) is clean; of the 14 compiled `.lean` files changed there since the
merge base (`160012dc`), none mentions any of these names, `Test/All.lean`'s one hit being an
import line (tested by `grep`; the other changes there in `Machine/Fibers.lean` and
`Machine/Stores.lean` are comment edits, read).

What landed (all proved, `[propext, Quot.sound]` or less; final `LEAN_NUM_THREADS=6 lake build
Effect4.Laws Test.All` green with both gates): steps 1–9 integrate seat A on seat I's union
(rows 111–116, 127, 137, 149; D-A1 (a) wired with the generated group regenerated in the fixed
order; the six `f.total` store rows and TY-08's promise half proved); step 10 lands row 156:
`ScopeLive` is the one predicate for a scope's presence, read by membership, the five posts that
answer a scope handle, the protocols' scope arms and the `scopeExit` constructor. Codex's
checked source `forkAfterMake` now has a `TypedProg` derivation at every world and
`DenotesTyped` holds at its root point (`ScopePresence.forkAfterMake_denotes`), so
`E4-TYPED-CE-018` is repaired; `M6Ledger.step_deliver` is no longer refuted by the absent-scope
witness (`M6Capstone.H1HaltAmendment.input_refused`) and stays open. Ledger: 37 open / 447
proved / 484 (seat I's: 43 / 441 / 484).

## Base and head

Base: `a6ec2a28` (seat I's head `160012dc` with `seat/A` at `c3f3df14` merged textually by the
coordinator). Head: the commit that adds this receipt, on `f98edd9e` (the last code commit).
Commits, one per step: `9eaee09c` (1), `b6e165d4` (2), `a3d983fd` (3), `5f742b85` (4),
`27896d8c` (5), `d5f6a0fe` (6), `0b432dac` (7), `c9866f74` (8), `8be71278` (10.1), `ed90205b`
(10.2), `b8723557` (10.3), `c69ec57c` (10.4), `9cbdd085` (10.5), `f98edd9e` (10.6); step 9 and
10.7 are builds. Nothing pushed; no `git merge`, `checkout`, `reset` or `push` was run; no
permission was refused.

## Work log (incremental, as written during the work)

- Read in full: `brief-I2.md` with its amendments (main checkout), `plan.md`, `receipt-A.md`,
  `receipt-I.md`, `receipt-C.md` (all sections; "Lines for seat A" in particular), Codex's
  `codex-second-eyes/review.md`, `ScopeAllocationPost.lean`, `scope-allocation-post.log` (main
  checkout), `AGENTS.md`.
- Step 1 (`9eaee09c`): receipt A's hunks 1–6, 8 applied by text. `Adequacy.lean`: seat B's
  `completionOk_of_fitsExit` (at `Requirement.empty`) and `fits_nat_val`/`fits_unit_val` deleted
  (seat A's `Membership.lean` copies, at any requirement, are the one home); seven
  `fits_unit_val hv` → `fits_unit_inv hv`, `nat_cell`'s `fits_nat_val (fits_sub …)` →
  `fits_nat_inv (fits_subN …)`, two `fits_sub w equiv.2 _ trivial` → `fits_subN …`, `, rfl` at the
  three world-order constructions (`:93`, `:262`, `:326` after the deletions). `Residual.lean`:
  `deferredCompleteWith`'s reference arm in `Ty.subN` (`:56`), `servicesFit_map … (serviceTy_of_le
  ord.1) h` (`:644`). `FramesNotKripke.lean`: `, rfl` at `:86`, `:687`. `TypedProgRows.lean:183`:
  the `forkIn` arm is `⟨pointTyped_rows_append … h.1, h.2⟩` (seat I's row-139 hunk made that pre
  a conjunction; receipt A, written before it, expected no edit). Hunk 7 (FitsOrder's local
  `fiber_inv`) is applied in step 2's commit: that battery reads H1's `CodeInert` and only builds
  after step 2's restatement. Hunk 9: no edit (the `Ty.sub_refl _` sites build: `Residual`,
  `FramesNotKripke`, `H2PartOne`, `TrivialPosts`; `M6Capstone` in step 2's build).
  Builds (tested): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly
  Effect4.Laws.Program.Typed.Seq` exit 0, 385 jobs, 1 min 37 s (seat A's cone compiled here first);
  `LEAN_NUM_THREADS=4 lake build Test.Program.FramesNotKripke Test.Program.TypedProgRows
  Test.Counterexamples.Machine.Semantics.AsyncHookContract
  Test.Counterexamples.Machine.Semantics.TrivialPosts Test.Program.TypedResidual` exit 0, 394 jobs;
  `grep -c 'sorryAx\|Classical.choice'` on both logs: 0. Ledger lines printed by the first build:
  `M3bAdequacy` 8 open / 66 proved / 74, `M4Stack` 0/4/4, `M5Hooks` 0/1/1, `M3bAssembly` 3/1/4,
  `M6Ledger` 20/0/20, `M7` 4/0/4, `M6Edits` 6/7/13, `M3bWorld` 0/6/6.
- Step 2 (`b6e165d4`): seat A's statements over seat C's split.
  - `Assembly.lean:924` **`typedState_load_of_code`** (new, receipt C's wording: `closed`,
    `noMarker`, `code` give `∃ w, TypedState root ty w (loadR …)`), proved as the projection
    `(machineTyped_load …).typed`, `[propext, Quot.sound]`. `ValueMembership.typedStateF_load`
    (`:993`) is now a one-line use of it (statement unchanged; seat A's 45-line second copy of
    `machineTyped_load`'s generated-part argument is gone); its instances `typedStateF_load_ref`,
    `_get` unchanged. `TypedSplit.lean` prints its axioms (that battery prints every `Assembly`
    theorem).
  - `FitsOrder.lean`: `m5_forces_leaf` (`:304`) over `∃ w, MachineTyped …` (reads the loaded root's
    code through `J`'s `LiveCode` at `rfl rfl rfl`); `prog3_loads_typed` (`:499`) is now
    `∃ w, MachineTyped src rootTy3 w (loadR prog3 100 100)` through `machineTyped_load` (strengthened
    from `TypedState`, as the brief asks); new flips `loadsTyped` (`:503`, M5's `LoadsTyped`) and
    `capstone_at_load` (`:508`, `ReachableTyped` at the load); `prog3_leaf` (`:512`) unchanged.
    History under `RawLeaf`: `Reviewed.m5_false` (`:388`, over `J`), `Reviewed.loadsTyped_false`
    (`:394`, new), `Reviewed.typedState_load_false` (`:398`, over `∀ …, LoadsTyped …`),
    `capstone_implies_load` (`:408`, `ReachableTyped` → `LoadsTyped`), `Reviewed.capstone_false`
    (`:416`, over `∀ …, ReachableTyped …`). Hunk 7: the local `fiber_inv` is deleted, the four sites
    call `TypedProg.fiber_inv`. The local `replayR_nil_machine`, `rreachable_load` are deleted (seat
    C's in `Assembly.lean` are the same statements). `load_not_inert` (`:288`) is kept as history over
    `H1Shapes.CodeInert` (H1's clause left `src/` at row 134). The import of `ValueMembership` is
    replaced by `H1Shapes`. The two `#guard_msgs (error)` fixtures are unchanged and pass.
  - `RawOrderLoad.lean` (seat C's `E4-TYPED-CE-009` over `J`): seat A's `Fits` makes its three
    refutations false (its `leaf_false` stopped elaborating: `Ty.subN` against `Ty.sub`). Kept as
    history under `FitsOrder.RawLeaf`, each a one-line use of FitsOrder's `Reviewed` theorem
    (`m5_false` `:33`, `loadsTyped_false` `:37`, `capstone_false` `:41`); its copies of the program,
    `fiber_inv` and `leaf_false` are deleted (the last is `FitsOrder.Reviewed.leaf_false` over the
    pre-137 judgment, and FitsOrder's fixture pins the same script failing against the production
    judgment). This removes `RawOrderLoad.fiber_inv`, one of the four consumers row 156 lists for
    the `scopeExit` constructor.
  - `AwaitLoad.await_typed` (`:234`): the await arm reads `FiberDeclared` in `Ty.subN` (seat A), so
    `fits_sub … (sub_exitOf_mono …)` became `fits_subN w'' below ans fits` with
    `below : Ty.subN (.exitOf fty.answer fty.error) rootTy.answer = true := sub_exitOf_mono _ _ _ _ ha he`
    (`normalize` keeps `exitOf`). Statement unchanged.
  - `Assembly.lean`'s capstone docstring (`M6Ledger.typedState_reachable`): CE-009 repaired
    (FitsOrder's flips, history), CE-018 (registered from Codex's review) named open under row 156.
  Builds (tested): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` and its 12
  Test importers: first run failed at `AwaitLoad.lean:271` (above) and `RawOrderLoad` (`loadR` not
  opened); after the repairs `LEAN_NUM_THREADS=4 lake build …AwaitLoad …RawOrderLoad
  Test.Program.TermFits Test.Program.SignatureControls Test.Program.AdmissionColumns
  Test.Audit.TypedStateDecl Test.Program.LoadedAdmission Test.Program.TypedWorldValidity` exit 0,
  420 jobs (seat A's batteries and dependents build on the union); 0 `sorryAx`/`Classical.choice`
  in that log; every axiom line of `FitsOrder`, `RawOrderLoad`, `AwaitLoad` at `[propext,
  Quot.sound]` or less (84 lines; `child_at` `[propext]`).
- Step 3 (`a3d983fd`): `CompletionStrong.ofRefGet` (`Assembly.lean:89`), `FiberColumnsBelow`
  (`Scheduler.lean:56`), `RacePayload.live` (`:69`), `RacePayload.programs` (`:71`): the inline
  `x.normalize.sub y.normalize = true` → `Ty.subN x y = true` (definitionally equal; seat A's name).
  No other inline form left under `src/` or `Test/` (tested: `grep -rn "normalize.sub"`, no hit).
  Build (tested): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` and its 12
  Test importers, exit 0, 399 jobs (Scheduler, Assembly and the 13 dependents rebuilt), 0
  `sorryAx`/`Classical.choice`.
- Step 4 (`5f742b85`): row 112's tie.
  - `MachineTyped` (`Assembly.lean:268`) gains the field `services : w.serviceTy =
    root.sig.serviceTy`, second, beside the typed state (whose first conjunct is `WorldValid`).
    The world order fixes the table (`le_serviceTy`), so the tie, once at the load, holds along
    every run. `ServicesFit` already reads `w.serviceTy` (seat A); no change.
  - `initialWorld` (`Validity.lean:45`) takes the static service table, default `nativeServiceTy`
    (so every `initialWorld rootTy` in the tree is unchanged, and the default is every
    service-free source's table by `SigApp.serviceTy_nil`, `rfl`). `initial_world_valid_at`
    (`:168`, new, the old proof at every table) and `initial_world_valid` (`:218`, statement
    unchanged, now its instance; its `M2Validity` ledger line unchanged, 0 open / 15 proved).
  - `machineTyped_load` (`Assembly.lean:869`): the world in its statement is now
    `initialWorld rootTy root.sig.serviceTy`, the tie by `rfl`. Callers that named the world
    (`loadsTyped_of_denotesTyped`, `AwaitLoad.loadsTyped`) now write `⟨_, …⟩`.
    `machineTyped_congr`, `storeTyped_of_typedState`: the new field passed through / skipped.
  - `LawfulSource` (`Assembly.lean:810`): body `Table.lawful root.table = true` → `LawfulSig
    root.sig`, the proposition seat A's field `ProgramSource.lawful` carries (rows 111, 114), so
    every source has it; the name and every statement's premise are kept.
    **`LawfulSig.tableLawful`** (`Signature.lean:1125`, new, proved `[propext, Quot.sound]`): a
    lawful signature's rows satisfy `Table.lawful`, so the new body contains the old one; with the
    field, M5's and the capstone's propositions are equivalent to their old forms at every source.
  - Batteries: the premise is discharged by the source's field (`src.lawful`,
    `(awaitProg : ProgramSource).lawful`) where `rfl` proved `Table.lawful []`
    (`FitsOrder.Reviewed.loadsTyped_false`, `RawOrderLoad.capstone_false`,
    `AwaitLoad.loadsTyped_false`, `capstone_false`); `AwaitLoad.OldMachineTyped` gains the same
    `services` field (its docstring says its other clauses are the current ones); the six `J`
    constructions take the tie by `rfl` (the commit message says five; six is the count) (`StaleCode.machineTyped_of_quiet`,
    `M6Capstone.machine_typed`, `H1TerminalAmendment.result_config_typed`,
    `H1HaltAmendment.config_input`, `FramesNotKripke.good_config`, `afterGood_config`).
  Builds (tested): `lake build Effect4.Laws.Program.Typed.Assembly` exit 0 (Validity, Signature
  and the typed chain rebuilt, 384 jobs); the 3 other src dependents and the 37 Test modules of
  the typed-state cone in one call: failed only at the six `J` constructions above (M6Capstone,
  FramesNotKripke); after them, exit 0 (387 jobs), and the whole set again exit 0 (457 jobs, all
  current). Axioms: `initial_world_valid_at`, `initial_world_valid`, `LawfulSig.tableLawful`,
  `machineTyped_load`, `machineTyped_congr`, `storeTyped_of_typedState`,
  `typedState_load_of_code` all `[propext, Quot.sound]` (printed in `TypedWorldValidity`,
  `SignatureControls`, `TypedSplit`).
- Step 5 (`27896d8c`, one commit): the joint switch to the source's signature.
  `PointTyped` (`Typed/Admission.lean:118`), `CaptureTyped` (`Assembly.lean:95`, both checker
  calls), `storePre`'s `memoGet` (`Residual.lean:66`) and `asyncPre`'s external arm (`:138`) read
  `src.signature` / `root.signature` for `nativeSignature src.table`. The ledger's premise is
  `Program.typeOfProgram root.signature root.program = some rootTy` in `LoadsTyped` (M5),
  `ReachableTyped` (M6c), and, since M7 consumes them, `M7Fragment.checked` and
  `ExitHandlesValid`; `loadsTyped_of_denotesTyped` reads it with `effTy root.signature`.
  `capture_lookup` re-checks unchanged (`[propext, Quot.sound]`), as do `fiberPre_mono`,
  `storePre_mono`, `asyncPre_mono` and every battery of the cone except one: seat A's
  `TypedProgRows` transport read `htab` against the old `nativeSignature src.table`; it now also
  keeps the service declarations (`hsvc : src'.services = src.services`, a section variable) and
  reads the extension through `SigApp.rows_append` (`signature_rows_append`, new, `:134`). For a
  source with no declarations every switched form equals the old one by `rfl`
  (`SigApp.signature_nil`), which is why the tree's sources needed no edit.
  Builds (tested): `lake build Effect4.Laws.Program.Typed.Assembly …Seq …ForkSource
  …ExitConnector` exit 0 (Admission, Residual, Seq, Adequacy, Stack, Scheduler, Assembly rebuilt);
  the 40-module cone (`cone.txt` in the scratchpad: the three src dependents and 37 Test modules)
  failed only at `TypedProgRows.lean:135`, `:159` (the transport), then exit 0 (457 jobs); 0
  `sorryAx`/`Classical.choice` outside the failed run's `TypedProgRows` lines.
- Step 6 (`d5f6a0fe`): row 116's domain bit.
  - `Residual.lean:130` **`bitEntry`** (def, now in `src`): `root.signature.dom op = true ∧` the
    row's answer and error columns below the certificate (receipt A's `bitEntry`, read through the
    source's signature after step 5; `dom`/`rowOf` are `nativeSignature root.table`'s). `asyncPre`'s
    external arm is `bitEntry root op cert`; `asyncPre_mono` unchanged (the arm reads no world).
  - Moved from seat A's battery to `Residual.lean` beside `typedProg_mono` (`:677`), all proved
    `[propext, Quot.sound]`: `bitEntry_rows_append` (`:718`), `signature_rows_append` (`:739`),
    `pointTyped_rows_append` (`:744`), `bodyTyped_rows_append` (`:752`), `storePre_rows_append`
    (`:765`), `asyncPre_rows_append` (`:777`, no entry hypothesis now), `fiberPre_rows_append`
    (`:784`), **`typedProg_rows_append`** (`:805`, outright: `TypedProg src w ty p → TypedProg
    src' w ty p` for `src'.program = src.program`, `src'.table = src.table ++ t'`,
    `src'.services = src.services`).
  - `TypedProgRows.lean`: the tripwire `asyncRowOnly_now` is replaced by `asyncDomainBit_now`
    (`:36`, `fun _ _ _ _ _ h => h.1`) and pinned failing by a `#guard_msgs (error)` fixture (the
    `Iff.rfl` mismatch); `asyncRowOnly_false` (`:94`, new: the old reading admits host row 0 at
    the empty table, where the bit is `false`); `typedProg_not_table_monotone_of` (`:71`) kept as
    history under `AsyncRowOnly`; its unconditional instance `typedProg_not_table_monotone` is
    false at this commit and deleted, flipped by `typedProg_table_monotone` (`:118`, the
    positive control at the same two sources); `AsyncEntryRows` proved from
    `bitEntry_rows_append` (`asyncEntryRows`, `:132`). 14 axiom lines, all `[propext, Quot.sound]`.
  Builds (tested): `lake build Effect4.Laws.Program.Typed.Residual` exit 0; `lake env lean
  -DwarningAsError=true Test/Program/TypedProgRows.lean` exit 0; Assembly and the 40-module cone
  exit 0 (457 jobs; Adequacy, Stack, Seq, Scheduler, Assembly and 19 Test modules rebuilt), axiom
  lines 1143, none outside `[propext, Quot.sound]`.
- Step 7 (D-A1 (a), in progress; committed below with the generated files): receipt A's hunk on
  `Program/Admission.lean`: `AdmitRefusal.emptyColumn («at» : Path)` after `internalHandle`;
  `AdmittedProgram.columnsTable : findEmptyColumnInTable table = none`, `columnsType :
  findEmptyColumnInEffTy ty = none` after `intFreeType`; `admitProgram`'s last arm runs the two
  scans after `checkTable`; the module docstring lists a sixth requirement. Dependents:
  `CheckedTyping.admitProgram_eq_ok` (two more `split` arms, closed by the new fields),
  `Run.admitted_unique` (two more `_` per pattern), `Run.admitProgram_certificate` (two more simp
  facts), the hand-built certificates `Test/Run/RunContract.lean`, `Test/Api/HostSessionContract.lean`
  and `Test/Api/KeyedHostContract.lean` (the last not in receipt A's list): two fields each,
  `by decide +kernel` (plain `decide` does not reduce the scans: tested, the build failed with
  "did not reduce to `isTrue` or `isFalse`"). `AdmissionColumns.lean`: seat A's tripwire `#guard`
  deleted; four `#guard`s added: CE-015's host-row answer refused as `emptyColumn
  ["table","0","answer"]`, a host-row request as `["table","0","request"]` (on a program that does
  not call the row), a program answer `prod never nat` as `["program","answer"]` (`pNeverPair`,
  whose checker type is pinned by a `#guard`), and the inhabited table still admitted.
  `AdmitRefusal` is not a policy family (`cases-policy.json`, checked below), so `make
  check-cases` is not owed.
  Commands so far (tested): `LEAN_NUM_THREADS=4 lake build Effect4.Program.Admission` exit 0;
  `LEAN_NUM_THREADS=1 python3 scripts/generate.py --only derived` exit 0 (1 min 51 s; run directly
  first because `make gen-derived` begins with the full `lake build`, which cannot pass while the
  committed `RunnerDerived.lean` lacks the new constructor; only `src/Effect4/Api/RunnerDerived.lean`
  changed, +7 −1: the `emptyColumn` arm at index 7 of `shapeDoc`, `toVal`, `ofVal`, `fits`);
  `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.CheckedTyping Effect4.Laws.Run
  Test.Run.RunContract Test.Api.HostSessionContract Test.Api.KeyedHostContract
  Test.Program.AdmissionColumns` exit 0 after the `decide +kernel` repair; then the full default
  `LEAN_NUM_THREADS=6 lake build` exit 0, 744 jobs, 10 min 14 s, gates: "library-root gate: 134
  API/utility modules, 221 Laws-only modules; every library source is reachable; Effect4 never
  reaches Laws", "checked 522 modules and 71834 declarations; semantic/test axioms are [propext,
  Quot.sound]; exact implementation boundary (15 module(s), 23 declaration(s)) additionally allows
  Classical.choice"; `grep -c sorryAx` 0.
- Step 7 (`0b432dac`): the generator chain, serially, each `LEAN_NUM_THREADS=1` (tested, exit codes
  from each log's last line): `make gen-derived` exit 0 (2 min 52 s; it ran the full `lake build`
  first (no-op after the build above), then `generate.py --only variances` (byte-identical) and
  `--only derived` (byte-identical to the direct run: only `RunnerDerived.lean` differs from the
  base)); `make gen-lcnf` exit 0 (35 s): `ocaml/gen/api_gen.ml` (+21 −21),
  `ocaml/engine/api_engine.ml` (+21 −21), `ocaml/gen/closure-api_gen.tsv` (+4 −4),
  `ocaml/gen/closure-api_engine.tsv` (+4 −4), every hunk a permutation of join-point parameters
  in `exitScoped`'s specializations (`frame_fiber_resume_cause…`, `evaluate_prim_with_fiber…`,
  `evaluate_prim_finalizer_or…`) and the matching hash column; neither face names `AdmitRefusal`
  (tested, `grep`), so the permutation is not this change's content (its cause is assumed: the
  compiler's join-point order under a rebuilt environment); committed as written. `make gen-eff`
  exit 0, `make gen-wire` exit 0, `make gen-cas` exit 0: byte-identical (tested, `git status`).
  Then `opam exec --switch=effect4 -- dune build` in `ocaml/` exit 0 (18 s) and
  `LEAN_NUM_THREADS=4 make check-ocaml` exit 0 (33 s; it re-cut the printed corpus, 400
  programs, with `generated/corpus-index.tsv` unchanged; `dune test eff gen clock`, `dune test
  engine` and `gen-check.sh` all PASS, "== ALL PASS: 0 failure(s) ==" ten times, "gen-check:
  PASS"). `make check-cases`: not owed (`tools/Conform/Effect4/cases-policy.json`'s families are
  `Ty`, `Eff`, `NativeOp`, `RowKind`, `RowShape`, `Registration`, `Lit`, `Term`, `CauseTerm`; the
  new matches are on `Option Path`).
- Step 8 (`c9866f74`, optional, done: each row a few lines): `Adequacy.lean:145` **`fits_total`**,
  `:156` **`fits_partialUpdate`** (`unfold` then `split` on the update's arms, `fits_nat_irrel` at
  the number arms); the six rows as proved `StoreImplements` instances, `:491`–`:569`:
  `refUpdate_implements`, `refGetAndUpdate_implements`, `refUpdateAndGet_implements` (one
  `poke_world` each), `refUpdateSome_implements`, `refGetAndUpdateSome_implements`,
  `refUpdateSomeAndGet_implements` (`cases` on `pf.partialUpdate a`: `restate_world` when nothing
  is written, `poke_world` when a value is; the `AndGet` arm reads the fresh cell by
  `List.getElem?_set_self`). Each closes its `M3bAdequacy` line (`#obligation_proved … := @…`);
  ledger `M3bAdequacy` 8/66/74 → **2 open / 72 proved / 74**, ceiling 8 → 2; audit "71 paired, 3
  without a namesake, 0 mismatches" (tested). The section docstring says twenty-nine of the
  thirty-one rows. TY-08's promise half: `Assembly.lean` **`promiseTable_of_strong`** (the coarse
  `PromiseTable` from the strong `PromiseCell` column: `completionOk_of_fitsExit` at an exit, the
  reference arm as it stands, both in `Ty.subN`) and **`cells_of_typedState`** (`TypedState →
  HeapTable w ∧ PromiseTable w`, i.e. `WorldValid.cells` follows from the generated columns;
  dropping that field is owed consumption). All ten `[propext, Quot.sound]` (printed in
  `ProtocolPosts.lean`'s foot and `TypedSplit.lean`). Builds (tested): `lake build
  Effect4.Laws.Program.Typed.Adequacy` exit 0, `…Assembly` exit 0, the 40-module cone exit 0 (457
  jobs). The probe that drafted them (`scratchpad/probes/RefRows.lean`) compiled first.
- Step 9 (at `c9866f74`, tested): `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All` exit 0,
  "Build completed successfully (740 jobs)", 5 min 36 s. Gates as printed: "Effect4 library-root
  gate: 134 API/utility modules, 221 Laws-only modules; every library source is reachable;
  Effect4 never reaches Laws" and "Effect4 module and axiom gate: checked 522 modules and 71862
  declarations; semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (15
  module(s), 23 declaration(s)) additionally allows Classical.choice"; `grep -c sorryAx` 0,
  `grep -c error:` 0. Admission census unchanged: "1349 programs reach 48 protocol rows, none with
  a consumed `True` post". Ledger (`scratchpad/tools/ledger.py`, the last report of each scope):
  `M3bAdequacy` 2/72/74 (ceiling 2), `M3bAssembly` 3/1/4, `M6Ledger` 20/0/20, `M7` 4/0/4,
  `M6Edits` 6/7/13, `M3bWorld` 0/6/6, `M2Validity` 0/15/15, `M4Stack` 0/4/4, `M5Hooks` 0/1/1,
  `M4Handshake` 1/0/1, `Test.IndexedColumnDraft` 1/7/8; whole tree 72 scopes, **37 open**, 447
  proved, 484 total (seat I's: 43 open, 441 proved, 484). Row 132's census, rerun on seat A's
  probes from the main checkout (`docs/research/2026-10-01-formal-pass/organization/probes/
  TyCasesInTyped.lean`, `verify-TyCasesDeep.lean`, and the widened copy seat A used, module filter
  extended to `Laws.Program.Signature` and `Program.Admission`; `LEAN_NUM_THREADS=4 lake env lean
  -M6144`, exit 0 each): red controls true; `Typed` 3 (shallow), `Typed.Membership` 62
  (shallow); deep: `Typed` 8 hits, 1 person-written (`projectProduct_typed`), `Typed.Admission` 3
  hits, 1 (`ProgramSource.mk.sizeOf_spec`, compiler-made), `Typed.Membership` 80 hits, 20
  person-written, `Signature` 3 hits, 1 (`SigApp.mk.sizeOf_spec`), `Program.Admission` 11 hits, 3
  (two `mk.sizeOf_spec`, `findInt`): identical to receipt A's numbers, so no person-written case
  analysis on `Ty` was added outside `Membership.lean` (tested). Axioms: a scratch file of
  `#print axioms` for every theorem added or re-proved in steps 1–8 (`scratchpad/probes/
  AxiomsI2.lean`, 92 names), `lake env lean -M6144` exit 0: 92 lines, all `[propext,
  Quot.sound]` (tested).
- Step 10.1 (`8be71278`): `World.lean:149` **`ScopeLive`** `(w : World) (sc : Nat) : Prop :=
  (w.state.scopes.entryAt sc).isSome = true` (a def, once, beside the world order) and `:432`
  **`scopeLive_mono`** (`w.le newer → ScopeLive w sc → ScopeLive newer sc`, `ordered.1.2.2.2.1 sc
  h`: the machine world order's scope component; receipt I's `ord.1.1.2.2.2.1` is the same
  component read through `leHost`). Build (tested): `LEAN_NUM_THREADS=4 lake build
  Effect4.Laws.Program.Typed.World` exit 0, 360 jobs.
- Step 10.2 (`ed90205b`): the scope arm of membership.
  - `Membership.lean:66`: `HandleFits`'s scope arm is `target = Ty.scopeTarget ∧ ScopeLive w
    index`. The transport section (`:672`) takes `hscope : ∀ sc, ScopeLive w1 sc → ScopeLive w2
    sc` beside the other table transports; `handleFits_map` (`:708`), `flatFits_map` (`:720`),
    `servicesFit_map` (`:738`), `fits_map` (`:749`, premise `hscope` before `hsvc`) carry it;
    `fits_mono` (`:856`) passes `scopeLive_mono`; `fits_restrict` (`Typed/Admission.lean`) passes
    the identity; `Residual.fiberPre_mono`'s `setContext` arm passes `scopeLive_mono ord.1`.
    **`fits_scope_inv`** (`:866`: a member of `Ty.scope` is `Val.scopeHandle sc` with `ScopeLive w
    sc`) and **`fits_scopeHandle`** (`:885`, the converse) are new. Inhabitance at the scope
    target now allocates a scope: `Grows` (`:2364`) gains `scope`, `World.allocScope` (`:2436`)
    and `FreshFrom.allocScope` (`:2443`, through `ScopeStore.entryAt_make_isSome`/`_self`) are
    new, `fits_handle_fresh`'s scope case (`:2450`) uses them; `inhabited_iff_fits` (`:2565`) is
    unchanged in statement. `World.lean:151`: a `Decidable (ScopeLive w sc)` instance
    (`inferInstanceAs` on the `Bool` equation).
  - `Assembly.lean:247`: `MachineLive.ambientScopes` is gone; **`ambientScope_live`** (`:289`, new,
    13 lines) derives it from `J`: the fiber's context fits its services (`ServiceOk.c5`), the
    ambient scope is the scope key's binding (`Env.scopeOfVal`), the key's carrier is `Ty.scope`
    (`MachineTyped.services`, the table tie of step 4), and the scope arm gives presence.
    `machineLive_of_quiet` (`:904`) loses its contexts premise; `MachineLive`'s docstring says
    where the field went. `ExitHandlesValid`'s docstring: the scope arm reads presence.
  - Batteries: `ValueMembership.lean:973`, `LoadedAdmission.lean:135`, and
    `Membership.fits_hasTy` read the scope arm's first conjunct (`.1`); `M6Capstone`,
    `StaleCode`, `FramesNotKripke`, `TypedSplit` drop the contexts argument of
    `machineLive_of_quiet`. `ExitConnector.redA_scope` (seat A's red control A: a scope handle at
    a world with no externals) no longer holds at `initialWorld` (the handle dangles); it is
    restated at `scopeWorld` (`:45`, a world holding scope 7), and **`dangling_scope_refused`**
    (`:65`, new) proves the dangling handle does not fit at the initial world.
  Builds (tested): `lake build Effect4.Laws.Program.Typed.Assembly` exit 0 (391 jobs); the
  40-module cone failed first at `ValueMembership.lean:973`, `ExitConnector.lean:48`,
  `LoadedAdmission.lean:135` (the arm's new conjunct), then at `ExitConnector.lean:70` (the
  decidability of `ScopeLive`, hence the instance), then exit 0 twice (457 jobs), 0
  `sorryAx`/`Classical.choice`. Axioms printed in that build: `ambientScope_live`,
  `redA_scope`, `dangling_scope_refused`, `StaleCode.machineTyped_of_quiet` `[propext,
  Quot.sound]`; `machineLive_of_quiet`, `H1TerminalAmendment.quiet_live` `[propext]`.
- Step 10.3 (`b8723557`): the five posts that answer a scope handle carry presence.
  - `Residual.lean`: `storePost`'s `scopeMake` (`:92`), `scopeFork` (`:99`), `memoBuild` (`:103`)
    are `Fits w' ans Ty.scope`, `memoRelease` (`:107`) is `ans = Val.unit ∨ Fits w' ans
    Ty.scope`, `fiberPost`'s `ambientScope` (`:205`) is `Fits w' ans Ty.scope`. Membership owns
    the shape (one owner): `fits_scope_inv` reads such an answer back as `∃ sc, ans = scopeHandle
    sc ∧ ScopeLive w' sc`, the amendment's second spelling.
  - `Adequacy.lean`, re-proved from the operation, all `[propext, Quot.sound]`:
    `scopeMake_implements` (`:779`; `syncOpStep_scopeMake`, the entry by
    `ScopeStore.entryAt_make_self`), `scopeFork_implements` (`:802`; the child by
    `ScopeStore.entryAt_forkChild_child` at the parent's entry), `memoBuild_implements` (`:826`;
    the layer scope by `entryAt_make_self`), `memoRelease_implements` (`:449`; the last release's
    layer scope through `MemoWorld.entryAt_mem` and the store's memo clause),
    `ambientScope_answers` (`:1098`, takes `live : ScopeLive w scope`; its `M3bAdequacy`
    declaration `:1445` takes `ScopeLive w scope →`, as `getContext_answers`' declaration takes
    its premises; the audit pairs it, "71 paired, 3 without a namesake, 0 mismatches").
  - **`StoreTyped.memo : w.state.MemoValid`** (`:45`, new field): `memoRelease` answers a layer
    scope only the store's memo invariant holds present. The six constructions re-establish it by
    `syncOpStep_memoValid _ _ _ _ store.memo step` (`restate_world` `:82`, `poke_world` `:264`,
    `complete_world` `:342`, `refMake_implements` `:601`, `deferredMake_implements` `:695`,
    `memoBuild_implements`); `Assembly.lean:331` `storeTyped_of_typedState` reads it from
    `WorldValid.wf.2.2.1`.
  - **Outside the brief's list (measured, under the stop rule's "few lines")**:
    `Machine/StoresLaws.lean:1225` `syncOpStep_memoValid`'s premise `(hwf : s.WF)` became
    `(hmemo : s.MemoValid)`: its proof read only `hwf.2.2.1` (ten sites, each now `hmemo`), and
    its one caller (`syncOpStep_wf`, `:1652`) passes `hwf.2.2.1` (tested: `grep -rn
    syncOpStep_memoValid src/ Test/` finds that caller and nothing else). 12 lines, no content
    change; the theorem is strictly more general.
  - `Assembly.lean:311` **`ambientScope_answers_of_typed`** (new): at `J`, the answer the machine
    gives an `.ambientScope` read (the context's ambient scope, `FiberAction.ambientScope`,
    `Machine/Fibers.lean:1491-1498`) lies in the post, through `ambientScope_live`. This is the
    amendment's "`ambientScope_answers` from `MachineLive.ambientScopes` through `J`".
  - Docstrings: the `M3bAdequacy` section said 23 store rows proved and 8 declared (stale since
    step 8); it now says 29 and 2.
  - `ProtocolPosts.lean`: `Memo.memoRelease_post_admits` (`:279`) and `Memo.memoCode_refused`
    (`:314`) take `live : ScopeLive w 1` (the flip now holds where the layer scope is present,
    which a build guarantees); the pinned exclusion fixture (`:879`) prints the new disjunct
    (`h✝ : Typed.Fits w (Val.scopeHandle 1) Ty.scope`) and still fails as pinned.
    `ProtocolPosts`' foot prints the eleven re-proved store theorems and `syncOpStep_memoValid`,
    `TypedSplit` prints `ambientScope_answers_of_typed`.
  Builds (tested): `lake build Effect4.Laws.Machine.StoresLaws` exit 0 (201 jobs); `lake build
  Effect4.Laws.Program.Typed.Assembly` exit 0 (384 jobs, 4 min 5 s: StoresLaws' dependents
  rebuilt), first try; ledger `M3bAdequacy` 2/72/74 ceiling 2 unchanged, `M3bAssembly` 3/1/4,
  `M6Ledger` 20/0/20, `M7` 4/0/4, `M6Edits` 6/7/13, `M3bWorld` 0/6/6; the 40-module cone failed
  only in `ProtocolPosts` (`:277`, `:314`: the old flips' `⟨1, rfl⟩`; `:889`: the fixture's
  message), then exit 0 (457 jobs), 0 `sorryAx`/`Classical.choice`; the two batteries again with
  the new prints, exit 0, every printed line `[propext, Quot.sound]`.
- Step 10.4 (`c69ec57c`): `Residual.lean`'s `fiberPre` arms `runIn` (`:179`), `scopeExit` and
  `closeScope` (`:183`), `forkIn` (`:190`), and `storePre`'s `scopeAdd`/`scopeRemove`/
  `scopeIsClosed`/`scopeFork` arm (`:64`) read `ScopeLive w scope` (no change of content:
  `ScopeLive` is the old body; `interruptAs`, in the amendment's list, reads only the fiber table
  and is unchanged). `storePre_mono` and `fiberPre_mono` read `scopeLive_mono ord.1` for the
  order's scope component (no `ord.1.1.2.2.2.1` is left under `src/`, tested by `grep`). Three
  row-139 clauses read the same fact at the machine's store, not the world's
  (`Assembly.lean:200` `QueueOk.links`, `Scheduler.lean:113` `StoredObserverOk`, `:132`
  `ObserverCommandOk`, each `(m.state.scopes.entryAt scope).isSome = true`); they are not in the
  amendment's list and are left as they are (under `WorldValid.state` it is `ScopeLive w`; see
  "What is owed"). Build (tested): `lake build Effect4.Laws.Program.Typed.Assembly` with the
  40-module cone, exit 0 (457 jobs; 25 modules rebuilt), 0 `sorryAx`/`Classical.choice`.
- Step 10.5 (`9cbdd085`): the `scopeExit` constructor carries presence.
  - `Residual.lean:274` `TypedProg.scopeExit` takes `live : ScopeLive w sc` first (its docstring
    says why: the machine halts on an absent scope, `prepareScopedExitR`, the same presence
    `fiberPre`'s `scopeExit` arm states). Consumers (receipt I's measured hunk): `fiber_inv`'s
    pattern (`:297`), `typedProg_mono`'s arm (`:686`, `scopeLive_mono ord.1 live`),
    `typedProg_rows_append`'s arm (`:814`), seat E's `Seq.close_typed` (`Seq.lean:40`); seat C's
    `RawOrderLoad.fiber_inv`, the fourth, was deleted in step 2. All re-check `[propext,
    Quot.sound]` (printed in the batteries that print them; the final scratch list below).
  - `M6Capstone.H1HaltAmendment`: `callback_typed` (`:2008`) takes `live : ScopeLive w 0`;
    **`callback_refused`** (`:2019`, new) proves its old statement false at the witness's world
    (whose store holds no scope). The eight controls the amendment names stay as history over
    **`OldTypedProg`** (`:1749`, a local copy of the judgment whose `scopeExit` constructor reads
    no pre; every other constructor is the current one) and over H1's and the split's states
    built on it (`OldH1SavedPosition`, `oldH1StatePreds`, `OldH1TypedState` `:1800`;
    `OldSplitSavedPosition`, `oldSplitPreds`, `OldSplitTypedState` `:1823`, `OldLiveCode`,
    `OldReadCode`, `OldMachineTyped` `:1839`, `OldConfigTyped` `:1846`, `OldSplitStepPreserves`
    `:1853`; every other clause the current one, as `AwaitLoad.OldMachineTyped` keeps it):
    `worker_saved` (`:2029`), `typed` (`:2037`), `old_typed` (`:2075`, its row-133-only
    `OldSavedPosition` now over `OldTypedProg`), `typedState_input` (`:2492`), `config_input`
    (`:2527`), `step_deliver_false` (`:2191`), `deliver_preserves_this_state` (`:2378`, with
    `old_result_typed` `:2321`, the halted output over the old states), and
    `step_deliver_refuted_by_absent_scope` (`:2568`, over `OldSplitStepPreserves`, with
    `old_output_outside` `:2554`). Helpers `old_callback_typed`, `oldH1SavedPosition_of_saved`,
    `oldSplitSavedPosition_of_saved`, `OldTypedProg.pure_inv`. **`input_refused`** (`:2579`,
    new, the repaired red control): `∀ w, ¬ ConfigTyped rootProgram unitTy w machine commands` —
    the queued `deliver` reads the running worker's code (`ReadCode`), the saved resume frame's
    run arm must type the callback at `w`, the `scopeExit` constructor demands scope 0, and
    `WorldValid.state` puts `w`'s store at the machine's, which holds no scope 0. Unchanged and
    still current: `result_typed`, `unguarded_step_false`, `output_outside` and the rest of the
    section.
  - `Assembly.lean`: `M6Ledger.step_deliver`'s docstring (`:1489`) and `MachineLive`'s (`:245`)
    drop the refutation (the docstring names the history and `input_refused`); `step_loop`'s
    docstring says "refuted before row 156". The ledger line stays open.
  Builds (tested): `lake build Effect4.Laws.Program.Typed.Assembly` with the 40-module cone exit 0
  first try (457 jobs; Residual, Seq, Adequacy, Assembly and the batteries rebuilt), 0
  `sorryAx`/`Classical.choice`; then `lake build Test.Counterexamples.Machine.Semantics.M6Capstone`
  with `callback_refused` exit 0. Axioms printed by the battery: all 44 lines of the section at
  `[propext, Quot.sound]`, among them `input_refused`, `callback_refused`, `callback_typed`,
  `old_result_typed`, `step_deliver_refuted_by_absent_scope`.
- Step 10.6 (`f98edd9e`): `Test/Counterexamples/Machine/Semantics/ScopePresence.lean` (new, 462
  lines), imported by `Test/All.lean` right after
  `Test.Counterexamples.Machine.Semantics.RawOrderLoad` (line 29; the brief names no anchor
  line, so the new import sits with the M5/M6 counterexample batteries).
  - Kept from Codex's probe: `forkAfterMake`, `makeThenClose`, `point`, `startingWorld`;
    `forkAfterMake_checked` (`:81`, `decide +kernel`); the five `#guard`s (the checker's type,
    the run's `fiber 1` at fuel 40, the allocation's answer and installed entry, the number
    refused as a scope).
  - History, red against the old definitions (proved): `oldStorePost` (`:107`) and
    `oldFiberPost` (`:115`), the posts with the five old scope-handle arms and every other arm
    the current one, and `OldPostTypedProg` (`:120`), the judgment over them with the old
    `scopeExit` constructor; its inversions; `old_missing_answer_allowed` (`:198`),
    `old_makeThenClose_refused` (`:204`), `old_forkAfterMake_denotation_refused` (`:221`),
    `old_denotation_shape_false` (`:244`), Codex's four refutations restated over it. His two
    one-line controls are pinned failing against the current definitions by `#guard_msgs
    (error)` (`:267`, the old post's `⟨scope, rfl⟩`; `:282`, `absent_scope_still_fits`'s `⟨rfl,
    rfl⟩`).
  - Flips and positive controls over the current judgment (proved): `absent_scope_refused`
    (`:290`), `scopeMake_post_needs_presence` (`:298`), `scopeMake_post_iff` (`:304`: the landed
    post is Codex's candidate `presentScopeAnswer`), `close_live` (`:310`),
    `allocation_alone_typed` (`:319`), **`makeThenClose_typed`** (`:328`, at every world and
    source) and `makeThenClose_at_start` (`:336`), `child_checked` (`:342`, `decide +kernel`),
    `fork_node` (`:348`, `rfl`: the denotation's fork node after the allocation answers `sc`),
    **`forkAfterMake_typed`** (`:360`: the checked source's denotation at `point` is typed at
    `pure (fiberOf unit never)` at every world, through seat E's `seq_typed`,
    `denoteR_bind`, `fits_scope_inv` and `scopeLive_mono`), `forkAfterMake_at_start` (`:391`),
    and **`forkAfterMake_denotes`** (`:399`): `Assembly.lean`'s `DenotesTyped` proposition for
    `forkAfterMake` read at `point`, `∀ w e ty, Node.at_ … point.path = some (.eff e) →
    PointTyped … w point ty → TypedProg … w ty (denoteR … e point)`, the flip of
    `m5_denotation_shape_false`.
  Builds (tested): `LEAN_NUM_THREADS=4 lake env lean -M6144 -DwarningAsError=true
  Test/Counterexamples/Machine/Semantics/ScopePresence.lean`: four failing runs (the fixtures'
  messages, `fits_scope_inv` applied to an unfolded post, `rw` needing the bind spelled out;
  `decide +kernel` under free variables; one re-run of the unchanged file after a patch script
  failed on a quoting error; `decide` stuck on `Ty.subN`, replaced by `Ty.subN_refl`), then exit
  0; `lake build Test.Counterexamples.Machine.Semantics.ScopePresence` exit 0 (386 jobs). 22
  axiom lines, all `[propext, Quot.sound]`.
- Step 10.7 (at `f98edd9e`, tested): `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All` exit 0,
  "Build completed successfully (741 jobs)", 3 min 45 s (StoresLaws' dependents rebuilt). Gates
  as printed: "Effect4 library-root gate: 134 API/utility modules, 221 Laws-only modules; every
  library source is reachable; Effect4 never reaches Laws" and "Effect4 module and axiom gate:
  checked 523 modules and 72028 declarations; semantic/test axioms are [propext, Quot.sound];
  exact implementation boundary (15 module(s), 23 declaration(s)) additionally allows
  Classical.choice" (one module more than step 9: the new battery). `grep -c sorryAx` 0, `grep -c
  error:` 0. Admission census unchanged: "1349 programs reach 48 protocol rows, none with a
  consumed `True` post". `M3bAdequacy` audit "71 paired, 3 without a namesake, 0 mismatches",
  `M3bWorld` "5 paired, 1 without a namesake, 0 mismatches". Axioms of step 10: a scratch file
  (`scratchpad/probes/AxiomsStep10.lean`, every theorem whose lines a step-10 commit touched, 148
  names, including the `M3bAdequacy` namesakes), `lake env lean -M6144`, exit 0: 139 lines
  `[propext, Quot.sound]`, 8 `[propext]` (`machineLive_of_quiet`, `quiet_live`, `Grows.refl`,
  `Grows.trans`, four `FreshFrom.*`), 1 with no axioms (`isSome_extends`); none above the
  ceiling (tested). Row 132's census rerun (the three probes as in step 9, `lake env lean
  -M6144`, exit 0 each): identical to step 9 and receipt A (`Typed` 3 shallow / 8 deep with 1
  person-written, `Typed.Admission` 3 / 1, `Typed.Membership` 62 shallow / 80 deep with 20
  person-written, `Signature` 3 / 1, `Program.Admission` 11 / 3): no person-written case analysis
  on `Ty` was added outside `Membership.lean` (tested).

## Every changed path (`git diff --numstat a6ec2a28 f98edd9e`: 39 files, +1822 −787; and this receipt)

`src/`: `Effect4/Api/RunnerDerived.lean` (+7 −1, generated), `Effect4/Laws/Machine/StoresLaws.lean`
(+14 −13), `Effect4/Laws/Program/CheckedTyping.lean` (+10 −2), `Effect4/Laws/Program/Signature.lean`
(+15), `Effect4/Laws/Program/Typed/Adequacy.lean` (+202 −69), `Typed/Admission.lean` (+6 −3),
`Typed/Assembly.lean` (+167 −87), `Typed/Membership.lean` (+77 −23), `Typed/Residual.lean` (+171
−31), `Typed/Scheduler.lean` (+5 −8), `Typed/Seq.lean` (+1 −1), `Typed/Validity.lean` (+15 −4),
`Typed/World.lean` (+16), `Effect4/Laws/Run.lean` (+3 −3), `Effect4/Program/Admission.lean` (+23
−8). `Test/`: `All.lean` (+1), `Api/HostSessionContract.lean` (+2), `Api/KeyedHostContract.lean`
(+3 −1), `Counterexamples/Machine/Semantics/AwaitLoad.lean` (+9 −5), `FitsOrder.lean` (+59 −73),
`M6Capstone.lean` (+285 −55), `RawOrderLoad.lean` (+31 −126), `ScopePresence.lean` (+462, new),
`StaleCode.lean` (+2 −4), `ValueMembership.lean` (+6 −41), `Program/AdmissionColumns.lean` (+26
−6), `Program/ExitConnector.lean` (+30 −8), `Program/FramesNotKripke.lean` (+4 −12),
`Program/LoadedAdmission.lean` (+1 −1), `Program/ProtocolPosts.lean` (+38 −6),
`Program/SignatureControls.lean` (+1), `Program/TypedProgRows.lean` (+72 −146),
`Program/TypedSplit.lean` (+5), `Program/TypedWorldValidity.lean` (+1), `Run/RunContract.lean`
(+2). `ocaml/` (generated): `engine/api_engine.ml` (+21 −21), `gen/api_gen.ml` (+21 −21),
`gen/closure-api_engine.tsv` (+4 −4), `gen/closure-api_gen.tsv` (+4 −4). `docs/research/
2026-10-01-landing/receipt-I2.md` (this file, force-added). No coordinator file was edited
(`docs/core/decisions.md`, `docs/STATE.md`, `README.md`, `AGENTS.md`, `docs/core/system-map.md`,
`Test/Counterexamples/REGISTER.md`, `lakefile.toml` untouched; tested by `git diff --name-only`).

## Generated files (step 7)

Producer commands, serially, `LEAN_NUM_THREADS=1`, exit codes from each log: `python3
scripts/generate.py --only derived` (direct, before the full build could pass) exit 0; `make
gen-derived` exit 0 (byte-identical to the direct run); `make gen-lcnf` exit 0; `make gen-eff`,
`make gen-wire`, `make gen-cas` exit 0, byte-identical. Changed and committed as written:
`src/Effect4/Api/RunnerDerived.lean` (the `emptyColumn` arm, index 7), `ocaml/gen/api_gen.ml`,
`ocaml/engine/api_engine.ml`, `ocaml/gen/closure-api_gen.tsv`, `ocaml/gen/closure-api_engine.tsv`
(a permutation of join-point parameters in `exitScoped`'s specializations and its hash column;
neither face names `AdmitRefusal`; the cause is assumed, not traced). Then `opam exec
--switch=effect4 -- dune build` in `ocaml/` exit 0 and `LEAN_NUM_THREADS=4 make check-ocaml` exit 0
("== ALL PASS: 0 failure(s) ==", "gen-check: PASS"). No generator ran in step 10, as the brief
allows generators only in step 7. That no generated output would move is assumed, by reading:
every step-10 path is under `src/Effect4/Laws/` or `Test/` (tested: `git diff --name-only
8be71278^ f98edd9e`), the producers read the `Effect4` root, and `Effect4` never reaches Laws
(tested: the library-root gate's line).

## The ledger before and after (`scratchpad/tools/ledger.py` on the build logs: the last report of each scope)

Before (seat I's receipt, at `160012dc`): 72 scopes, 43 open, 441 proved, 484 total;
`M3bAdequacy` 8 / 66 / 74. After (step 10.7's build): 72 scopes, **37 open, 447 proved, 484
total**: `M3bAdequacy` 2 open / 72 proved / 74 (ceiling 2; the six `f.total` rows, step 8),
`M3bAssembly` 3 / 1 / 4, `M6Ledger` 20 / 0 / 20, `M7` 4 / 0 / 4, `M6Edits` 6 / 7 / 13, `M3bWorld`
0 / 6 / 6, `M2Validity` 0 / 15 / 15, `M4Stack` 0 / 4 / 4, `M5Hooks` 0 / 1 / 1, `M4Handshake` 1 / 0
/ 1, `Test.IndexedColumnDraft` 1 / 7 / 8; every other scope 0 open. Step 10 moved no ledger line
(it changes definitions and re-proves instances; `step_deliver` stays a declared goal).

## What is owed, with the exact obstacle

- `M6Ledger`'s 20 command goals, `step_deliver` among them: wave 2's command proofs. Row 156
  removes the one known refutation of `step_deliver`; nothing here proves it.
- `DenotesTyped` in general (`M3bAssembly.denoteR_typed`, declared): only its instance at
  `forkAfterMake`'s root point is proved (`ScopePresence.forkAfterMake_denotes`).
- One name for presence at the machine's store: `QueueOk.links` (`Assembly.lean:200`) and the
  observer clauses' `dropScopeFinalizer` arms (`Scheduler.lean:113`, `:132`) read
  `(m.state.scopes.entryAt scope).isSome = true`, the fact `ScopeLive w` states at the world (equal
  under `WorldValid.state`). Obstacle: those clauses are over `m`, not `w`; reading them through
  `ScopeLive` needs `w.state = m.state` at the clause (a coordinator's choice: keep, or give the
  machine-level spelling one name). Not in the amendment's list.
- `ambientScope_answers_of_typed` and `StoreTyped.memo` are consumed only by the adequacy layer:
  owed consumption by the command proofs (`loop`'s store arm, the ambient read).
- `M3bAdequacy`'s `memoGet`, `memoComplete`: a memo-table typing clause (every entry's Deferred
  declared at its layer's types) that no typed-state clause states (unchanged since step 8).
- `WorldValid.cells` is derivable (`cells_of_typedState`, step 8): dropping the field is owed
  consumption.
- Receipt A's owed items not in this brief: D-A2 (template parameters in row columns), C2, C7, C8
  of Σ_app, C4's converse, `evalTerm_fits`'s consumers.
- Bounded evidence: the `#guard`s (the run of `forkAfterMake` at fuel 40, the store steps, the
  admission refusals) are finite checks; the census and the exit-type lane are finite corpora; no
  host-only evidence was used.

## `step_deliver`'s ledger line after the constructor change

`M6Ledger.step_deliver` (`Assembly.lean:1489`) stays a declared, open goal (`M6Ledger`: 20 open,
0 proved, 20). It is **no longer refuted by `E4-SCHED-CE-020`'s witness** (proved): under the
current judgment that witness's input is not a typed configuration at any world
(`M6Capstone.H1HaltAmendment.input_refused`), because the worker's saved resume frame must type
the scope-exit callback at the input's world and the `scopeExit` constructor now demands scope 0,
which the machine's store does not hold (`callback_refused` at the witness's world). The
refutation `step_deliver_refuted_by_absent_scope` is kept as history over the pre-156 judgment
(`OldTypedProg`, `OldSplitStepPreserves`). Nothing here proves the goal: it is a command proof of
wave 2 (each halting arm of `deliverR` shown unreachable from `I`); no other refutation of it is
in the tree (tested: `grep -rn step_deliver src/ Test/`; besides that history, the two
`step_deliver_false` theorems, in `H1TerminalAmendment` and `H1HaltAmendment`, refute the
row-133-only `OldStepPreserves`, not `StepPreserves`).

## Lines proposed for the coordinator's files

Checked against what landed here; receipt A's wording kept where it still holds.

**`docs/core/decisions.md`**, status cells:

- Row 96: "D1 as amended by row 137: 'exactly the declared type' is equality of normal forms;
  `Equiv` compares in `Ty.subN` both ways (`Ty.subN_equiv_iff`), landed by seat A (`bbed898d`),
  integrated on seat I's union in pass I2 (`9eaee09c`–`a3d983fd`). D3's liveness now includes
  the scope store: a scope handle fits only when its scope is present (row 156, pass I2
  `ed90205b`)."
- Row 111: "Σ_app landed in Laws (`Laws/Program/Signature.lean`, seat A): `SigApp`, `SigExtends`;
  C3 both halves (`check_ext`, `check_restrict`), C5 (`restrictWorld`, `servicesFit_restrict`,
  `fits_restrict`), C6 (`LawfulSig`, `admitSig_ok_iff`, `lawful_append`); C4's append direction
  holds outright under row 116's bit (`typedProg_rows_append`, `Residual.lean`, pass I2
  `d5f6a0fe`); the typed state, the protocols and the M5–M7 premises read the source's signature
  (pass I2 `27896d8c`); C1 trivial; C2, C7, C8 open."
- Row 112: "Shape A landed (seat A, `f920d4e8`) and tied to the source (pass I2, `5f742b85`):
  `MachineTyped.services : w.serviceTy = root.sig.serviceTy`, set at the load
  (`initialWorld rootTy root.sig.serviceTy`, `machineTyped_load`), kept by the world order
  (`le_serviceTy`)."
- Row 113: receipt A's line, unchanged: "Per-code carriers landed: `SigApp.serviceTy`,
  `serviceTy_code`; red control `one_code_two_carriers`."
- Row 114: "`LawfulSig` travels on `ProgramSource.lawful` (default `SigApp.lawful_empty`);
  `admitSig_ok_iff` is its located refusal; `LawfulSource` is `LawfulSig root.sig`, which every
  source carries, and contains `Table.lawful` (`LawfulSig.tableLawful`, pass I2 `5f742b85`); M5
  and M6 range over lawful sources."
- Row 115: receipt A's line, unchanged.
- Row 116: "Landed (pass I2, `d5f6a0fe`): `asyncPre`'s external arm is `bitEntry` (the domain bit
  of the source's signature, then the row's columns); the old reading is refuted
  (`asyncRowOnly_false`) and its tripwire pinned failing; `TypedProg` is monotone along an
  appended table (`typedProg_rows_append`), the flip of `typedProg_not_table_monotone`, kept as
  history under the old reading."
- Row 127: "Landed (seat A, `de926765`; runner admission in pass I2, `0b432dac`, D-A1 (a)):
  `inhabited` agrees with `Fits` (`inhabited_iff_fits`) and is sound against `Val.hasTy`;
  `admitColumn` refuses `prod never nat` and `except never never`; runner admission refuses an
  empty column (`AdmitRefusal.emptyColumn`, `AdmittedProgram.columnsTable`/`columnsType`); the
  derived group regenerated in the fixed producer order."
- Row 137: "Landed at every site (seat A's arms and `World.lean:81`; seat B's `Residual.lean:56`;
  seat C's `CompletionStrong.ofRefGet`, `FiberColumnsBelow`, `RacePayload.live`/`.programs` in
  `Ty.subN`, pass I2 `a3d983fd`); `E4-TYPED-CE-009` repaired."
- Row 139: "Landed (seat C `b41d0808`; seat I `509d243c`; pass I2 under row 156): the scope arm
  of `HandleFits` reads the scope store (`ed90205b`), the scope-handle posts carry presence
  (`b8723557`), the `scopeExit` constructor reads it (`9cbdd085`); `MachineLive.ambientScopes`
  is derived from `J` (`ambientScope_live`); `step_deliver` is no longer refuted
  (`input_refused`). Three machine-store clauses (`QueueOk.links`, the observer clauses'
  scope-finalizer drop) spell the same fact at `m.state` (owed: one name)."
- Row 149: "Ruled (a) and landed: `emptyColumn` in the scans and at runner admission
  (`AdmitRefusal.emptyColumn`, pass I2 `0b432dac`); `AdmitRefusal.uninhabited` stays the `int`
  scan's; no contract revision."
- Row 156: "Landed in pass I2 (`8be71278`–`f98edd9e`; ratification owed): `ScopeLive`
  (`World.lean`) read by name by `HandleFits`' scope arm, the five scope-handle posts (`Fits w'
  ans Ty.scope`), the scope arms of `storePre`/`fiberPre` and `TypedProg.scopeExit`; the
  adequacy instances re-proved from the step (`StoreTyped.memo`, `syncOpStep_memoValid` at the
  memo clause); `E4-TYPED-CE-018` repaired by `ScopePresence.lean`; `step_deliver`'s refutation
  is history."

**`Test/Counterexamples/REGISTER.md`** (seat F's register):

- `E4-TYPED-CE-006`: append "`Equiv` compares in `Ty.subN` since 2026-10-01 (row 137);
  `natCell_equiv_spelling` through `Ty.sub_le_subN`." (receipt A's, holds: `ValueMembership.lean
  :822`).
- `E4-TYPED-CE-009`: "REPAIRED 2026-10-01 (seat A `bbed898d`, `55fe8043`, `ea77af5f`; integrated
  in pass I2 `b6e165d4`, `a3d983fd`): `FitsOrder.lean`: `prog3_loads_typed` (`J` at the load),
  `loadsTyped`, `capstone_at_load`, `rawLeaf_false`; historical `Reviewed.m5_false`,
  `Reviewed.loadsTyped_false`, `Reviewed.typedState_load_false`, `Reviewed.capstone_false` under
  `RawLeaf`; `RawOrderLoad.lean`'s three refutations as history; every declared-type comparison
  of the protocol entries in `Ty.subN`."
- `E4-TYPED-CE-015`: "REPAIRED 2026-10-01 at the column and the signature (seat A, `de926765`)
  and at runner admission (pass I2, `0b432dac`): `AdmissionColumns.lean`'s `#guard`s refuse
  CE-015's host-row answer as `emptyColumn ["table","0","answer"]`, a host-row request, and a
  program answer `prod never nat`, and admit the inhabited table; the tripwire is deleted."
- `E4-TYPED-CE-018`: "REPAIRED 2026-10-01 (pass I2, decisions row 156, `8be71278`–`f98edd9e`):
  `Test/Counterexamples/Machine/Semantics/ScopePresence.lean`: Codex's refutations as history
  over `OldPostTypedProg` (`old_missing_answer_allowed`, `old_makeThenClose_refused`,
  `old_forkAfterMake_denotation_refused`, `old_denotation_shape_false`), his two one-line
  controls pinned failing; flips `absent_scope_refused`, `scopeMake_post_needs_presence`,
  `makeThenClose_typed`, `forkAfterMake_typed` (every world, so `startingWorld`) and
  `forkAfterMake_denotes` (`DenotesTyped` at `point`); `forkAfterMake_checked` and the guards
  kept."
- `E4-SCHED-CE-020`: evidence cell: "`M6Capstone.lean`: `H1HaltAmendment.step_deliver_false`,
  `deliver_preserves_this_state`, `step_deliver_refuted_by_absent_scope` as history over the
  pre-156 judgment (`OldTypedProg`), `result_queue`, `root_unchanged`, `result_typed`,
  `unguarded_step_false`; `H1.halted_bad_exit_rejected`; since row 156 (pass I2, `9cbdd085`) the
  witness's input is refused (`input_refused`, `callback_refused`)." Status unchanged
  (REPAIRED); the repair cell gains "row 156: the `scopeExit` constructor reads `ScopeLive`".

**`docs/DESIGN-ISSUES.md`**: receipt A's DI-15 and DI-67 sentences hold as written (DI-67's
"admission refuses an empty column" now includes runner admission).

**`docs/core/system-map.md`**: receipt A's type-row sentence; and in the typed-state vocabulary,
"scope presence is one predicate, `ScopeLive w sc` (row 156), read by membership, the posts that
answer a scope handle, the protocols' scope arms and the `scopeExit` constructor".

**`docs/core/host-boundary.md` §4.4**: receipt A's ("exactly" reads "equal normal forms").

**`docs/STATE.md`**: "Pass I2 (2026-10-01): seat A integrated on seat I's union (rows 111–116,
127, 137, 149), runner admission refuses empty columns (D-A1 (a), generated group
regenerated), and row 156 landed (`ScopeLive`; `E4-TYPED-CE-018` repaired; `step_deliver` open
and no longer refuted)."
