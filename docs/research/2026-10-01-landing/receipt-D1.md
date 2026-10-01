# Seat D1 receipt: the four contract rows (117, 151, 152, 153)

Seat D1 of the 2026-10-01 landing, wave 2. Brief: `docs/research/2026-10-01-landing/brief-D1.md`
with its "Amendments (2026-10-01, after pass I2)" (they win where they differ from the body);
plan: `plan.md` (§4 rules, §5 measure). Worktree `/Users/pooks/Dev/lean4-effect4-seat-D1`, branch
`seat/D1`. Evidence words: **proved** (a kernel theorem compiled here, axioms printed),
**reproduced** (another seat's proved fact compiled again here), **tested** (a finite check run
here: a build's report, a `#guard`, a `grep`), **assumed** (not run here; a reading names the
lines read).

This file is written incrementally: a stop at any point leaves a true record of what was done up
to that point. The sections below the work log are filled as the rows land.

## The one thing first

**Two of the four rows stop at measured reports for the owner, and three shared shapes changed.**
Row 152 (a) and row 153 (b) landed in full (proved); row 117 landed its side condition only and
row 151 landed controls only. Row 151 (a) cannot land inside this seat's files: voiding the
`acquireRelease` release in `denoteFin` breaks the term/frame simulation (`foreignRelease_intro`,
`Intro/AcquireRelease.lean:100`, tested by a reverted trial) unless the frame machine voids too, a
runtime departure from rc.112 (`internal/effect.ts:3795`); and the scope store's generated typing
reads a `preds` clause only at `foreign` finalizers. Row 117's presence clause, measured by a
reverted trial and proved over local copies, is not preserved by the walk (`presence_not_walked`)
and needs a closed root row at M5 (`load_presence_needs_closed_row`): landing it alone would make
open M6 goals false, so part two is stopped. Before merging, know the shape changes a branch in
flight (seat D3's command proofs) may hit: `fitsExit_failure_iff` now ends `∧ ShapeFree c` and
`fitsExit_of_clean` takes a `ShapeFree c` argument (row 152; one token or one argument per site:
nine consumer sites outside `Membership.lean` and this seat's own batteries needed one); `PointTyped`, `storePre`'s `memoGet` arm and `CaptureTyped` check a
node through `Eff.expandIn src.program` (row 153; a proof that unfolds them and compares the check
with a raw-node lemma needs `Eff.expandIn_eq_self`; every existing control re-checked unchanged);
`IteratorProtocol.step` and `LoopProtocol.step` take a third argument `rows` (row 117; `fun _ =>
rfl` at equal or empty rows). The branch merges with `refactor/phase1-phase3` at `52cf49e7` with
no textual conflict (tested, `git merge-tree`; main changed no Lean file since the base).

## Base and head

Base: `6b3f2c92` (main after pass I2's merge `c898ad04` and its record). Code head: `589427c8`.
Head: the commit that adds this receipt (its child). Commits, one per row and in the brief's
order, each after its narrow build: `64df7977` (row 152), `e7426050` (row 151, controls),
`dd046828` (row 117, the side condition), `31845697` (row 117, the presence measurement),
`0c2e123e` (row 153), `589427c8` (row 151, the second red control). Nothing pushed; no `git
merge`, `checkout`, `reset` or `push` was run; no permission was refused. Two trial edits
(`DenoteR.lean`'s `foreign` arm for row 151, `Contracts.lean`/`Residual.lean`'s `SavedOk` for row
117) were built for measurement and restored byte for byte from copies before any commit
(tested: `git status` clean after each).

## Work log (incremental)

- Read in full: `brief-D1.md` with its amendments, `plan.md` (§4, §5, and the rest), `brief-G.md`'s
  "Rules", `receipt-I2.md` (all), `receipt-B.md` (all; "The findings for the owner", "What is
  owed"), `receipt-C.md` ("One thing first", "Lines for the coordinator's files", "What is owed",
  the proposed row on layer references), decisions rows 106, 107, 117, 132, 135, 136, 151, 152,
  153, 156 (`docs/core/decisions.md`, read-only), the formal pass's G5
  (`docs/research/2026-10-01-formal-pass/proofs/note.md:354-372`) and its probe
  (`proofs/probes/FrameCategory.lean`), `AGENTS.md`.
- Builds use `scratchpad/d1/tools/build.sh` (a logging wrapper around `LEAN_NUM_THREADS=2 lake
  build <modules>` in this worktree); the test cone is the reverse import closure of
  `Effect4.Laws.Program.Typed.Membership` over `src/` and `Test/` (`tools/cone.py`): 9 src modules
  and 26 Test modules besides `Test.All` (tested: the script's output, 37 lines with `Effect4.Laws`
  and `Test.All`).

### Row 152 (a), commit `64df7977`

- **The clause** (`Membership.lean:101` `ShapeFree`, `:132-139` the `exitOf` arm): `Fits w v
  (.exitOf a e)` at `Value.exitErr written` with `causeImage.ofVal written = some c` is now
  `CauseFits (fun x => Fits w x e) c ∧ ShapeFree c`, where `ShapeFree c` says no reason of `c`
  dies with `badName` or `notImplemented` (the body of `NoShapeDefect`'s failure arm, so
  `noShapeDefect_failure_iff : NoShapeDefect ty (.failure c) ↔ ShapeFree c := Iff.rfl`,
  `Admission.lean:36`, proved). `FitsExit` is `Fits` at the reified exit, so it carries the
  exclusion; `ExitOk`'s second conjunct is now implied by its first (statement kept).
- **Statements changed** (each was false after the clause): `fitsExit_failure_iff`
  (`Membership.lean:192`, now `↔ FitsCause w ty.error c ∧ ShapeFree c`) and `fitsExit_of_clean`
  (`:230`, a new premise `shape : ShapeFree c`; a clean `die badName` used to fit every exit
  type). **New**: `fitsExit_failure_cause` (`:198`), `fitsExit_failure_shape` (`:203`),
  `fitsCause_of_clean` (`:218`, the cause half `fitsExit_of_clean` used to prove inline).
  **Re-proved, statements unchanged** (one conjunct carried at the `exitOf` arm):
  `cleanExit_of_never_fits`, `fits_hasTy`, `fits_map` (so `fits_mono`, the arm's monotonicity),
  `fits_sub`, `fits_normalize` (`and_congr_left'`), `fits_instantiate_widens`, `fitsExit_sub`,
  `fitsExit_subN`, `completionOk_of_fitsExit`, `fits_queryReasons`,
  `fits_of_inhabited_handleFree`, `fits_of_inhabited_fresh` (the witness `exitErr ⟨[]⟩` is
  shape-free vacuously); `strongExit_of_clean` (`Admission.lean:151`, passes its `shape`) and
  `exitHasTy_of_fitsExit` (`ExitConnector.lean:52`, `fitsExit_failure_cause`).
- **Red control flipped** (`Test/Program/ProtocolPosts.lean`, `CloseIter`): `badName_fits` is
  history as `old_badName_fits` (`:550`) over `H2PartOne.oldExitFits` (`Test/Program/H2PartOne.lean:19`,
  a local copy of the old `exitOf` arm whose components read the current `Fits`); its flip
  `badName_refused` (`:579`, `¬ Fits w badNameExit (exitOf unit never)`, proved); the old proof
  script pinned failing against the current judgment by a `#guard_msgs (error)` fixture
  (`:1118`, "`introN` failed ... ⊢ Typed.Fits w CloseIter.badNameExit (Ty.unit.exitOf
  Ty.never)"). `closeSeq_protocol_refused` is history as `old_closeSeq_protocol_refused`
  (`:562`) over `OldCloseStep` (`:555`, the protocol's step clause with `oldExitFits` for
  `Fits`).
- **Positive controls** (proved): `closeSeq_protocol_typed` (`:678`), the negation of the old
  refutation at every root, world and exit: `IteratorProtocol root w (pure (exitOf unit never))
  (pure unit) (.store (.closeSeq [] ex []))`; and the general walk `closeSeq_protocol` (`:649`):
  for every remaining finalizer list whose programs are typed at `⟨unit, never⟩` at every later
  world, and clean, shape-free captured reasons (`CapturedOk`, `:609`), the walk meets the
  iterator protocol to the close-walk row's exact post; with `exitR_typed` (`:593`: the `Exit`
  primitive keeps a typed program typed at `Exit<a, e>`, through seat E's `close_typed`) and
  `capturedOk_append` (`:615`); `closeSeq_release_typed` (`:685`) its two-finalizer instance.
  `H2PartOne`: `base_badName_still_fits` is history as `old_base_badName_fits` (`:30`), flipped
  by `base_badName_refused` (`:39`) and `base_notImplemented_refused` (`:44`).
- **Examples that stayed positive** (tested: the 26-module test cone built, exit 0, with no
  `sorryAx` in the final log): every exit fixture of `ValueMembership.lean` (`g3_*`, the
  `exitOk` success exits; unchanged), the await-by-value controls (`ProtocolPosts.AwaitValue`,
  `AwaitLoad`), `join` (`TrivialPosts`), `catchCause`/`matchCause` shapes (`TypedControl.natCatch_*`,
  `TypedProgBindRed.catchNat_typed`, `TermFits`), every clean-failure and interruption control
  (`H2PartOne.interrupt_admitted`, `user_die_admitted`, `missingService_*`,
  `RaceFailureBuffers.*`, `TypedControl.cancel_*`, `sleep_stack_accepted`). The edits they
  needed are proof-only: `TypedControl.natErr_fits` (the shape conjunct), `leakyGuard_rejected`,
  `TypedStack` (`:80`), `AsyncHookContract.does_not_fit`, `clean_input_fits` (one token or a
  shape argument each); `RaceFailureBuffers.old_admitted`, `user_die_admitted`,
  `interrupt_admitted`, `missingService_admitted`, `last_empty_failure_typed`,
  `MissingServiceTransport.input_ok` (through `strongExit_of_clean` / `fitsCause_of_clean`).
  One test helper changed meaning: `StaleCode.exitFailClean` (`:86`) read `cleanExit`, which a
  clean `die badName` satisfies; it now reads "interruptions only", which the two finite
  machines satisfy (`only_root6`, `only_root7`, `finished7` re-decided by `decide +kernel`,
  tested), and `exitsTyped_of` derives both conjuncts from it.
- **Outside the brief's file list** (consequential repairs, measured): `Typed/Admission.lean`
  (+6 −1: `noShapeDefect_failure_iff`, `strongExit_of_clean`'s argument), `Typed/ExitConnector.lean`
  (one line), `Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean` (+5 −2),
  `StaleCode.lean` (+11 −5), `Test/Program/TypedControl.lean` (+13 −9),
  `Test/Program/TypedStack.lean` (one line).
- **Commands** (tested): `build.sh r152-src Effect4.Laws.Program.Typed.Assembly
  Effect4.Laws.Program.Typed.Seq Effect4.Laws.Program.Typed.ExitConnector`: first failed at
  `ExitConnector.lean:52`, `Admission.lean:148` (the two consumers), then exit 0 (391 jobs); the
  test cone: failed at the sites above, then exit 0. Axioms: a scratch file of `#print axioms`
  for the 33 names added or re-proved in `src/` (`scratchpad/d1/Axioms152.lean`, `lake env lean`,
  exit 0): 32 `[propext, Quot.sound]`, 1 `[propext]` (`noShapeDefect_failure_iff`); the
  battery theorems print in the build: the 11 `CloseIter` lines and the 3 new `H2PartOne` lines
  all `[propext, Quot.sound]`.
- **Register** (proposed): `E4-TYPED-CE-017` REPAIRED (lines below).

### Row 151 (a): stopped at a measured report (owner's decision); positive controls landed, commit `e7426050`

The recommended option has three parts; none lands inside this seat's files without either a
runtime change or a shape change the brief does not give it, measured as follows.

- **"Say which clause."** The scope store's typing is generated (`Typed/State.lean`'s
  `#typed_state` over `Typed/Sources.lean`). Printed here (tested: `#print
  Effect4.Program.Typed.ScopeStateOk`, `FinNameOk`, by `lake env lean` on a scratch file):
  `ScopeStateOk`'s open arms read `FinNameOk P w e` at each registered finalizer, and
  `FinNameOk` is `True` at every finalizer name except `foreign capture`, where it is the
  generated `CaptureOk P w e capture`, whose one field is `P.CaptureOk`. A scan of the
  environment (tested: every constant under `Effect4.Program.Typed` whose type or value names
  the generated `CaptureOk`) finds only `FinNameOk` and `CaptureOk`'s own projections, so
  **`preds.CaptureOk` (`Assembly.lean:125`) is the one clause the scope store's typing reads,
  and only for `foreign` finalizers**. Typing every registered finalizer (the failing `release`
  of the red control is a `FinName.release`, where `FinNameOk` is `True`) needs the generated
  bundle to read a clause at every finalizer name: a source row in `Typed/Sources.lean`
  (`FinName` as an owner, or a custom row at the scope store's finalizer fields), a new
  `Preds` field, and a line in every `Preds` instance (1 in `src/`, `Assembly.lean:113`; 7 in
  `Test/`: `M6Capstone.lean:194`, `:1124`, `:1794`, `:1818`, `:1875`, `H1Shapes.lean:50`,
  `ValueMembership.lean:417`; tested by `grep`), and `State.lean`'s pinned count line ("17
  predicates, 11 carrier predicates"). Outside the brief's list, and a shared shape seat D3's
  parallel command proofs build on.
- **The void.** Measured by a trial edit (tested, then reverted byte for byte from a copy):
  `denoteFin`'s `foreign` arm with the mask's continuation `seqR fun _ => .pure (.success .unit)`
  instead of `Effects.Program.pure` (`DenoteR.lean:268-269`). `LEAN_NUM_THREADS=2 lake build
  Effect4.Laws.Program.Intro.AcquireRelease …` failed at `Intro/AcquireRelease.lean:100`:
  `CodeMeans.actMask` needs `Delivers k` of the mask's continuation (`Means.lean:285-289`,
  `Delivers`, `:43`), and a voiding continuation does not only deliver. The frame side it is
  related to answers the release's own value: `Program/Compile.lean:1130-1131` (`.releaseBody`
  → `Prim.withFiber (EffThunk.releaseMasked …)`), transcribing rc.112
  `internal/effect.ts:3983` (`provideContext(release(a, exit), context)`, the finalizer's value)
  and `:3795` (`scopeCloseUnsafe` returns the lone finalizer's effect as is). So the void is a
  change to the frame machine too (the `Effect4` root, so the OCaml face regenerates through
  `make gen-lcnf`, which this seat may not run), and a departure from rc.112's runtime value
  (its declared type is `Effect<void>`, `Scope.ts:567`; the finalizer's declared type is
  `Effect<unknown>`, `internal/effect.ts:3850`, and the release's `Effect<unknown, never, R2>`,
  `:3980`): a signed divergence, the owner's to rule, like FR-08's.
- **Reading of the brief.** The brief names "the `.release label fails` arm of `denoteFin`"; that
  arm is `FinName.release`, a synthetic finalizer whose success is already `unit`. The value
  receipt B's finding and the row describe is an `acquireRelease` release's, which is the
  `foreign` arm (`DenoteR.lean:261-270`, whose masked body is `Body.release`); the measurement
  above is of that arm (assumed to be the intent; the `FinName.release` arm has the same
  simulation obstacle, `denoteFin_means`, `Simulation/Hooks.lean:284`).
- **Not landed, by the stop rule**: `scopeAdd`'s pre demanding the finalizer's typing alone
  (without the void it refuses registering an `acquireRelease` release that answers a
  non-`unit` value, which the checker admits, `Program/Checker.lean:201-209`: a narrower
  contract than the owner recommended), so `release_registration_admitted` stays as it is and
  `lone_release_outside_post` stays red.
- **Landed (proved), positive under every option**: `Scope.close` with zero, one and two
  finalizers installs a program typed at the close-scope row's `⟨unit, never⟩`:
  `CloseScope.close_zero_typed`, `close_one_typed`, `close_two_typed` (`ProtocolPosts.lean`),
  through `closeScope_installs` at three concrete stores (`okReleaseStore`, `twoReleaseStore`,
  the orders computed by `decide +kernel`); axioms `[propext, Quot.sound]` each (printed by the
  build). `H2PartOne`'s saved-frame facts are unchanged by this row (no edit).
- **Landed (proved), the second refused shape, commit `589427c8`** (receipt B had it by reading):
  `CloseScope.foreign_untyped` (`ProtocolPosts.lean:547`): for `acquireRelease(succeed 1, (a,
  exit) => succeed 5)`, which the checker admits (`acq_checked`, `:533`: at
  `⟨nat, never, {Scope}⟩`; the release's declared type is `Effect<unknown, never, R2>`, rc.112
  `internal/effect.ts:3973`), the foreign finalizer's program (`denoteFin (.foreign c)`) is
  typed at no type whose answer column is `unit`, at any world and closing exit: the masked
  release answers `5` (`release_check`, `:541`, the release node's type `nat` in every
  environment). A scope whose lone finalizer is that capture closes to exactly that program
  (`closeScopeUnsafeR`'s one-finalizer branch, `InterpR.lean:162`), so `closeScope_installs`'
  `lone` premise fails for it. With `lone_release_outside_post` (the failing `release`), both
  refused shapes the row names now have a proved red control. Axioms `[propext, Quot.sound]`
  (printed by the build).
- **Options for the owner** (row 151), with what each costs, measured above:
  (a) as recommended: the void in the term and the frame machine at the `foreign` release
  (re-prove `foreignRelease_intro`; regenerate the OCaml; a signed divergence), and the
  source-table row for finalizer typing. (a″) the same divergence placed once at the close:
  `Scope.close`'s lone-finalizer branch runs the finalizer then answers `void`
  (`closeScopeUnsafeR`, `InterpR.lean:157-163`, and `storesCloseScopeUnsafe`,
  `Machine/Stores.lean:1917-1923`), so finalizers are typed at `⟨unknown, never⟩` and an
  `acquireRelease` release needs no voiding of its own; this is where rc.112's types promise
  `void` (`Scope.ts:567`), still a runtime departure from `:3795`, and still the source-table
  row. (c) the handler side stays a hypothesis (`closeScope_installs`' `lone` premise),
  discharged per close by the command proofs. **Recommendation: (a″)**, if a divergence is
  accepted at all: one change at the one operation whose declared type is `void`, no change to
  how a release is typed; otherwise (c).

### Row 117: the side condition landed (commit `dd046828`); the presence clause measured and not landed (commit `31845697`); part two stopped

- **Measured first, as the brief asks** (tested: a trial edit of `Contracts.SavedOk` with a context
  argument and the clause `Provides ctx tin.requires`, built, then restored byte for byte from a
  copy). Cheap consumers (a few lines each): `Contracts.savedOk_mono` (`Contracts.lean:139`),
  `Residual.savedOk_mono` and its `M3bWorld` line (`Residual.lean:707`, `:854`), and by reading
  `Assembly.lean`'s `savedPosition_of_saved` (`:129`), `LiveCode` (`:217`) and `ReadCode` (`:227`),
  which would pass `f.context`. **Not cheap: the walk.** `Stack.lean:51` (`WalkTyped`'s saved
  case), `:391` (`saveAnswerR_typed`), `:413` (`deliver_active`), their `M4Stack` lines (`:443`,
  `:454`) and `popR_typed`'s conclusion: the build failed there (tested), and the walk's 24
  code-installing arms (`walk_saved _` in `popR_typed`, counted by `grep -c`) install code at a
  frame's output type (a guard's or answer slot's `tout`, a resumed iterator's or loop's `tin'`,
  a mask's type), for which presence at the current code says nothing. `PresenceMeasure`
  (`Test/Program/H2PartOne.lean:430-548`) proves it over local copies of the clause
  (`Provides`, `:442`; `SavedOkPresent`, `:446`): `presence_not_walked` (`:495`): a saved frame
  with code at the empty row and one answer frame up to a row requiring the scope service meets
  the clause in the empty context, and the frame `popR` leaves (`walk_installs`, `:488`, by
  `rfl`) does not; `walked_typed` (`:506`): the presence-free walk theorem still types that
  output. A clause the walk keeps must be per position: the stack carries the context each
  frame's output runs in (a scope exit or a context restore changes it inside a frame's
  continuation, which `FrameAccepts` sees only as `TypedProg` at a type), so `TypedProg` and the
  frame judgment would have to track the provided row (G5's coeffect reading). That is a
  redesign of `TypedProg`, `FrameAccepts`/`StackAccepts`, the walk, seat B's 40 fiber-row frame
  instances and the J/I code clauses, not a few lines. **And at the load**:
  `load_presence_needs_closed_row` (`:523`): the loaded root runs in `emptyCtx`, and the checker
  types `acquireRelease` outside `scoped` with the scope service in its row (`openProg_checked`,
  `:517`, `decide +kernel`), so the clause at the load needs `rootTy.requires = ∅`: M5, M6c and
  M7's fragment would gain that premise; rc.112 runs only closed rows: `Effect.runPromise` takes
  `Effect<A, E>`, whose requirement parameter defaults to `never` (`Effect.ts:17494-17497`), and
  an open row runs only through `runPromiseWith(context)` (`:17533-17535`).
- **Why the clause is not landed in `J` alone**: with presence at the current code only, `J`
  would not be inductive: `presence_not_walked`'s two frames are a fiber's frame before and after
  a `deliver` (the walk is `deliver`'s step), so `M6Ledger.step_deliver` would be refuted by a
  machine of that shape (assumed: the step-level witness is not built here; the walk-level fact
  is proved). Landing it would turn open M6 goals into false ones. The restored-context clause on
  `TypedProg.scopeExit` (`Provides prev ty.requires`) is not landed for the same reason: its only
  source in a typed state is presence at the `scoped` operation's position.
- **Landed: the side condition** (proved, `Residual.lean:373`, `:392`):
  `IteratorProtocol.step` and `LoopProtocol.step` carry `rows : tout.requires = ∅ →
  tin.requires = ∅` beside `errors`. These are the two frame arms the walk passes a failure
  through by the error columns alone (`popR_typed`'s `iter`/`loop` failure arms, through
  `strongExit_failure_of_error`), i.e. the non-discharging arms whose transport is G5's
  `exitOk2_transport`; the frames read the protocols at every later world (`FrameAccepts.iter`,
  `.loop`, row 135), so the condition is stated under `∀ w', w.leHost w' → …`. The other arms do
  not transport by columns: `restoreMask`/`finalizerMask` and `asyncFinalizer` have `tin = tout`;
  `answer` and `resume`'s run arm install code typed at `tout`; `resume`'s skip arm is itself
  the transport, stated in the exit judgment, which part two would strengthen in place.
  Consumers: `iteratorProtocol_mono`, `loopProtocol_mono` (re-proved, one binder each),
  `hookLaws_interpR` (two patterns, `Stack.lean`), `ProtocolPosts.closeSeq_protocol` (`fun _ =>
  rfl` at its empty rows). `HookLaws` is unchanged: the walk does not read `rows` in part one
  (owed consumption: part two's failure transport). The checker keeps the rows of a loop equal
  (`Program/Checker.lean:178-191`, the `iterate` rule answers `b.requires`), so the wave-2 loop
  arm meets the condition by reading; the generator's (`checkStmts`) is assumed, not read.
- **Flips** (`H2PartOne.MissingServiceTransport`): `loop_admitted` is history as
  `old_loop_admitted` (`:357`) over `OldLoopProtocol` (`:333`, the protocol without `rows`) and
  `oldFrameProtocols` (`:351`); `loop_refused` (`:369`, proved at every exit judgment `Ex`): the
  witness's stack from `inner` (requires the scope service) to `outer` (requires nothing) is
  refused. `loop_kept_admitted` (`:386`): a loop frame from `inner` to a row that keeps the scope
  service is accepted. `input_ok`, `output_eq`, `output_bad` are unchanged (facts about
  `FullExitOk` and `popR`).
- **Part two: stopped** (the brief's stop rule): `NoShapeDefect`'s alphabet does not gain
  `missingService`; `E4-TYPED-CE-008` stays SEEDED (its transport now fails at the loop frame,
  but a guard's skip arm and a scoped region's exit still carry `die missingService` from a
  requiring row to an empty one under part one, by reading `TypedProg.guard`'s skip premise and
  the `scoped` arm, `EvaluateR.lean:169-183`). The scoped and provision positive controls the
  row names belong to part two and are not written.
- **Commands** (tested): `build.sh r117-e2-src Effect4.Laws.Program.Typed.Assembly …Seq
  …ExitConnector` exit 0 first try; the test cone failed only at `H2PartOne.lean:328` (the old
  `loop_admitted`), then exit 0 with no `sorryAx`. Axioms (printed by the builds): the three new
  `H2PartOne` theorems of the side condition and the seven of `PresenceMeasure` `[propext,
  Quot.sound]`, except `walk_installs` `[propext]`; the re-proved `iteratorProtocol_mono`,
  `loopProtocol_mono`, `hookLaws_interpR`, `popR_typed_interpR` are in step 5's list.

### Row 153 (b), commit `0c2e123e`

- **The redirect agreement** (proved, `DenoteR.lean:1199` `denoteLayer_ref_redirect`, in the
  layer equations' section): under well-formed references (`root.layerRefsWF = true`), for a
  reference site `(site, target) ∈ root.refSites []` and a point with fuel `k + 1`,
  `denoteLayer root (.ref target) q m scope = denoteLayer root (LayerTerm.expandRound (Node.eff
  root) (.ref target)) (q.redirect target) m scope`: the build of a reference is the build of its
  expansion (its target's term, `Program/Refs.lean`'s `expandAlgebra`) at the redirected point.
  Proved from the `.ref` arm of `denoteLayerWith` (`denoteLayer_ref_succ`) and the
  well-formedness clause that the target is a layer that is not a reference.
- **Why not an equality of the two programs' denotations** (proved red, `Test/Program/
  LayerRefs.lean:180` `memo_keys_differ`): at a program whose target is memoized
  (`Layer.effect`), the run's build at the reference site keys the memo on the target's path
  (`run_key`, `[0, 0]`) and the expansion's copy at the same point keys it on the site's
  (`expansion_key`, `[1, 0]`), so the two builds are different programs; the redirect is what
  gives two references one memo entry (`Program/Refs.lean`'s module note). Receipt C's wording
  of (b), "the raw program's denotation at a point equals the expansion's at the redirected
  point", is therefore landed as the redirect lemma above, with the typing read through the
  expansion (next item); the expansion is the checker's object, not a model of the run.
- **M5's reduction over the expansion.** The typed state reads a node through the rounds of the
  program's expansion: `Eff.expandIn root e` (`ReferenceTyping.lean:122`, the rounds
  `expandRefs` runs, on a subterm; `Eff.expandIn_self` (`:132`): `expandIn root root =
  root.expandRefs` by definition; `Eff.expandIn_eq_self` (`:152`) and
  `LayerTerm.expandIn_eq_self` (`:157`) for reference-free subterms; `Eff.expandIn_acquireRelease`
  (`:169`)). `PointTyped` (`Typed/Admission.lean:129`), `storePre`'s `memoGet` arm
  (`Residual.lean:68`) and `CaptureTyped` (`Assembly.lean:96`, the `preds.CaptureOk` clause)
  check the expansion of the node as written; the node and the run stay the program's.
  `loadsTyped_of_denotesTyped` (`Assembly.lean:1004`) has no `refFree` premise now: the root
  point is typed by `typeOfProgram`'s own verdict (`Program/Typing.lean:61-64`, through
  `Eff.expandIn_self`). Re-proved: `capture_lookup` (`:842`, `Eff.expandIn_acquireRelease`),
  `pointTyped_rows_append`, `storePre_rows_append` (one `rw [hprog]` each). For a reference-free
  program every reading is the old one (`expandIn_eq_self`); every existing positive control
  re-checked unchanged (tested: the 26-module typed test cone, exit 0, no `sorryAx`, no edit).
- **Red, history** (`Test/Program/LayerRefs.lean`): `OldPointTyped` (`:72`, the point typing
  before row 153, checking the node as written); `old_root_untyped` (`:82`): at every world, fuel
  and type the corpus's `layer.ref` root point is not typed, since the checker refuses the
  program as written (`check_refuses`, `:56`) while certifying its expansion (`checked`, `:46`;
  `check_expansion`, `:65`); `has_reference` (`:53`): the old reduction's premise fails here.
- **Positive controls** (proved): `root_typed` (`:96`): the root point is typed at the checker's
  type at every world and fuel; `loadsTyped` (`:116`): `DenotesTyped src → LoadsTyped src rootTy
  fuel cf` at every fuel, through the restated reduction (`noMarker`, `:100`, at every compile
  budget); `site_redirect` (`:123`): the lemma at the program's one reference;
  `expansion_site_is_target` (`:132`): the expansion holds the target's term at the site
  (`decide +kernel`, a finite check). `TypedSplit.lean`'s note now points here.
- **Outside the brief's list** (measured): `Laws/Program/ReferenceTyping.lean` (+63, new
  definitions and lemmas beside `expandRefs`'s C4 lemmas) and `Typed/Admission.lean`
  (`PointTyped`'s check, +8 −2 with the import), the definition the expansion reading has to
  live in so the run's typing premises and the reduction's agree; `Test/Program/TypedSplit.lean`
  (its note).
- **Owed** (the exact obstacle): `LoadsTyped` at `layer.ref` is proved from `DenotesTyped`, M5's
  open denotation lemma (`M3bAssembly.denoteR_typed`), not outright; the general fact that the
  expansion holds the same term at a site and at its target (`expansion_site_is_target` is its
  instance here), which the denotation lemma needs at each hop, is not proved: it needs the
  expansion's rounds to reach a fixed point within `refSites.length + 1` rounds under
  `layerRefsWF`'s program order (a depth bound over the seven mutual sorts of `expandRound`).
- **Axioms** (`lake env lean -DwarningAsError=true Test/Program/LayerRefs.lean`, exit 0, 24 lines,
  every one `[propext, Quot.sound]` or `[propext]`): `denoteLayer_ref_redirect`,
  `loadsTyped_of_denotesTyped`, `capture_lookup` `[propext, Quot.sound]`; `Eff.expandIn_self`,
  `Eff.expandIn_eq_self`, `LayerTerm.expandIn_eq_self`, `Eff.expandIn_acquireRelease`
  `[propext]`; the battery's 17 theorems as printed.
- **Register**: `E4-TYPED-CE-019`, SEEDED by `old_root_untyped` and REPAIRED by `root_typed`,
  `loadsTyped` (lines below).

### Step 5: the final build, the census, the ledger, the axioms (at `589427c8`)

- `LEAN_NUM_THREADS=2 lake build Effect4.Laws Test.All` (tested, through `build.sh final2`):
  exit 0, "Build completed successfully (743 jobs)" (the base's 742 and `Test.Program.LayerRefs`).
  Gates as printed: "Effect4 library-root gate: 134 API/utility modules, 221 Laws-only modules;
  every library source is reachable; Effect4 never reaches Laws" and "Effect4 module and axiom
  gate: checked 525 modules and 72273 declarations; semantic/test axioms are [propext,
  Quot.sound]; exact implementation boundary (15 module(s), 23 declaration(s)) additionally allows
  Classical.choice". `grep -c sorryAx` 0, `grep -c '^error'` 0. The two threads sufficed (the
  first full run, `final1`, before the last commit: 89 s; `final2`: 45 s).
- Admission census (printed by `Test/Program/AdmissionCensus.lean:153`): "1349 programs reach 48
  protocol rows, none with a consumed `True` post", unchanged.
- Ledger (`scratchpad/d1/tools/ledger.py` on the build log, the last report of each scope): 72
  scopes, **37 open, 447 proved, 484 total**, unchanged from pass I2: `M3bAdequacy` 2/72/74,
  `M3bAssembly` 3/1/4, `M6Edits` 6/7/13, `M6Ledger` 20/0/20, `M7` 4/0/4, `M4Handshake` 1/0/1,
  `Test.IndexedColumnDraft` 1/7/8, every other scope 0 open. No ledger line moved: the rows change
  definitions and batteries, and the goals they serve (M5's `denoteR_typed`, the command proofs)
  are wave 2's.
- Axioms: a scratch file of `#print axioms` for 71 `src/` theorems added or re-proved across the
  four rows (`scratchpad/d1/AxiomsAll.lean`, `lake env lean -M6144`, exit 0): 63 `[propext,
  Quot.sound]`, 8 `[propext]` (`noShapeDefect_failure_iff`, `Eff.expandIn_self`,
  `foldl_expandRound_eq_self`, `foldl_layer_expandRound_eq_self`, `Eff.expandIn_eq_self`,
  `LayerTerm.expandIn_eq_self`, `foldl_expandRound_acquireRelease`,
  `Eff.expandIn_acquireRelease`); none above the ceiling. Every battery theorem prints its axioms
  in the build, all `[propext, Quot.sound]` or `[propext]`.
- Row 132's census (tested): the organization seat's probes, copied to the scratchpad from
  `docs/research/2026-10-01-formal-pass/organization/` (`probes/TyCasesInTyped.lean`,
  `verify-TyCasesDeep.lean`), `lake env lean -M6144`, exit 0 each, red controls true: shallow
  `Typed` 3, `Typed.Membership` 62; deep `Typed` 8 hits with 1 person-written
  (`projectProduct_typed`), `Typed.Admission` 3 with 1 (`ProgramSource.mk.sizeOf_spec`,
  compiler-made), `Typed.Membership` 80 with 20: identical to pass I2's, so no person-written case
  analysis on `Ty` was added outside `Membership.lean`. (`denoteLayer_ref_redirect` cases on
  `LayerTerm`, not `Ty`.)
- `make check-cases`: not owed (no new match on a policy family; the new matches are on
  `LayerTerm`, `Val`, `RProgram`, `Option`). No generator was run.

## Every changed path (`git diff --numstat 6b3f2c92 589427c8`: 17 files, and this receipt)

`src/`: `Effect4/Laws/Program/DenoteR.lean` (+48), `Laws/Program/ReferenceTyping.lean` (+63),
`Laws/Program/Typed/Admission.lean` (+14 −3), `Typed/Assembly.lean` (+23 −17),
`Typed/ExitConnector.lean` (+1 −1), `Typed/Membership.lean` (+56 −25), `Typed/Residual.lean`
(+23 −9), `Typed/Stack.lean` (+2 −2). `Test/`: `All.lean` (+1, `Test.Program.LayerRefs` right after
`Test.Program.H2PartOne`), `Counterexamples/Machine/Semantics/AsyncHookContract.lean` (+5 −2),
`StaleCode.lean` (+11 −5), `Program/H2PartOne.lean` (+242 −20), `Program/LayerRefs.lean` (+230,
new), `Program/ProtocolPosts.lean` (+326 −29), `Program/TypedControl.lean` (+13 −9),
`Program/TypedSplit.lean` (+10 −8), `Program/TypedStack.lean` (+1 −1).
`docs/research/2026-10-01-landing/receipt-D1.md` (this file, force-added). Outside the brief's
named list, each measured in its row's section: `ReferenceTyping.lean`, `Admission.lean`,
`ExitConnector.lean`, `AsyncHookContract.lean`, `StaleCode.lean`, `TypedControl.lean`,
`TypedStack.lean`, `TypedSplit.lean`. Not touched: `Assembly.lean:200`, `Scheduler.lean` (seat
D3's step 0), the foot of `Assembly.lean` (`M6Ledger`/`M6Edits`/`M7`), `Typed/Commands/`,
`Edits.lean`, and every coordinator file (`docs/core/decisions.md`, `docs/STATE.md`,
`README.md`, `AGENTS.md`, `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md`,
`lakefile.toml`; tested by `git diff --name-only 6b3f2c92 HEAD`).

## Plan §5

1. **Repeated proofs that disappeared.** Few, honestly: `fitsExit_of_clean`'s inline cause proof
   is `fitsCause_of_clean` (one home, read by `RaceFailureBuffers.old_admitted` and
   `old_base_badName_fits`); part one's alphabet has one predicate, `ShapeFree`, which
   `NoShapeDefect`'s failure arm is (`noShapeDefect_failure_iff`, `Iff.rfl`); the old reduction's
   two-lemma plumbing (`expandRefs_eq_self_of_refSites_nil`, `layerRefsWF_of_refSites_nil`) is one
   `Eff.expandIn_self` (`rfl`). Nothing else was deduplicated.
2. **Program-to-execution connections closed.** M5's reduction now covers programs with layer
   references (`loadsTyped_of_denotesTyped`, no reference-free premise), with the run's hop and
   the checker's object tied by `denoteLayer_ref_redirect`; the close walk's iterator protocol is
   proved for clean finalizers at the close-walk row's exact post (`closeSeq_protocol`), the
   handler side `E4-TYPED-CE-017` lacked. Owed consumption: the wave-2 `closeIter` arm of `loop`
   reads `closeSeq_protocol` (it lives in the battery; moving it beside `closeWalk_typed` in
   `Typed/Adequacy.lean` is a one-commit move); `rows` is read by no walk step until part two.
   The ledger's open count is unchanged (37).
3. **The eventual claim.** Unchanged by this seat: M7 covers the frame machine at the empty host
   table on answer-free tapes with observation `obs` (row 138); nothing here is verified lowering
   or host safety. Row 153 widens M5's reduction to programs with layer references; M5 itself
   stays open (`denoteR_typed`).

## What is owed, with the exact obstacle

- **Row 151, the owner's decision** (options and costs in its section): then the source-table row
  for finalizer typing (`Typed/Sources.lean`, a `Preds` field, 1 + 7 instances), the void in the
  term and in the frame machine with `foreignRelease_intro` re-proved and the OCaml face
  regenerated, `scopeAdd`'s pre, and the flips `lone_release_outside_post` → positive and
  `release_registration_admitted` → red. `E4-TYPED-CE-016` stays SEEDED.
- **Row 117, the owner's decision on the presence design**: a clause the walk keeps is per position
  (each frame's output runs in a context a continuation may restore), so `TypedProg` and
  `FrameAccepts`/`StackAccepts` would carry the provided row (G5's coeffect reading); M5, M6c and
  M7's fragment gain `rootTy.requires = ∅` at the load (rc.112 runs closed rows,
  `Effect.ts:17494-17497`). Then part two (`missingService` in `NoShapeDefect`'s alphabet at an
  empty row), its scoped and provision positive controls, and the walk's failure transport reading
  `rows`. `E4-TYPED-CE-008` stays SEEDED.
- **Row 152**: the `causeOf` arm of `Fits` still admits shape defects in a reified cause (the
  value a `catchCause`/`matchCause` handler reads); the row names `exitOf` only, so it is left as
  is (a question for the owner, not a finding: no refutation is known).
- **Row 153**: the general fact that the expansion holds the same term at a reference site and at
  its target (`expansion_site_is_target` is its instance at `layer.ref`), needed by
  `denoteR_typed` at each hop: it needs the expansion's rounds to reach a fixed point within
  `refSites.length + 1` rounds under `layerRefsWF`'s program order (a depth bound over the seven
  mutual sorts of `expandRound`); and `LoadsTyped` at `layer.ref` outright, which waits on
  `denoteR_typed`.
- **Wave 2's new obligation from the side condition**: the `loop` and `gen` command arms construct
  the protocols with `rows`, from the checker's typing (the `iterate` rule answers the body's
  row, `Program/Checker.lean:178-191`, so it holds there; the generator's `checkStmts` row is
  assumed, not read).
- **Bounded evidence**: the finite facts are kernel computations on concrete programs and stores
  (`decide +kernel`, `rfl`): the close orders, the memo keys, the checked types, the expansion's
  layers; the admission census is a finite corpus walk. The general theorems quantify over every
  world, program, exit and finalizer list. No host-only evidence was used; no TypeScript was
  checked.

## Lines proposed for the coordinator's files

**`docs/core/decisions.md`** (status lines to append):

- **Row 152**: "Landed 2026-10-01 (seat D1, `64df7977`; ratification owed): `Fits` at `exitOf a e`
  reads `ShapeFree` on the encoded cause (`Membership.lean`; `NoShapeDefect`'s failure arm is
  `ShapeFree`, `noShapeDefect_failure_iff`), so `FitsExit` carries part one's exclusion
  (`fitsExit_failure_iff` gains the conjunct, `fitsExit_of_clean` a premise); membership's laws
  re-proved at the arm. The close walk types at the exact post for clean finalizers
  (`ProtocolPosts.CloseIter.closeSeq_protocol`, `closeSeq_protocol_typed`); `badName_fits` and
  `closeSeq_protocol_refused` are history over `H2PartOne.oldExitFits`. Every exit fixture and
  every await-by-value, join, catch and match control stayed positive. `E4-TYPED-CE-017`
  repaired."
- **Row 151**: "Wave 2 (seat D1, `e7426050`, `589427c8`): not landed; measured. Option (a)'s void
  in `denoteFin`'s `foreign` arm breaks the term/frame simulation (`foreignRelease_intro`,
  `Intro/AcquireRelease.lean:100`: `CodeMeans.actMask` needs `Delivers`) unless the frame machine
  voids too (`Program/Compile.lean:1130-1131`, a departure from rc.112's runtime value at
  `internal/effect.ts:3795`); the scope store's generated typing reads `preds.CaptureOk` only at
  `foreign` finalizers, so typing every finalizer needs a source-table row and a `Preds` field.
  Both refused shapes are proved red (`lone_release_outside_post`; `foreign_untyped`, the
  `acquireRelease` release answering a value); `Scope.close` with zero, one and two finalizers is
  typed at `⟨unit, never⟩` (`close_zero_typed`, `close_one_typed`, `close_two_typed`). Seat D1
  recommends (a″): void once at `Scope.close`'s one-finalizer branch (term and frame), where
  rc.112's type promises `void` (`Scope.ts:567`), finalizers typed at `⟨unknown, never⟩`, with the
  source-table row; else (c). Owner's decision owed."
- **Row 117**: "Wave 2 (seat D1, `dd046828`, `31845697`): the side condition landed: the iterator and
  loop protocols carry `rows : tout.requires = ∅ → tin.requires = ∅` (the frames read them at every
  later world); `MissingServiceTransport.loop_admitted` is history over `OldLoopProtocol`, flipped
  by `loop_refused`. The presence clause is not landed: proved over local copies, presence at the
  current code is not preserved by the walk (`H2PartOne.PresenceMeasure.presence_not_walked`) and
  at the load needs a closed root row (`load_presence_needs_closed_row`); landing it alone would
  make open M6 goals false. A per-position clause (`TypedProg` and the frame judgment carrying the
  provided row) and M5's closed-row premise are the owner's to rule; part two waits on them.
  `E4-TYPED-CE-008` stays seeded."
- **Row 153**: "Landed 2026-10-01 (seat D1, `0c2e123e`; ratification owed) as (b):
  `denoteLayer_ref_redirect` (`DenoteR.lean`: under `layerRefsWF`, a reference site's build is its
  expansion's, the target's term, at the redirected point); the typed state reads a node through
  the expansion's rounds (`Eff.expandIn`, `ReferenceTyping.lean`; `PointTyped`, `storePre`'s
  `memoGet`, `CaptureTyped`), so `loadsTyped_of_denotesTyped` has no reference-free premise.
  `Test/Program/LayerRefs.lean`: `old_root_untyped` (history), `root_typed`, `loadsTyped` (from
  `DenotesTyped`), `site_redirect`; `memo_keys_differ` shows the run is not the expansion's (a
  reference keys the memo on its target), so the agreement is the redirect, not an equality of
  denotations. Owed: the expansion holds the same term at a site and its target, in general.
  `E4-TYPED-CE-019` seeded and repaired."

**`Test/Counterexamples/REGISTER.md`** (cells; each row's other cells stand):

- `E4-TYPED-CE-017`, status: "REPAIRED 2026-10-01 (seat D1, decisions row 152, `64df7977`); SEEDED
  2026-10-01"; witness cell: "`Test/Program/ProtocolPosts.lean`, `CloseIter`: `old_badName_fits`,
  `old_closeSeq_protocol_refused` (history over `H2PartOne.oldExitFits`, `OldCloseStep`; the old
  proof pinned failing by a `#guard_msgs (error)` fixture); flips `badName_refused`,
  `closeSeq_protocol_typed`; the walk `closeSeq_protocol` with `exitR_typed`,
  `capturedOk_append`, `closeSeq_release_typed`".
- `E4-TYPED-CE-016`, status unchanged (SEEDED); witness cell, append: "the `acquireRelease` shape
  proved (seat D1, `589427c8`): `CloseScope.acq_checked`, `release_check`, `foreign_untyped`;
  positive under every option: `close_zero_typed`, `close_one_typed`, `close_two_typed`"; repair
  cell, append: "measured (seat D1 receipt): the void breaks `foreignRelease_intro` without a
  frame-machine change; finalizer typing needs a source-table row; owner's decision".
- `E4-TYPED-CE-008`, status unchanged (SEEDED); witness cell, replace `loop_admitted` by
  "`old_loop_admitted` (history over `OldLoopProtocol`), `loop_refused` (row 117's side condition,
  seat D1 `dd046828`), `loop_kept_admitted`"; repair cell, append: "the side condition landed; the
  presence clause measured, `PresenceMeasure.presence_not_walked`,
  `load_presence_needs_closed_row` (seat D1 `31845697`); part two waits on the owner's presence
  design".
- `E4-TYPED-CE-003`, repair cell: replace "base Fits/FitsExit stay unchanged" and
  "`base_badName_still_fits`" by "since decisions row 152 base `Fits` at an exit type excludes them
  too (`base_badName_refused`, `base_notImplemented_refused`; the earlier base judgment as
  history, `old_base_badName_fits` over `oldExitFits`)".
- New row: `| E4-TYPED-CE-019 | REPAIRED 2026-10-01 (seat D1, decisions row 153, `0c2e123e`); SEEDED
  2026-10-01 | M5 reduces to the denotation lemma for every checked program | `Test/Program/
  LayerRefs.lean`: `old_root_untyped` (with `OldPointTyped`, the point typing as written: the
  corpus's `layer.ref` root point is typed at no type, the checker refusing the program as written,
  `check_refuses`, while certifying its expansion, `checked`), `has_reference` | `PointTyped`
  reads a node through the expansion's rounds (`Eff.expandIn`); `root_typed`, `loadsTyped`,
  `site_redirect`, `expansion_site_is_target`; `memo_keys_differ` keeps the run the program's |`.

**`docs/core/system-map.md`** (typed-state vocabulary): "membership at an exit type reads part
one's exclusion (`ShapeFree`, row 152), so an exit carried as a value keeps it"; "the typed state
reads a program node through the rounds of the program's expansion (`Eff.expandIn`, row 153): the
checker's object is the expansion, the run is the program's, redirected".

**`docs/STATE.md`**: "Wave 2 seat D1 (2026-10-01): rows 152 and 153 landed (`E4-TYPED-CE-017`,
`-019` repaired); row 117's side condition landed, its presence clause and part two measured and
stopped (owner); row 151 measured and stopped (owner; both refused shapes proved red)."
