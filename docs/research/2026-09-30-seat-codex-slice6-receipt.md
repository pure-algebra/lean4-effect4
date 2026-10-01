# Slice 6 implementation receipt

Item A is stopped by the brief’s regeneration fence: the new located refusal necessarily changes
`src/Effect4/Api/RunnerDerived.lean`, outside §6’s permitted generated paths. The repair is
preserved as a patch, not installed. Other items continue below; M5–M7 proofs remain outside scope.

Base: `74b526d4deb67b447a2ab6045f73b4e61adabf2d`, branch `codex/slice6-fixes`, worktree
`/Users/pooks/Dev/lean4-effect4-slice6`. Only this worktree is used. No pushes.
Brief precedence: original, addendum 1, addendum 2, addendum 3.

Finishing criteria: each item lands only after its named narrow builds and controls; runtime
changes include the required regenerated artifacts and OCaml checks. Every new theorem has an
axiom receipt at `[propext, Quot.sound]`. A stop-rule item records the decisive evidence and
smallest amendment, then the next independent item proceeds. Protected coordinator documents
remain untouched. The final receipt lists commit/file scope, exact commands/results, retained
counterexamples, bounded evidence, and open obligations.

## A — interim host-handle rule

**STOPPED under original §6. No A runtime change landed.** The exact generated diff is
`2026-09-30-seat-codex-slice6-evidence/A/runner-generated.diff`. `AdmitRefusal.internalHandle`
requires the Runner derived codec to add its constructor. The existing codec fails with missing
cases at lines 782 and 832. The prescribed `gen-derived` stage therefore cannot be byte-identical,
but §6 permits changes only to the four LCNF outputs and eff/wire/cas groups.

Smallest amendment: permit the generated `src/Effect4/Api/RunnerDerived.lean` change for the new
refusal and its producer acceptance fixture `tools/Effect4Gen/guards/runner.lean`; then rerun the
fixed generation order, remaining runner tests, dune, and `make check-ocaml`. No owner decision
about a legitimate internal-handle host row was needed.

The developed patch is `2026-09-30-seat-codex-slice6-evidence/A/implementation.patch`, against
base `74b526d4`. It contains all source/test paths plus the new HostHandleForgery battery and
register proposal. Only these own edits were restored after saving the patch, so later items
start from an unchanged runtime. The candidate generated output is saved separately and was not
installed or hand-edited.

The patch uses the generated type fold to scan raw answer/error types, preserving request types.
It refuses non-allocation success values with any handles, including at `unknown`. Failure arms
stay unchanged under addendum 1. ExternalContract retains its cell row, now refusing admission at
`["table", "1", "answer"]`, and expects the earlier `answerType` refusal for the dead cell.
The integer-refusal laws after the new check gain its successful-scan premise. Certificate
consumers in Run and the three session/run tests gain the new field.

Validation performed before restoring the patch:
- `LEAN_NUM_THREADS=1 lake build Effect4.Program.Admission Effect4.Program.Compile
  Effect4.Laws.Program.Admit Effect4.Laws.Program.Handles.Hooks
  Effect4.Laws.Program.CheckedTyping Effect4.Laws.Run Effect4.Laws.Api.HostSession
  TestSupport.AcquireHandle Effect4.Api.Runner`: the named modules individually built after local
  proof repairs (logs `narrow-build-1` through `-6`; the first is named `narrow-build.log`).
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Handles.Hooks
  Test.Counterexamples.Machine.Runtime.HostHandleForgery Test.Api.HostSessionContract
  Test.Api.KeyedHostContract Test.Api.ExternalContract Test.Api.AcquireHandleContract
  Test.Api.PackagesContract Test.Program.InvocationContract Test.Program.HostSpecContract
  Test.Program.LinkedRowsContract Test.Run.RunContract`: all the listed host/linked tests and
  Hooks built; the aggregate command failed on the stale RunnerDerived dependency of RunContract.
  `narrow-build-7.log` records the exact outcomes. RunnerContract was not run.
- `lake env lean -DwarningAsError=true /private/tmp/item-a-proof-axioms.lean`: exit 0, every one of
  the eight printed laws within `[propext, Quot.sound]`; source and output copied to `axioms.lean`
  and `axioms.log`. Four repaired admission laws are not yet separately axiom-printed.
- The manifest Runner command was obtained from
  `lake env lean -M4096 --run tools/Effect4Gen/Driver.lean --commands` and run with only its output
  redirected to the evidence candidate; exact argv in `runner-generation.log`, exit 0.
  `git diff --no-index` against the tracked output exited 1 and established the stop condition.
- `git diff --check`: exit 0 before saving the patch. No LCNF or OCaml check was attempted after
  the stop condition. The cache rebuilt a substantial dependency graph despite the copied cache.

The host tests are finite controls: 7 internal forms in both table columns, 11 nesting paths,
request/later-row controls, all 15 real host rows, certified live unknown-answer rejection with
stores unchanged, and honest scalar/fresh-allocation sessions. The general reply laws establish
handle-free input and either handle-free converted output or the exact newly allocated external
handle, separately covering closed failure images. None claims the parked runtime/Fits bridge.

Proposed register row E4-HOST-CE-007 is in the saved patch only; it must not be read as repaired
at the current branch head. No protected authority document was edited.

## B — answer-free M6 scope

**LANDED after narrow checks.** `NoHostAnswer` excludes only `answerAsync`; `RReachable`
requires it for every tape member. `AnswerOk` and `decision_preserves` are unchanged, and the
M6Ledger ceiling remains 20. The capstone docstring retains the four host-free refutations and
the pending shared-exit-judgment repair. This fixes E4-SCHED-CE-015 for host answers only.

Changes: `src/Effect4/Laws/Program/Typed/Assembly.lean`, `src/Effect4/Laws/Program/Admit.lean`,
`Test/Program/TypedStack.lean`, `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`,
`Test/All.lean` at the TrivialPosts anchor, and `Test/Counterexamples/REGISTER.md`.
Four requested SEEDED rows were added: E4-PROV-CE-005/006, E4-TYPED-CE-004, E4-SCHED-CE-016.
Their original witnesses remain under the committed pass directory. Proposed decision row 95:
M6 now counts host-answer-free tapes, with host-free repairs and all 20 proofs still open.

Commands from the slice6 worktree, with evidence under `2026-09-30-seat-codex-slice6-evidence/B/`:
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Typed.Assembly Effect4.Laws.Program.Admit`:
  exit 0; 366 jobs, ceiling 20 unchanged (`narrow-build.log`).
- `lake env lean -DwarningAsError=true Test/Counterexamples/Machine/Semantics/M6Capstone.lean`:
  final exit 0 (`M6Capstone.log`). The first run found a local timer-list proof simplification
  issue, fixed before the successful rerun (`M6Capstone.failed.log` is historical failure only).
- `lake env lean -DwarningAsError=true Test/Program/TypedStack.lean`: exit 0 (`TypedStack.log`).
- `lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/B/axioms.lean`:
  exit 0 (`axioms.log`). The new empty-table law and all eight counterexample/control theorems
  are within `[propext, Quot.sound]`, with no sorryAx in final output.
- `git diff --check`: exit 0 for the implementation changes. Stored unified patches in the A
  evidence naturally contain blank context lines; their whitespace is patch syntax.

The original capstone is refuted against a local copy of old reachability. The bad tape fails
the new premise. The four-decision clock tape meets it and actually exits successfully with
unit. These are finite execution controls plus exact statements about those controls; no
universal M5–M7 proof is claimed. No regeneration is needed for this proof-side item.

Commit ledger: `ca05788c` records A's stopped patch and evidence only, with all paths under
`docs/research/2026-09-30-seat-codex-slice6-{receipt.md,evidence/A/}`. The B commit follows it.


## C — fork ledger steps 3–5

**STOPPED before changing the runtime, under original §6's reader rule.** The precise extra
reader is `src/Effect4/Api/Supervision.lean:346`:
`#guard loaded.fibers.map RunFiber.origin = [.root]`. The plan §2 and the brief step-4 checklist
name the two runtime readers, the laws and three Test guards, but not this inline loaded-root
assertion. It also must move before the origin field can be deleted. `reader-census.log` records
the read-only search at `eca77d6a` (the B commit).

Smallest amendment: include this one inline loaded-root assertion in item C's reader checklist,
restating it via `originOf`. Its file is already in scope; no extra operational reader or live
fork creator was found. `RuntimeR.loadR` and the witness `spawnRoot` create roots only.
No ledger, comparison runner, reader migration or deletion landed, so there are no runner
counts or mutant results to report, and C's final regeneration/full check was not run.

Addendum 1's default-removal fallback also applies by static inspection: one laws file alone
has 37 calls omitting the site argument, more than the threshold of about 20 outside Machine
and Compile. `src/Effect4/Laws/Api/Supervision.lean` lines
270,277,285,294,301,309,318,340,349,358,367,376,386,396,405,413,422,445,458,467,477,486,496,506,
515,518,521,523,535,538,541,543,622,624,633,651,653: 13 spawn, 4 launchEntrant, 14 WithFiberAction
constructors, 6 FiberAction steps. This is a static lower bound, not measured compiler failures.
Keep the eight defaults when C resumes. The first three belong to WithFiberAction, despite the
addendum's shorter name. There is no proposed kind field.

D's ledger-dependent users and control move must remain held; its generic lifts and guard
re-derivation can be checked independently. Protected authority files remain untouched.


## D — generic lifts and slice 6 proofs

**PARTIAL: generic family landed; ledger-dependent users remain held by C.**
The generic module is `src/Effect4/Laws/Machine/Lift.lean`, namespace `Effect4.Machine.Lift`,
with exactly the three prescribed imports. It contains command-loop, decision and replay lifts,
the 13-field DecisionLift premise, frame law, and generic MachineEdits adapter for native facts.
No M6 instance was ported. The frame law is written against all 18 command constructors;
`parkedAt_em` retains its constructive proof. The native fold/reachability helpers sit beside
`Guard.Reachable` in Core, which imports Lift and makes the new module reachable from Laws.
No root-import anchor or core-root dependency was changed.

Lift step checks (evidence directory D):
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.Lift Effect4.Laws.Program.Guard.Core`:
  exit 0, 305 jobs (`lift-build.log`). Existing Core obligation ceilings unchanged.
- `lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/D/lift-axioms.lean`:
  exit 0, all 30 newly added theorems at `[propext, Quot.sound]` or less (`lift-axioms.log`).
- Static inspection: no forbidden first/try/simp_all or unrestricted hand simp in the new Lift
  module; no Guard or Typed import cycle, and no trace/M6 instances copied from the research file.

These are generic implications under explicit command/edit premises; they do not discharge the
M5–M7 statements. The guard replacement, native memo-id user, and its evidence follow below.
The trace user, four ledger facts, AgreesUpdates restatements, and forkedOf/Agrees move require C
and remain unlanded. M1Trace ceiling therefore remains 2. Row 94's three-user comparison is
not yet available.

Prior commit ledger: `eca77d6a` is item B; `4369c629` is the C stop receipt and census only.


### D guard re-derivation

The four driveState inductions in `Guard/Driver.lean` are deleted. Each contract field now
instantiates `driveState_lift_unit` at its invariant, using the existing per-command facts;
`driverContract` calls `driverContract_of_lift`. Its public statement is unchanged.

- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard.Driver
  Effect4.Laws.Program.Guard.Decision Effect4.Laws.Api.Guard`: exit 0, 344 jobs (`D/guard-build.log`).
- `lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/D/guard-axioms.lean`:
  exit 0; all six contract/helper theorems within `[propext, Quot.sound]` (`guard-axioms.log`).
- Same lean command for `D/dependencies.lean`: exit 0 (`dependencies.log`). Both the replacement
  and public contract reach the new lift and the per-command fact (4 positive controls), and
  reach none of the four removed inductions (8 negative controls). The removed names are also
  absent from the compiled environment. This finite meta-level walk includes types and
  `value? (allowOpaque := true)` theorem bodies; its first version spent its bound on duplicate
  queued names, corrected by deduplicating at enqueue. The successful run exhausted no bound.
- `git diff --check` for source changes: exit 0. No regeneration needed.

Proof-search note for row 94: this replacement composes explicit existing per-command proofs;
no new search bank or four separate induction proofs were required. It establishes only the
same guard contract. `75ee115c` is the preceding generic-lift commit.

### D native memo-id user

`src/Effect4/Laws/Program/Guard/MemoIds.lean` proves `steppedBy_memoIdsOk` and
`reachable_memoIdsOk`: on every native machine reached from Api.load by a raw decision prefix,
memo-map ids are distinct and below nextName. The claim fixes program/table/compile budget and
initial replies but permits arbitrary decisions and per-step budgets. **The reference machine
is not covered.** The existing `Laws/Program/Guard.lean` aggregate imports the new module, so
there is no orphan source or core-root dependency.

The proof covers all nine interpreter store hooks, plus direct native enterScoped and
exitScoped writes. The shared store view lemma transports exactly memo ids and the nextName
bound, not a generic store-order assumption. The outer decision proof instantiates
MachineEdits/machineFact_stepDecision, then reachable_lift_pure supplies the history step.

- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard.MemoIds`: final exit 0 (309 jobs,
  `D/memo-build-2.log`); `memo-build.log` records the first failed draft, whose copied record
  syntax and unresolved projection/search goals were repaired locally.
- `lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/D/memo-axioms.lean`:
  exit 0, all 46 new theorem checks within `[propext, Quot.sound]` (`memo-axioms.log`).
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard Effect4.Laws.Api.Guard`: exit 0,
  345 jobs (`memo-integration.log`). `git diff --check`: exit 0. No regeneration.

Row 94 evidence: explicit store-view, hook and state-projection lemmas support aesop assembly
in four places (withFiber, evaluatePrim, fireObserver and driveStep). The decision and history
lifts are composed by hand. No new bank or statement-generating command was added. There is
still no three-user comparison because the trace and ledger users are held at C.

D now has its generic family, guard re-derivation, and native memo-id user. The two ledger users,
AgreesUpdates, the trace-control move, and M1Trace ceiling reduction remain blocked by C's exact
reader-list amendment. `9dddff27` is the guard-replacement commit preceding this memo commit.

## F — closed layer build environment

**STOPPED under original §6 after successful Lean checks and LCNF generation. No F runtime
change landed.** The generator changed `ocaml/gen/closure-api_engine.tsv` and
`ocaml/gen/closure-api_gen.tsv`, outside the four permitted LCNF outputs and eff/wire/cas groups.
Each manifest has 6 added/5 removed lines: the new `Point.layerBuild` row, changed
`provideLayerWithK` row and affected declaration hashes. This is actual generated output,
not a predicted dependency. Exact diff: `F/generated-manifests.diff`.

Smallest amendment: allow these two accompanying closure manifests. Then apply the saved F
patch, complete the prescribed eff/wire/cas stages, build dune and run `make check-ocaml`,
including the prepared actual `errLeak` engine check. E4-PROV-CE-005 remains SEEDED at this head.
The whole developed source/test/generated patch is `F/implementation.patch`, based on
`e1c6a1fc`; `F/changed-paths.json` lists its paths. Only those own edits were restored after
saving it. The generated ML outputs are included in the patch, never hand-edited.

The patch closes both native/reference layer build entries via `Point.layerBuild`, preserving
the program body's environment and the service context. It adjusts the five affected source
files and adds `LayerEnvironment.lean`, plus an OCaml engine assertion for both Fast and Ref
carriers. The Test import uses the same reserved runtime slot after LiveStack, because stopped
A has not installed HostHandleForgery. The OCaml assertion is prepared but has not run.

Evidence under `2026-09-30-seat-codex-slice6-evidence/F/`:
- Before and after manifests: `LEAN_NUM_THREADS=1 lake env lean -M4096 --run
  harness/truth/Truth.lean <truth-before/after.json> --tapes harness/truth/tapes`, and the same
  driver `--corpus <corpus-before/after.json> 400 4`. All four exit 0. Exact paths appear in
  baseline.log/after.log. `run-comparison.log`: 37 truth fixtures and 400 random depth-4
  programs; no run or runSync value changed. This is finite evidence only.
- Narrow source build: Compile, DenoteR, Agreement, Handles.Hooks, Intro.Scope, Intro.Memo,
  Guard.RaceSites, RuntimeR: exit 0, 356 jobs (`narrow-build.log`).
- RuntimeRContract, ProvisionContract and LayerSharingContract passed (`tests-build.log`).
  The first LayerEnvironment version exhausted memory (compiler exit 137). It was repaired
  to use executable guards for concrete runs and a separate general fiber-exit agreement
  law, retaining all outcomes and both local settings of the two extra controls.
- `LEAN_NUM_THREADS=1 make gen-derived gen-lcnf`: exit 0 (`regenerate.log`). Its prerequisite
  full build passed 721 jobs; LayerEnvironment passed in 1.4 seconds. The module/axiom gate
  checked 500 modules and 68495 declarations at its declared semantic/test ceiling.
  All seven new battery theorem axiom prints are within [propext, Quot.sound]. Derived output
  stayed unchanged; api_gen.ml, api_engine.ml and their two manifests changed.
- `lake env lean -DwarningAsError=true .../F/axioms.lean`: exit 0; all three Point helper
  theorems have no axioms (`axioms.log`). Source `git diff --check`: exit 0. Generated
  api_engine.ml line 9441 has a trailing blank-space line; retained exactly as generated.
- `bun install --frozen-lockfile` in this worktree's ts/eff: exit 0, 19 packages; lockfile
  unchanged (`bun-install.log`). No dependency installation touched the main checkout.

Stopped before gen-eff/gen-wire/gen-cas, dune and make check-ocaml. No OCaml runtime result or
host conformance is claimed. The run comparison does not establish unrestricted equivalence.
Proposed row 104: source repair verified and preserved, landing held only by the two manifest
paths plus the remaining target checks. No protected coordinator document changed.

## G — layer values and provision fixtures

**STOPPED under addendum 2's G rule, with addendum 3's two exceptions applied.** A third
in-tree fixture changes: `Test/Program/AuthorContract.lean:267–268` expects
`Api.checkLayer (Layer.value Counter.key (str "x"))` to succeed. Counter is declared at nat;
this authored expression elaborates to an effect leaf returning a string. It is distinct
from leftWins/rightWins and from the reported gap programs.

`G/AuthorContractProbe.lean` imports the actual test module, proves that exact elaboration,
its present acceptance, and its rejection by G's revised effect-leaf equation as
`valueNotSubtype Counter.key string nat` at `[]`. The body check remains the original checker
at empty environment/path `[0]`; that body has no layer. The probe also pins why replacing
this with a synthetic string succeed leaf would be inaccurate: that leaf is already refused
by literalOutsideAlphabet. This is a checked change to one concrete program, not a scan claim.

Command: `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true
 docs/research/2026-09-30-seat-codex-slice6-evidence/G/AuthorContractProbe.lean`.
Exit 0; all eleven axiom prints are within [propext, Quot.sound] (`G/probe.log`).
No checker, judgment, fixture or register edit was installed, and no corpus regeneration was
run. E4-PROV-CE-006 remains SEEDED.

Smallest amendment: add this one AuthorContract guard to G's fixture exceptions and expect
its located valueNotSubtype refusal. Preserve the nearby positive string-carrier Greeting
fixture at lines 290–292. Then implement the already specified checker/judgment changes,
move leftWins/rightWins, run the named laws/tests and regenerate the corpus index.
Proposed row 105: include the third fixture in the bounded change list. No protected document
changed; `8065fd64` is the preceding F stop/evidence commit.

## E — Fits membership

### E1: the new module beside the old judgments

Membership is constructor-complete for the actual value encoding, with Equiv invariance,
native cell/deferred spellings at nat, table-based liveness, and declared liveness at unknown.
`fold_of Effect4.Program.Typed.Fits` targets the recursive judgment itself and generates the
algebra, homomorphism and equality connector. `cleanExit` moved unchanged from Admission;
Admission imports Membership, making the new file reachable without a root-import edit.
The old judgments and all their callers remain in place at this first commit.

- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Typed.Membership`: exit 0, 360 jobs;
  new module itself built in 1.0 second (`E/membership-build.log`). Dependencies rebuilt
  after restoring F's stopped runtime change.
- `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/E/membership-axioms.lean`: exit 0;
  all 37 named laws plus Fits.alg, Fits.hom and Fits.eq_cata within [propext, Quot.sound].
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Typed.Admission
  Effect4.Laws.Program.Typed.Residual Effect4.Laws.Program.Typed.Stack
  Effect4.Laws.Program.Typed.Assembly`: exit 0, 366 jobs (`E/coexistence-build.log`).
  Existing M3bWorld ceiling 3 and M6 ceiling 20 unchanged at this stage.
- Source `git diff --check`: exit 0. No runtime or generated-output change.

Changed files for E1: Membership.lean, Admission.lean and this receipt/evidence.
The preceding stop commit is `1d8ef8e1`. Cutover, test migration and retirement follow below.

### E2: source caller cutover

The four modules Admission, Residual, Stack and Assembly now use Fits/FitsExit/FitsCause and
ServicesFit. Fits is applied in its native `(world, value, type)` order. The old definitions
remain beside them temporarily for the test migration; they are no longer the production
judgments. The runtime checker/twin and its bridge remain parked.

The eight prescribed body changes are exactly Admission's strongExit_success,
strongExit_of_clean and cleanExit_of_never; Residual's strongValue_bool_true, strongExit_bool
and settling_fork; Stack's strongExit_failure_of_error and popR_typed. Two new binder-exact
adapters, strongValue_mono and strongExit_mono, close the corresponding M3bWorld obligations.
The obligation audit checks 6/6 binders for both, exact true, zero mismatches; the remaining
residual-program weakening obligation keeps ceiling 1 (from 3). M6 remains 20 open.

- Separate `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Typed.<Module>` runs in order
  Admission, Residual, Stack, Assembly: all exit 0 (`E/cutover-build.log`).
- `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/E/cutover-axioms.lean`: exit 0; all eight
  repaired bodies and both new adapters within [propext, Quot.sound].
- Source `git diff --check`: exit 0. No additional existing source proof body outside the
  measured eight changed. No M5–M7 proof or regeneration was added.

E1 is `5e142337`. This commit owns the four cutover modules and receipt/evidence. Existing
Test callers are migrated in E3; this intermediate commit records the narrow law build only.

### E3: tests and retained falsifiers

The eight named existing test files were checked; seven required edits and AdmissionCensus
was byte-identical. B's M6Capstone also moves to FitsExit. ValueMembership retains a local
copy of the old source/control/state predicates, the old load refutation, G1–G6 with their
new refusals and honest controls, and the equality-invariance G7 refutation. Its production
controls prove typed loaded states for Ref.make(5) and Ref.make(5).flatMap(Ref.get).
These are two concrete program controls, not the general M5 obligation.

The old predicate block is byte-identical to its selected pre-E spans (audit and SHA-256 in
`E/tests/audit.md`); a local World alias resolves imported-name ambiguity without changing it.
The bridge `live_iff_handlesLive` connects production Live to Reviewed.HandlesLive under
WorldValid, in Test where the retired model is retained. No old judgment remains needed by
Membership. The existing heap-extension bank positive and negative controls are retained.

- `LEAN_NUM_THREADS=1 lake build Test.Program.TypedControl Test.Program.TypedResidual
  Test.Program.TypedStack Test.Program.LoadedAdmission Test.Program.AdmissionCensus
  Test.Counterexamples.Machine.Semantics.AsyncHookContract
  Test.Counterexamples.Machine.Semantics.TrivialPosts
  Test.Counterexamples.Machine.Semantics.M6Capstone
  Test.Counterexamples.Machine.Semantics.ValueMembership`: final exit 0, 382 jobs
  (`E/tests-build-2.log`); ValueMembership built in 1.9 seconds.
- First run (`tests-build.log`) found imported World/Fits name ambiguities and an explicit
  argument supplied to an implicit List membership lemma. Those elaboration errors and their
  cascading recovery axioms were fixed before the successful run; they are not proof evidence.
- Every printed theorem in the successful test log stays within [propext, Quot.sound], with
  no sorryAx or Classical.choice. The old-load red, six paired controls, G7, liveness bridge,
  both loaded-state greens and the proof-search controls all pass.
- Source `git diff --check`: exit 0. No regeneration.

E4-TYPED-CE-004/005/006 are marked REPAIRED with their exact controls and the general-M5 limit.
Test/All imports ValueMembership immediately after M6Capstone, the reserved semantic slot:
stopped G has not installed LayerValue, whose future import belongs immediately before it.
`c1bcfdf6` is E2. This commit owns the changed Test paths, register, receipt and test evidence.

## H1 — command queue conditions
Pending.

## H2 — shared exit judgment, probe first
Pending.
