# Slice 6 implementation receipt

## After addendum 5

**The one thing first.** The audit, A, and all three C steps are complete. C step 5 is
integration-ready: the old fiber field and its comparison runner are removed together, the
Lean and OCaml paths read/write the machine ledger, generation is current, and the required
OCaml and repository checks pass. The owner authorized the additional prelude/test readers,
two closure manifests, and explicit ForkRecord type root as recorded below. D's held users
follow, then F, G, H1, and H2 part one. H2 excludes only badName and notImplemented;
missingService waits for part two. Nothing has been pushed.

Authority read from the main checkout:
`/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-codex-brief-slice6-addendum-5.md`,
commit `56da0e1edeefc97ce878afaefe34ca702f86c35f` (hash receipt under
`2026-09-30-seat-codex-slice6-evidence/after-addendum-5/authority.json`). It is not merged into
this branch; the coordinator owns that merge. Rows 111–117 are not implementation work here.
The After-addendum-4 and first receipt sections below are retained as checkpoint history.

### C — additional OCaml reader, stop lifted by the owner

The Lean deletion and focused dependency repairs pass, including the two repaired race bodies
at `[propext, Quot.sound]`. `make gen-derived` then passed, including its 724-job full
prerequisite build. Derived output was byte-identical. The earlier failed build and the focused
332-job repair build are retained in C evidence. The two new
mechanical repairs are the generated frame-rule count fixtures (one old fiber field disappears,
one ledger field appears) and two unchanged race statements proved by explicit launch cases.
They are not extra origin readers.

The actual extra reader is `ocaml/engine/test/test_engine.ml:545,551,560,566`: Fast and Ref
fetch raw fiber records with `I.fibers` and inspect `parent.origin` / `child.origin`. The
handwritten `ocaml/engine/tools/api_engine_prelude.ml:99–106` still constructs the old fiber
field; `sh_api_load` passes `Origin_root` at :117, and `sh_spawn` / `sh_spawn_generic` pass
`Origin_forked` at :136–137 and :162–163. Both spawn substitutions advance fibers and next_id
without a ledger append (:139–142, :165–168). `ocaml/engine/externs.txt:88–90` makes those
substitutions actual engine behavior. Regeneration alone cannot repair this handwritten source.

**Owner amendment, 2026-10-01:** “Yes—finish C with this amendment.” Include the prelude's load/make/spawn transcriptions and the four
Fast/Ref creation-provenance assertions in C's checklist. Remove the fiber-origin argument,
append the exact ForkRecord at both spawn substitutions, and make the assertions inspect the
machine ledger (root has no record; child retains parent, daemon and exact site). Keep the
same independent Fast/Ref controls and prescribed producer/OCaml checks. The extern map is unchanged. Subsequent generated-path and producer-input amendments are
recorded separately below.

### C — two additional generated manifests, stop lifted by the owner

`make gen-lcnf` completed the fibers, machine and API-oracle cuts, then was interrupted
(exit 130) before the engine cut completed, upon observing two additional generated paths:
`ocaml/gen/closure-fibers_gen.tsv` and `ocaml/gen/closure-machine_gen.tsv`. The first changes
67 existing rows and the second 9; declaration names/counts are unchanged. These are the
producer's own closure statistics/hashes for the changed record layout and spawn body.
The exact diff and keyed row inventory are `C/additional-manifests.diff` and `.json`.
No generated output was hand-edited.

The original §6 generated-path stop and addendum 5's “No other generated path is permitted”
required a further explicit amendment. **Owner ruling, 2026-10-01:** “Yes—include both
generated manifests.” These two companion manifests are permitted as
producer outputs of C, like the already allowed API manifests. Rerun the prescribed
LCNF stage before eff/wire/cas and the named checks. The second LCNF run completed the interrupted engine cut. Its subsequent OCaml build
exposed the separate producer-input amendment below.

### C — engine type root, measured producer amendment

All five generation stages passed. `dune build` then failed at the approved spawn
transcription: the engine producer emitted `fork_record = Placeholder_fork_record` rather
than its record fields. Both spawn definitions are replaced by the handwritten prelude, so
the producer does not see their constructor. The explicit type-root list already handles
`Origin` for this reason. The proposed amendment adds exactly `Effect4.Machine.ForkRecord`
to the engine entry in `ocaml/gen/roots.json`, keeping all other fields unchanged.
`C/roots-amendment.patch` is the exact change; `C/dune.log` and its command/result JSON
retain the compiler evidence. This new producer-input path awaits the owner under §6's
scope stop. **Owner ruling, 2026-10-01:** “Yes—include the ForkRecord type root.”
The exact proposed recipe change is now authorized and applied; regeneration and checks resume.

### C — step 5 complete

Base: `e5cc184ba820ab4ea79b38fd32820421514812b9`. The commit containing this section
is C step 5. `C/step5-paths.json` lists its exact implementation paths and `C/step5-source.patch`
retains the source diff. The eight site defaults remain as ruled. No second origin owner remains
in Lean or the handwritten engine. The `Origin` result alphabet remains available to the API.

The comparison runner's final execution was at that exact base (`runner-at-step4.commit.txt`):
8,594 programs, 34,376 runs, 189,068 decision boundaries, 348,162 member comparisons,
zero mismatches; all three ledger mutants were rejected. Its source and Test/All import are
retired in this same commit as `RunFiber.origin` and the constructor argument.

Verification, one Lean process at a time, `LEAN_NUM_THREADS=1`:
- The deletion's focused builds pass (`delete-narrow-1`, `delete-broad-repairs`). Both repaired
  race statements retain their statements and print only `[propext, Quot.sound]` (`step5-axioms`).
- Full producer order passed: derived (`gen-derived-2`), LCNF (`gen-lcnf-3`), eff/wire/cas
  (`post-root-generation`). The four LCNF outputs and their four manifests are the only
  generated diffs. The failed/interrupted intermediate runs remain alongside the final logs.
- `opam exec --switch=effect4 -- dune build`, inside `ocaml/`: exit 0 (`dune-2`).
- `opam exec --switch=effect4 -- dune exec engine/test/test_engine.exe`: exit 0; 80 checks,
  including all four Fast/Ref root and exact child-provenance assertions (`engine-test`).
- `make check-ocaml`: exit 0. The three-engine differential covers 472 programs, 2,960 tapes,
  65,712 positions and 131,424 projection comparisons, with zero divergences, profile-refused
  tapes or raised tapes. The independent seam/prelude checks also pass (`check-ocaml`).
- `make check`: exit 0 (`make-check`): 724-job build, fresh Test/All root, library/test closure
  and axiom gate, and regenerated-file drift. The semantic/test ceiling remains
  `[propext, Quot.sound]`; the gate's existing exact implementation exceptions are unchanged.
- Implementation whitespace checks: exit 0 (`git diff HEAD^ HEAD --check -- src Test ocaml`).
  Raw retained compiler logs and diff artifacts include emitted trailing whitespace; the
  all-artifact check reports that whitespace, and those evidence bytes are retained unchanged.
  Generated outputs were explicitly staged
  before the drift gate, whose comparison is against the index; regeneration changed none of
  those bytes. No generated output was edited by hand.

`C/check.py` and each `.command.json` / `.result.json` retain exact argv, cwd, environment,
exit and elapsed time; earlier generation uses `C/run.py` with command/result text files.
These execution comparisons are finite evidence. D still owes the general reachable ledger
facts and trace agreement; C does not claim them from the runner or backend differential.

### D — trace user and named bank

Base: C step 5, `f05a6acec7f52c91efa717739b9afb87b729e16b`. This commit supplies the
native trace-agreement user. The ledger user and diagnostic module move follow separately.
The already landed generic lifts, guard re-derivation and memo-ID user are unchanged.

The observation is the ordered list of parent/child/daemon triples in the fork events and
ledger. Source paths are absent from the events. Agreement does not establish semantic
correctness of the recorded parent or flag. Emission requires an explicit no-fork condition;
spawn appends the same triple on both sides. All eighteen native commands and all eight
outside-loop edits feed the existing loop/decision/history lifts. The final theorems have
no per-command, admission or typed-state premise. The four AgreesUpdates fields hold for
any input machine satisfying agreement. There is no reference-machine or M6 instance.

Verification is under `after-addendum-4/D/`, via `check.py` command/result JSON:
- The trace candidate passes (`trace-3`), with 69 theorem dependency reports at the ceiling.
  The first two failed drafts are retained; repairs only add required type annotations,
  exact intermediate states, and the explicit safe emission rule to the named bank.
- Production `lake build Effect4.Laws.Api.TraceOrigin`: exit 0, 312 jobs
  (`trace-production-1`). `TraceFacts.M1Trace` is now **0 open, 3 proved**, ceiling **2 → 0**.
- All 72 authored production theorem declarations print at `[propext, Quot.sound]` or less
  (`trace-production-axioms`). This includes the bank positive and original obligations.
- The omitted-bank fixture first failed as intended; its exact diagnostic is now captured
  under `#guard_msgs (error)`. The fixture and direct Supervision consumer build pass
  (`trace-bank-red`, `trace-tests`, 315 jobs). The named-bank positive uses the exact same
  proposition.
- Row 94 measurement (`trace-census`): plain aesop closes **23/76** inspected statements,
  and aesop with StepInv closes **20/76**, within the census's default per-goal budget.
  The denominator includes generated projections. This is not a claim that enabling the bank
  improves every statement. The targeted emit positive requires it; native case analysis and
  history-wrapper selection remain written by hand. No statement generator is introduced.
- Source/test whitespace and forbidden-tactic scans pass. No generator was required.

The independently checked ledger draft has 77 theorem dependency reports: 27 require no axioms
and 50 use only the permitted ceiling. It remains a checked draft until the next production
commit; this trace commit does not claim its integration.

### H2 — part-one exclusion clarified by the owner

Addendum 5's “The judgment” requires `NoShapeDefect ty ex` to exclude `missingService` when
`ty.requires` is empty, and sends that judgment through the saved-stack contract. Its part-two
section simultaneously holds the contract amendment needed to transport this same clause.
The already checked `AuditH2.loop_admitted`, `output_eq`, and `output_bad` refute that full
transport at the current contracts. This is a contradiction in scope, not a prediction of a
ninth compiler failure. The eight-body PartOne harness and its named repair plan deliberately
exclude only `badName` and `notImplemented`; they do not implement the full conditional clause.

**Owner clarification, 2026-10-01:** “Yes—two defects in part one; missingService waits.”
The user approved the following exact clarification: part one keeps `ExitOk w ty ex` and the signature-free
`NoShapeDefect ty ex` interface, but the latter ignores `ty` for now and excludes only
`badName` and `notImplemented`. The conditional `missingService` clause remains part two,
with row 117's contract amendment. The eight-body cap, clean-failure premise, local lemmas,
controls, and no-ninth-repair rule remain exactly as addendum 5 states. This resolves the
wording conflict; H2 part one remains in queue after H1. The full clause is not silently retained.

**Proposed register row, not written to the register:**

| ID | Status | Claim under attack | Witness | Next action |
| --- | --- | --- | --- | --- |
| `E4-TYPED-CE-008` | SEEDED 2026-10-01 | The frame contracts transport `missingService` across a change in the requirement row | `docs/research/2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean`: `AuditH2.loop_admitted`, `output_eq`, `output_bad`; logs in that audit | A never-answer loop frame accepts the failure at a nonempty requirement row and returns it unchanged at an empty row, where the full exclusion refuses it. Row 117 holds a frame/operation contract amendment with scoped/provision positive controls. This is a saved-frame witness, not a reached-run claim. |

## After addendum 4

**The one thing first.** The model-probe audit is committed at
`2d27419eab723f265e718a0f7a82708f560c04a2`. Item A landed at `90df5d21a4d33ad9d5330e090ea102024a318d66`. C step 3 is committed at
`be6631ab`; step 4 now passes its reader/relation checks. **C is not integration-ready:** the
old origin field remains and the engine has not been regenerated. C step 5 and D's held users,
then F, G and H1, remain in that order. H2 and proposed D1–D6 remain held for the coordinator. Nothing has been pushed.

Continuation base: `f437b066` (the tracked audit brief), then audit commit `2d27419e`.
Branch/worktree: `codex/slice6-fixes`, `/Users/pooks/Dev/lean4-effect4-slice6`.
Finishing criteria remain those of the original receipt: each item lands only after its named
checks; a proved stop records the smallest amendment and the next independent item proceeds.
The first receipt is preserved below as history, not current status.

### A — host-handle rule, after the codec amendment

The original A implementation patch is applied, with its register row and the producer guard
for the new refusal. The generated Runner codec now includes that constructor. The host table
scan examines raw answer/error types, including nested types; requests stay outside this rule.
Accepted non-allocation success replies carry no handles. The external allocation exception
still constructs the new external handle. Closed failure payloads remain governed by the
existing error alphabet, as addendum 1 requires.

Changed paths are enumerated in
`2026-09-30-seat-codex-slice6-evidence/after-addendum-4/A/changed-paths.json`.
The exact generated diff is alongside it. Regeneration changed only RunnerDerived and the
API oracle/engine outputs with their two closure manifests. **Scope interpretation:**
addendum 4 explicitly permits `closure-api_gen.tsv` and `closure-api_engine.tsv`; this queue
uses that permission for these exact generated paths, including A's changed `externalValue`
closure. Their changes are 5 added/6 removed rows each. This does not permit the other two
closure manifests or arbitrary generated paths.

Verification (all commands run in the designated worktree, `LEAN_NUM_THREADS=1`):
- `make gen-derived gen-lcnf gen-eff gen-wire gen-cas`: exit 0, in that order
  (`regeneration.command.txt`, `regeneration.log`, `regeneration.result.txt`).
- The first `make gen-derived` reached the known stale Runner codec during its prerequisite
  build and failed only that target. The existing Driver/Main producer then regenerated the
  codec, allowing the prescribed full sequence to run. `bootstrap_runner.py` records the exact
  producer route; its first attempt lacked the driver's backslash normalization, failed, and
  was corrected before `bootstrap-fixed` passed. No generated bytes were hand-edited.
- The seven-module narrow build and all eleven requested host/session/runner/program tests
  passed, including the previously unrun `RunnerContract` and `RunContract`.
- All twelve axiom prints passed at `[propext, Quot.sound]` or less, including the four
  admission laws called out in addendum 4 (`axioms.lean`, `axioms-1.log`).
- `opam exec --switch=effect4 -- dune build`, inside `ocaml/`: exit 0.
- `make check-ocaml`: exit 0; the differential and engine checks passed.
- `git diff --check` on the implementation: exit 0. An independent source/test review found
  no concrete bug or missing required case.

`checks.py` and `checks-results.json` retain every exact command, working directory, elapsed
time, exit status and log. The host/session controls and OCaml differential are finite tests;
they do not establish the parked runtime-to-Fits bridge. The general reply laws are separately
axiom-checked. `E4-HOST-CE-007` is REPAIRED by this landing. Row 97's authority update remains
the coordinator's. No protected authority document changed.

### C — step 3, ledger beside the old field

Base: `90df5d21a4d33ad9d5330e090ea102024a318d66`. The step-3 commit contains the ledger,
its reader, local append/lookup laws, the comparison runner and this receipt. `spawn` writes one
record beside the existing child append and event emission. Roots have no record. `originOf`
first tests fiber membership; a missing fiber has no origin, while a member without a record is
root. The old field remains the independent comparison value. The eight site defaults remain;
the 37 callers required by the fallback are listed in the original C section below.

The source changes are `Machine/Fibers.lean`, new `Laws/Machine/ForkLedger.lean`,
`Laws/Machine/Clauses.lean`, `Laws/Machine/Handles.lean`, and the new-law import in
`Laws/Api/Supervision.lean`. The test changes are `Test/Api/ForkLedgerRunner.lean` and its
`Test/All.lean` import. The Handles helper changes only generalize exact record updates over the
new, unobserved ledger field; no additional origin reader or fork writer was found.

Evidence: `2026-09-30-seat-codex-slice6-evidence/after-addendum-4/C/`. `run.py` retains exact
argv, worktree, result and output for each command, with `LEAN_NUM_THREADS=1`.

- `lake build Effect4.Laws.Machine.ForkLedger Test.Api.ForkLedgerRunner
  Effect4.Laws.Api.Supervision`: exit 0 (`beside-build-final`, 320 jobs).
- `lake env lean -DwarningAsError=true Test/Api/ForkLedgerRunner.lean`: exit 0
  (`runner-final`). **8,594 programs, 34,376 runs, 189,068 decision boundaries, 348,162 member
  fiber comparisons, zero mismatches.** All three ledger-only mutants were rejected: dropped
  site, flipped daemon flag, changed parent. The old field stays unchanged in each control.
- Required root, ordinary/scoped/explicit-scope, missing-scope, race, finalizer, multiple-fork
  and merge fixtures pass. Exact merge records include two layer-build forks followed by three
  cleanup forks. `MergeSites.lean`/`merge-sites.log` retain the finite diagnostic that corrected
  the first fixture expectation.
- `lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/C/local-axioms.lean`:
  exit 0. All nine public ledger laws and the changed `spawn_eq` are at `[propext, Quot.sound]`
  or less (`local-axioms.log`). Append equality is unconditional; lookup of the new child has
  the explicit freshness premises. Bounds imply the record's fresh lookup. These are general
  laws, separate from the finite runner. Whole-run uniqueness, bounds and correspondence remain
  D's held work; this checkpoint does not claim them.
- `git diff --check`: exit 0 before commit. Earlier failed drafts and builds are retained as
  development history: record layout/type annotations, old exact-record proof rewrites, and
  the two incomplete merge fixture expectations were repaired before the final runs.

No generator, OCaml check, full battery or `make check` was run for this beside checkpoint;
step 5 owns those checks. The comparison runner must retire in the same commit as the old field.

### C — step 4, readers and relations

Base: `be6631ab`. All amended checklist readers now use the machine ledger. The old fiber field
and its comparison runner remain until step 5. `readers-census.log` shows only that runner and
mechanical make-argument plumbing still using the old field (Codegen's unrelated `Origin` is
unchanged). There is no additional operational reader or fork writer.

`originEntries` is now the ordered **fork-only** ledger projection; roots are absent there.
`load_origins` separately proves both the empty ledger and the root's `originOf = some root`.
Append/source statements remain unconditional append statements. The source allocation bridge
also has a separate exact lookup law with explicit fiber and record freshness. World Γ freshness
is not silently used as runtime freshness. Fresh-child status requires a fresh record lookup;
existing member status uses the distinct allocated id. These statements do not claim lookup/field
agreement for an arbitrary detached fiber value.

The book and native/reference relation compare the complete machine ledger. FiberControl no
longer stores origin. `bookMeans_controls_forks` names the combined control-and-provenance
observation; exit/store observations and trace exclusion are unchanged. Mechanical relation
consumers in Simulation and RuntimeR moved with that signature. The guard's exact `spawn_machine`
equation includes the record append, with a separate lemma that GuardState ignores provenance.
No guard condition or typing judgment was weakened.

Changed implementation paths are in `C/step4-paths.json` (paths relative to this worktree).
Commands in `C/`:
- `lake build Effect4.Laws.Api.Supervision Effect4.Laws.Program.RuntimeR
  Effect4.Laws.Program.Typed.ForkSource Test.Api.SupervisionContract`: exit 0, 367 jobs
  (`readers-2`). The first run exposed only the exact-machine construction in `spawn_rel`;
  the explicit fork-field transport fixed it.
- `lake build Effect4.Laws.Program.Guard.Core`: exit 0, 305 jobs (`readers-guard-final`).
  Earlier guard-dependency logs retain the exact-record equation and elaboration repairs.
- `lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/C/readers-axioms.lean`:
  exit 0. All 22 printed new/restated laws are at `[propext, Quot.sound]` or less.
- The affected origin gates have zero open obligations: API 18 proved, Book 2,
  Simulation/Fibers 6, Simulation/Actions 10, Guard 18, ForkSource 2.
- `git diff --check`: exit 0 for implementation/receipt paths.

D research preparation is retained without claiming it landed: `InvariantCandidate.lean` passed
as `invariant-4` after its generic allocation/transport lemmas were repaired. Its command-level
premise is explicit. `InvariantFullCandidate.lean` adds an **uncompiled** concrete native command
candidate. Neither is the required whole-run proof yet. There is no new library invariant or
StepInv bank at this checkpoint, and no generated change.

## First receipt — historical status before addendum 4

Do not merge this as a completed slice 6. B, the independent parts of D, and E are implemented
and narrowly verified. A, C, F, G, H1 and H2 stopped under the brief's rules; D's ledger-dependent
work remains held by C. H1 found a new observer-to-token typing gap, and H2 reached the eight-body
repair limit. The stopped A/F repairs are preserved as patches, not installed. M5–M7 proofs remain
untouched. The required amendments and evidence are recorded below.

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

The seven files named by E and B's M6Capstone were checked; seven required edits and
AdmissionCensus was byte-identical. M6Capstone also moves to FitsExit. ValueMembership retains a local
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

### E4: retirement complete

Removed HandlesLive, ServicesOk, HandlesFit, StrongValue, StrongCause and StrongExit from
production Admission. No production source mentions those retired judgment names. Their
reviewed copies and the WorldValid liveness bridge remain in ValueMembership. Two source
introductory comments (Typed.World and Typed.ForkSource) now use the current vocabulary;
Assembly no longer lists the repaired liveness obstruction among current M6 refutations.
The still-open layer, queue and shared-exit limitations remain explicit.

- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Typed.Assembly` with the same nine
  Test targets listed in E3: exit 0, 382 jobs (`E/retirement-build.log`). Every printed
  theorem remains within the ceiling; no recovery or Classical.choice axiom appears.
- `rg` for the six retired names under `src/Effect4/Laws/Program/Typed`: zero matches.
  Source `git diff --check`: exit 0. No runtime change or regeneration.

`602ab157` is E3. E4 owns Admission, Assembly and the two comment-only source changes,
plus receipt/evidence. E is now complete within its dispatched scope: the 37 membership
laws, fold connection, eight source proof repairs, two checked obligation adapters, test
migration, three register repairs, and retirement have all been checked. M3bWorld has one
remaining obligation; M5 initialization and all M6 command proofs remain open.

Proposed row 96: Fits with D1–D4 is the production value judgment; the equality experiment and
old definitions are Test controls only. The runtime twin and host-reply-to-Fits bridge stay
parked. The two concrete loaded-state proofs do not claim the general initialization theorem.

## H1 — command queue conditions

**STOPPED under original §6: a checked new counterexample refutes the proposed step_observe
statement, even with all of addendum 3's queue conditions. No H1 source change landed.**
`H1/ObserveGap.candidate.lean` retains the proposed queue/step statements locally and proves
`proposed_step_observe_false`. All eleven printed theorems pass the axiom ceiling.

The witness has the checked pure-unit program, its loaded reference machine with nextToken 1,
and an initial world extended with the historical declaration Θ(root,0) = unit. It proves
WorldValid and TypedState, the internal-key bound, and every proposed queue field for
`observe root (success unit) (resumeAwait root 0 awaitValue)`: source exit typing, authority,
unique owners, key bound, external-key exclusion and code-site condition. The command emits
`resume root 0 (pure (success (reifyExitVal (success unit))))`. The resulting encoded exit is
not unit, so ResumeOk rejects it in every later world: world extension cannot change token 0's
declared type. Thus the proposed step cannot keep the queue typed.

This is a constructed typed state, not a reached run. There is no active park, and executing
that stale resume would be inert. The refutation concerns the required unconditional typing
of every queued command; it does not claim an observed runtime result is mistyped. The proof
quantifies over any proposed reference resume-code-site predicate: the input observe command
has no code field, so no disputed continuation scan can repair this witness. Factoring the
internal bound into TypedState rather than as a separate conjunct does not remove it.

Smallest amendment: require an observer's emitted result to fit the waiting token, including
awaitValue's encoded-exit conversion, before admitting that observe command. An alternative
would amend how inert resumes are typed, but that changes the all-commands requirement and
needs an explicit ruling. Inspect the other observer modes under the same connection before
dispatching step_observe. No extra condition has been silently installed to evade the stop.
Propose a new register row for this observer-to-token mismatch; CE-016 remains SEEDED and
CE-017 has not been marked repaired.

Checked commands (all from this worktree):
- `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard.Core
  Effect4.Laws.Program.ReasonsR`: exit 0, 346 jobs (`H1/dependencies.log`).
- `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/H1/PendingBelow.candidate.lean`:
  exit 0; pending_below within [propext, Quot.sound] (`pending.log`). This confirms the
  pending-token question without an added bound, but the law is preserved in evidence only.
- Same command for `H1/ObserveGap.candidate.lean`: exit 0 (`observe.log`); all eleven
  checks within [propext, Quot.sound], no recovery axioms.

`H1/GuardCore.candidate.diff` and `draft-notes.md` retain the proposed generic helpers and the
18-command condition matrix, uninstalled and uncompiled. Existing requestOfR can be reused;
registrationDone must inspect the reference raceRegister operation, since interpR.parkOf
always returns none. The recursive reference code-site scan remains a named open design
point; blindly quantifying over every continuation answer would strengthen the native rule.
Rows 106 and the command ledger remain open; no M5–M7 proof was started. E4 is `0c1e9915`.

## H2 — shared exit judgment, probe first

**STOPPED under addendum 3's part-one cost rule. Eight existing proof bodies require changes;
no H2 production change landed.** The successful baseline and the mechanical part-one probe
use the same fresh namespace and the same 67 copied theorem regions. The baseline compiles;
the part-one probe fails in eight distinct bodies, with no errors outside theorem regions.
The two failure sites in popR_typed count once. This is a measured lower bound on required
repairs, not eight completed repairs or a claim that all remaining proofs would pass after them.

| Module | Existing bodies requiring repair |
| --- | --- |
| Admission | strongExit_success, strongExit_of_clean, cleanExit_of_never |
| Residual | strongExit_bool, settling_fork, strongExit_mono |
| Stack | strongExit_failure_of_error, popR_typed |

Seven bodies predate E; strongExit_mono is the adapter added in E and is now an existing body
on this branch. It is counted, not hidden as a mechanical rename or a new helper. The probe
makes 59 mechanical FitsExit-to-ExitOk substitutions and adds the two part-one definitions;
no existing proof body was repaired. Membership's base FitsExit remains unchanged. Copies of
the four E cutover modules supply the baseline, including their then-retained old definitions;
the mapped proof bodies are the post-E bodies. The harness transformations and source hashes
are recorded in harness-notes.md and the two map files.

The required repair to strongExit_of_clean includes an explicit new premise: cleanExit alone
permits die badName, so it cannot imply the strengthened exclusion. Its callers in popR_typed
also need the appropriate original-cause and interrupt-provenance evidence. Merely adding
unfolding to the failed proof would leave that statement false. The diagnostic attribution and
local repair outline are in part-one-errors.json and mechanical/repair-plan.md. The latter is
retained as the preparing seat's static plan; the compiler results in probe-status.json and
this receipt supersede its uncompiled status.

Smallest amendment: authorize the eight named existing-body repairs (seven legacy plus the E
adapter), the explicit clean-failure premise, and the local cause-exclusion lemmas needed by
those bodies. Keep the part-two requirement-row question separate and retain the prohibition
on M5–M7 proofs. Further failures after those repairs would need another cost report; this
probe does not promise that eight is the final cost. Proposed row 107 remains open. Neither
E4-TYPED-CE-007 nor E4-TYPED-CE-003's repair column was changed.

Commands, all with LEAN_NUM_THREADS=1 and from this worktree:
- `lake env lean -DwarningAsError=true
  docs/research/2026-09-30-seat-codex-slice6-evidence/H2/Baseline.lean`: exit 0
  (`baseline.log`, empty successful output).
- The same command for `H2/PartOne.lean`: exit 1, expected diagnostic result
  (`part-one.log`). `map_errors.py PartOne part-one.log` maps the primary errors to the eight
  bodies above (`part-one-errors.json`); no harness errors remain. A failing elaboration's
  recovery placeholders are not proof evidence, and no positive claim is drawn from its
  apparently unchanged downstream proofs.
- The same command for `H2/diagnostics/MissingServiceTransport.lean`: final exit 0
  (`missing-service.log`), all five printed theorems within [propext, Quot.sound]. The first
  run's opaque-definition decidability failure was replaced by direct reduction; its log is
  retained as missing-service.failed.log and is not proof evidence.

The last diagnostic is limited to the part-two helper: equal error columns do not transport
missingService exclusion when the requirement row changes from nonempty to empty. It supplies
no saved frame or reached run and does not refute the full stack walk. It records why an
additional service-presence argument is needed; part two was not implemented after the stop.
All H2 candidates remain research evidence only. No source, tests, generated files or runtime
behavior changed for H2. The preceding H1 evidence commit is `ea80292b`.

## Final state and merge limits

Audited item head: `46f61553339c65fe2ea0d1a7d0ee4d35434694a0`. The last Lean source/test
change is E4, `0c1e9915`; H1 and H2 add only research evidence and this receipt. The closeout
commit adds the final audit and ledger, updates this receipt, and corrects two register status
sentences so G and H1 cannot be mistaken for completed repairs. No further Lean change is made.

| Item / step | Commit | Outcome |
| --- | --- | --- |
| A | ca05788c | Stopped: generated Runner codec outside the permitted paths; patch retained. |
| B | eca77d6a | Implemented and checked; host-answer-free scope only. |
| C | 4369c629 | Stopped: one extra loaded-root reader; dependent D work held. |
| D: generic lifts | 75ee115c | Implemented and checked; no M6 instance. |
| D: guard driver | 9dddff27 | Implemented and checked through the generic lift. |
| D: memo identifiers | e1c6a1fc | Implemented and checked on native reachable states only. |
| F | 8065fd64 | Stopped: two generated closure manifests outside the permitted paths; patch retained. |
| G | 1d8ef8e1 | Stopped: an additional accepted AuthorContract fixture would change. |
| E1 | 5e142337 | Membership and fold connection added beside the old judgments. |
| E2 | c1bcfdf6 | Production callers migrated; eight body repairs and two new adapters checked. |
| E3 | 602ab157 | Tests migrated and old falsifiers retained. |
| E4 | 0c1e9915 | Old production judgments retired; final narrow checks pass. |
| H1 | ea80292b | Stopped: proposed observer step is refuted by the checked local witness. |
| H2 | 46f61553 | Stopped: eight existing bodies need repair in the part-one probe. |

[commit-ledger.json](2026-09-30-seat-codex-slice6-evidence/commit-ledger.json) gives each full
commit hash and every changed path, including evidence. The per-item sections give the exact
build/probe commands and outcomes. [final-audit.json](2026-09-30-seat-codex-slice6-evidence/final-audit.json)
records the branch, audited head, changed source/test paths and scope checks.

Final static checks: no changes to docs/core, docs/STATE.md, README.md or docs/ARCHITECTURE.md;
no runtime or generated-output difference from the supplied base; no retired value-judgment
name under production Typed; whitespace checks pass for active source/tests, the register and
receipt. Stored patch/diff artifacts retain their original context and generated bytes and are
not treated as source whitespace changes. An independent read-only review checked the item
evidence and H2's copied source maps; it found only the two now-corrected status sentences.

The final production evidence is the successful E retirement build (Assembly and nine named
Test targets, 382 jobs) plus the earlier D/B narrow builds and explicit axiom receipts. The full
721-job build and 500-module / 68495-declaration trust output belong to F's generation attempt,
before E; they are not a post-E whole-tree sweep. No final whole-battery or make-check sweep was
requested or run. The stopped runtime repairs have no completed OCaml execution receipt.

M5–M7 proofs, the C-dependent D proofs and forkedOf move, M3bWorld's remaining residual-program
weakening obligation, and M6's 20 obligations remain open. The runtime-to-Fits bridge remains
parked. None of the finite controls is a general runtime or compiler theorem. The main checkout
was not used for this implementation. No push was made.
