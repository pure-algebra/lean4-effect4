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
Pending.

## D — generic lifts and slice 6 proofs
Pending.

## F — closed layer build environment
Pending.

## G — layer values and provision fixtures
Pending.

## E — Fits membership
Pending.

## H1 — command queue conditions
Pending.

## H2 — shared exit judgment, probe first
Pending.
