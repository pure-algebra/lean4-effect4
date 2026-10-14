# PROC-6 landing receipt

Slices P and A are committed and approved.
The coordinator update is merged, and every required A behavior gate passes.
The block-session claim remains a planned goal.
The continuation brief authorizes B through F, subject to its stop rules.

Status: receipt, history rather than authority.
Evidence kinds: checked Lean builds, exact axiom audits, finite controls, and outside behavior comparisons.
Scope: decisions row 379. This checkpoint records P and A; later sections record subsequent slices.

## Commits and ownership

| Item | Commit or path |
| --- | --- |
| Base | `d6e162caf2bdfd6e1a3718b75d4c8aa34d145034` |
| Branch | `codex/proc6` |
| Worktree | `/Users/pooks/Dev/lean4-effect4-codex` |
| P head | `9d404a1ecbd180973ebdef20441bb1e155d093cc` |
| A core head | `479f2d7ddac01962e2c0423199d782454a66b11e` |
| A hooks head | `8576f0db4c1497714c38735103d871cb16b6bac5` |
| Coordinator merge | `5290731d502d5a9f3335d950b8117b4146143eb4` |

The main checkout and Gemini worktree receive no source edits from this seat.
The coordinator owns merging this branch.
The commits name their paths explicitly.
The branch is not pushed.

## Slice P

The new block meaning reads the current context and cuts calls and loops at its budget.
Argument trees retain the caller's budget and read the context of their invocation.
At a positive call budget, a missing definition returns `badShapeExit`.
A missing parameter returns `badShapeExit` at every budget.
A budget cut remains `none`.

`BodyRows` admits no nested block or context constructs yet.
`BlockRows` requires a leading block without layers, with admitted bodies and main program.
The initial agreement statements use the empty context.
Stage 4 still owes their context generalization.

The registry claim `rows-block-host` points to `Effect4.Run.h9_blocks`.
Its role is simulation, its concept is translation-simulation, and its requirement is R6, serving R10.
Every new obligation has a placement and a named consumer.
[The goal inventory](landing-evidence/goal-placements.json) records each name, source path, requirement, consumer, scope and checked status.

| Module | Contents |
| --- | --- |
| `src/Effect4/Laws/Program/BlockMeaning.lean` | Reader trees, full block algebra, recursive meaning, host observation, and stage 0 goals |
| `src/Effect4/Laws/Program/FragmentBlock.lean` | Body and root fragments, with the body-lookup goal |
| `src/Effect4/Laws/Program/Agreement/BlockPlain.lean` | The block-to-hooks goal |
| `src/Effect4/Laws/Program/Agreement/Blocks.lean` | Parameter and compile relations, address goals, and root connection |
| `src/Effect4/Laws/Program/Agreement/HostedBlocks.lean` | Stability and completed-run closing goals |
| `src/Effect4/Laws/Api/SessionMeaningBlocks.lean` | The completed-session observation and its planned theorem |
| `src/Effect4/Laws/Program/ValidatedBlocks.lean` | Planned protocol and reference-model consumers |

The root imports append these modules to `src/Effect4/Laws.lean`.
The registry changes in `tools/ProofGraph/Registry.lean`.
The producer regenerates `generated/semantics.md`.

### Checked evidence

The commands run from the worktree, except the stated OCaml command.
Every command containing Lake runs inside the shared slot.
These shell variables abbreviate the retained command lines:

```sh
slot=/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh
scratch=/tmp/proc6-landing
export PATH="$scratch/bin:$PATH"
```

The Make commands include `-o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules`.
These options keep the existing dependency links and prevent installation.
The retained `finish-checks.sh` records the final command sequence.

| Command | Result | Log |
| --- | --- | --- |
| `"$slot" lake build Effect4 Effect4.Laws` at base | PASS, 1111 jobs | `landing-evidence/initial-build.log` |
| `"$slot" lake build Effect4.Laws.Program.ValidatedBlocks` | PASS, 546 jobs | `landing-evidence/p-leaf-build-3.log` |
| `"$slot" lake build ProofGraph.AxiomAudit ProofGraph.Plan` | PASS, 17 jobs | `landing-evidence/p-audit-tools-build.log` |
| `"$slot" lake env lean -DwarningAsError=true "$scratch/p-audit.lean"` | PASS; all 24 statuses are goals | `landing-evidence/p-audit.log` |
| `"$slot" make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics` | PASS, 1651 jobs | `landing-evidence/p-semantics-final.log` |

The exact audit reports:

```text
#axiom_audit: 50 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 24 planned goals
```

The plan query reports:

```text
Effect4.Run.h9_blocks: goal; nearest []; 0 lemmas, 0 definitions
next goals: 1
  goal Effect4.Run.h9_blocks : Effect4.Run.H9Blocks
```

The retained P audit lists every goal's status and full statement.
All 24 remain goals.
P changes no machine behavior and reaches no outside behavior gate.

## Slice A

An ordinary call now pushes an empty program-argument frame.
The reference meaning, call-hop law, induction measure and typed call proof follow that change.
`weight_redirect_params_lt` replaces the deleted `weight_redirect_call_lt` in the call introduction.

`PlainHooks` moves unchanged from its temporary P location into `Agreement/Machine.lean`.
The existing loop-fragment proofs supply `PlainHooks.of_loopedRows` in `src/Effect4/Laws/Program/Agreement/Machine.lean`.
Its concept is translation-simulation; it serves `rows-block-host`, R6, through the existing hosted session laws.
Its reach is plain resolver and suspension hooks for `LoopedRows` at every captured point.
It establishes no block, context, scheduler or host agreement.
The measured migration has 23 premises: 12 in Machine, two in Segment, six in Hosted, and three in SessionMeaning.
The public loop-meaning premises retain their fragment restrictions and use adapters internally.

The three exit-pass helpers accept either saved interruptibility flag.
Current callers supply `true`.
These helpers remain steps of `run-eq-meaning`, R6, in `src/Effect4/Laws/Program/Agreement.lean`.
Their consumers are the existing exit-frame proofs in Agreement, Loop, LoopCalls and Machine.
The machine forms and scheduler remain the existing forms.
The scheduler generalization belongs to F.

| Commit group | Changed paths |
| --- | --- |
| A core | `src/Effect4/Program/Compile.lean` |
| A core | `src/Effect4/Laws/Program/DenoteR.lean` |
| A core | `src/Effect4/Laws/Program/Agreement.lean` |
| A core | `src/Effect4/Laws/Program/Intro/Sequential.lean` |
| A core | `src/Effect4/Laws/Program/Intro/Weight.lean` |
| A core | `src/Effect4/Laws/Program/Typed/Denotation.lean` |
| A core | `src/Effect4/Laws/Program/Agreement/Loop.lean` |
| A core | `src/Effect4/Laws/Program/Agreement/LoopCalls.lean` |
| A core, generated | `ocaml/gen/api_gen.ml` |
| A core, generated | `ocaml/engine/api_engine.ml` |
| A core, generated | `ocaml/gen/closure-api_gen.tsv` |
| A core, generated | `ocaml/gen/closure-api_engine.tsv` |
| A hooks | `src/Effect4/Laws/Program/Agreement/Machine.lean` |
| A hooks | `src/Effect4/Laws/Program/Agreement/Segment.lean` |
| A hooks | `src/Effect4/Laws/Program/Agreement/Hosted.lean` |
| A hooks | `src/Effect4/Laws/Api/SessionMeaning.lean` |
| A hooks | `src/Effect4/Laws/Api/SessionMeaningLoop.lean` |
| A hooks | `src/Effect4/Laws/Program/Agreement/BlockPlain.lean` |
| A hooks, generated | `generated/semantics.md` |

### Checked evidence

| Command | Result | Log |
| --- | --- | --- |
| `"$slot" lake build Effect4.Laws.Program.Agreement.Machine Effect4.Laws.Program.Intro.Sequential Effect4.Laws.Program.Typed.Denotation` | PASS, 504 jobs | `landing-evidence/a-narrow-repair.log` |
| `"$slot" lake build Effect4.Laws.Program.Agreement.Hosted` | PASS, 409 jobs | `landing-evidence/a-hosted-repair.log` |
| `"$slot" lake build Effect4 Effect4.Laws` | PASS, 1118 jobs | `landing-evidence/a-build-accepted.log` |
| `"$slot" lake env lean -DwarningAsError=true "$scratch/a-lexical-control.lean"` | PASS, three finite guards | `landing-evidence/a-lexical-after.log` |
| `"$slot" lake env lean -DwarningAsError=true "$scratch/a-audit.lean"` | PASS, exact audit below | `landing-evidence/a-audit.log` |
| `"$slot" make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-lcnf` | PASS, all four ML checks | `landing-evidence/a-gen-lcnf.log` |
| `opam exec --switch=effect4 -- dune build`, from `ocaml/` | PASS, exit 0; no diagnostics | `landing-evidence/a-dune.log` |
| `make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules check-compiler check-native check-ocaml check-truth check-host-protocol` | Compiler, native and OCaml pass; truth reaches the known baseline P2b failure | `landing-evidence/a-gates.log` |
| `make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics` | PASS, 1645 jobs | `landing-evidence/a-semantics.log` |
| `lake env lean -DwarningAsError=true "$scratch/p-audit.lean"` | PASS, 24 planned goals remain | `landing-evidence/a-final-goals.log` |

The combined gate command runs under `"$slot" bash "$scratch/finish-checks.sh"`.
It stops at the baseline P2b failure.
The remaining commands run under `"$slot" bash "$scratch/remaining-checks.sh"`.
The script uses `set -euo pipefail`, preserving each command's failure through its log pipe.

The compiler comparison passes 129 OCaml cases and three mutations.
Its normalization and validity checks report 235 and 81 cases.
The native comparison passes 867 cases.
The OCaml comparison and generated-file check pass.

The first truth run passes 81 programs and 12 signed divergences before the baseline P2b error.
Coordinator commit `f78fda8ef` repairs that error.
After the merge, one truth rerun passes the corpus, widening checks, P2b controls and generated-module typecheck.
Its log is `landing-evidence/a-truth-after-merge.log`.
The generated to-do fixture matches coordinator commit `6c3bbf320` byte for byte.
The merge supplies that fixture.

The separate host-protocol run passes; its log is `landing-evidence/a-host-protocol.log`.
It reports 57 rc.112 runs, 52 admitted programs, 86 scripts, 295 runs and 60 Bun tests.
Its service comparison passes 13 scripts.
Its SQLite comparison passes 11 recorded requests and the negative controls.

The local package fetch seeds `3e5e79335e778c04493245e14e31bb2d48d0d54f` before the truth rerun:

```sh
git -C .lake/packages/whatwg fetch /Users/pooks/Dev/lean4-whatwg-svg html/svg
```

The fetch reads the local kit repository and downloads nothing.

The exact audit reports:

```text
#axiom_audit: 4635 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 1 planned goals
```

The one audited goal belongs to `Agreement/BlockPlain.lean`.
The audit checks all modules A edits, including the compiler and typed denotation.
The block-session plan query still reports a goal.

The finite lexical control contains three guards.
Before A, its two isolation guards fail and its explicit-invocation control passes.
After A, all three pass without diagnostics.
This evidence covers compilation and suspension hops, not scheduler execution or host behavior.

The behavior gate logs retain their exact observations and counts.
These finite comparisons establish their tested scope, not universal target or host correctness.

## Adjustments and repairs

1. The generated `denoteRowsB.alg` carrier pairs source syntax with its meaning.
   The sketch's direct reader lift does not typecheck.
   `blockAlgB` lifts the same `thenOpt` and `loopStep` equations explicitly.
   Its leaf fields reuse `denoteRows.alg`.
2. P needs the `PlainHooks` type before A changes its consumers.
   P defines it temporarily in `BlockPlain`; A moves the same declaration into `Machine`.
3. Lean refuses imports after the root's trailing module documentation.
   The new imports append at the end of the import block, before that documentation.
4. `#plan_status` accepts declaration identifiers, not registry claim strings.
   The audit queries the claim's verified pointer, `Effect4.Run.h9_blocks`.
5. Parameter approximation uses equal list lengths and pointwise lookup witnesses.
   The available list library has neither proposed `List.Forall₂` nor `List.Forall2`.
6. A record-layout error and an omitted `compile` unfolding fail intermediate builds.
   The corrected sources pass the retained final builds.
   No theorem premise changes to repair either failure.

The prep receipt marks four gate baselines pending.
It records a passed host-protocol baseline.
This receipt uses this branch's measured gate results and does not invent missing baseline results.

## Open work and decision proposal

B replaces the old block meaning and migrates its consumers and claim pointers.
Its twelve stage 0 goals are proved.
Block plainness, forward agreement, closing steps and validated consumers remain planned goals at the B checkpoint.
F still owes machine forms with a context and scheduler agreement at every context budget.
G still owes the shipped consumer's per-request replay and keyed composite check.

The new fragments impose no row-column or service-key restriction.
The landing introduces no budget-safety invariant.
The completed-run premise supplies no progress, termination, funding or host-conformance proof.

Proposed register note, for the coordinator:

> PROC-6 slices P and A implement row 379's placement and lexical-call preparation.
> The block-session claim remains a planned goal.
> The continuation review approves both slices and authorizes B through F under its stop rules.

The decision register stays unchanged in this branch.

## Retained evidence

[The evidence manifest](landing-evidence/manifest.json) lists the retained files and their hashes.
The directory contains the exact build and gate logs, the audit sources, and the lexical control.
It retains the failed intermediate logs beside the successful replacements.
[The command record](landing-evidence/commands.json) records results and their source revisions.
[The source digest](landing-evidence/source-files.json) binds the checked files to the committed tree.

The manifest records exact evidence hashes and source commits.
The subagent reports are independent source reviews, not additional Lean runs.
Every Lake run uses the shared slot.
Existing installed dependencies supply Bun and tsgo; the wrapper adds `--no-install` to nested Bun calls.
The version record reports Bun 1.4.2, tsgo 7.0.0-dev.20260629.1 and dune 3.24.2.

## F risk 6 preflight

The independent source audit finds no demonstrated blocker.
The proposed relation must preserve stopped waiting calls as well as completed exits.
A waiting call retains its request, stores and host state.
Existing frontier claims consume that exact observation.
The audit checks sources; it does not prove the new relation or its connectors.
The detailed report is retained when F lands.

## Slice B

All twelve stage 0 goals are proved in place, with their approved statements unchanged.
The combined build and exact audit pass.
The application law retains its arbitrary outer context and gains the optional finished exit.

Base: `42ae57813a368b2acfa349f9d06768aa89e729b9`. Code head: `b7ca24a26fbfb69b29ccfc137d1ec7d0dfb7ed9f`.
The coherent commits are `f763dda79`, `9efb68b6c`, `f83b7c82d` and `b7ca24a26`.
The first moves `bodiesOf` before the block modules lose their old import dependency.
The next proves the meaning laws; the application migration and remaining deletions follow.

`BlockMeaning.lean` owns `mapOps` and `blockOf?`.
`Block.lean` keeps its module entry through an import.
`ParamRows.lean` retains only the parameter-to-row renaming.
The old recursive-handler meaning and `Effects/Mrec.lean` are deleted.
The Mrec import is the brief's one permitted root-import removal.
The author note and both registry pointers now name the surviving laws.
[The source record](landing-evidence/b/sources.json) lists every changed path and its digest.

The meaning laws serve rows-block-host, R6, and block-handler-monotone/block-handler-unfolds, R10.
`denoteBlockB_straight` carries the deleted no-block compatibility placement, R2, on its stated straight data-row fragment.
Its consumer is the cache-body connection.
The cache helpers serve ref-cache-invalidated-reads-through, R10; the application reader uses the library's `invalidate_get` law.
The finite block battery retains budget cuts, missing progress and finished cases.
It claims no universal scheduler or target agreement.

| Command inside the shared slot | Result | Evidence |
| --- | --- | --- |
| `lake build Effect4.Laws.Library.Ref.Cache` | PASS, 531 jobs | `b-cache-final-build.log` |
| `lake build Test.Program.BlockMeaning` | PASS, 863 jobs | `b-control-build.log` |
| `lake build Effect4.Laws Test.Program.BlockMeaning Test.Dogfood.Scenario.Todo.Cached` | PASS, 1530 jobs | `b-dependents.log` |
| `lake env lean -DwarningAsError=true /tmp/proc6-landing/b-audit.lean` | PASS | `b-audit.log` |
| `make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics` | PASS, 1657 jobs | `b-semantics.log` |

The final three commands run through `lean-slot.sh bash /tmp/proc6-landing/b-final-checks.sh`.
The audit reports:

```text
#axiom_audit: 202 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 1 planned goals
```

The one remaining audited goal is C's body-fragment lookup, included through `FragmentBlock.lean`.
Every queried stage 0 goal reports proved with zero next goals.
`Effect4.Run.h9_blocks` remains a goal at this checkpoint.
The independent Cached audit checks 26 declarations with no planned goals or dependencies on them.
No behavior gate is reached by B.

[The B manifest](landing-evidence/b/manifest.json) binds the retained logs, statement comparison and proof receipts.

## Slice C

The two block-fragment obligations are proved in place, with their approved statements unchanged.
Base: `5af6bc8d5`. Code head: `f05a7b117019a688ee6477e841d16302375b267a`.
The changed files are `FragmentBlock.lean` and `Agreement/BlockPlain.lean`.
The semantics producer updates `generated/semantics.md`.

`bodiesOf_blockRows` proves membership of each indexed definition body.
`PlainHooks.of_blockRows` supplies the resolver and suspension hooks from the whole root block.
Their helpers follow body and argument spines, including lexical calls, invocations and parameters.
Placement: translation-simulation, rows-block-host, R6.
The consumers are `compilesBlk` and the hosted session proof.
The reach remains the stage 1 block fragment without context constructs.
These laws establish no scheduler progress or target behavior.

The shared slot runs `bash /tmp/proc6-landing/c-integrated-checks.sh`:

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Agreement.BlockPlain Effect4.Laws` | PASS, 1096 jobs | `c-integrated-build.log` |
| `lake env lean -DwarningAsError=true /tmp/proc6-landing/c-integrated-audit.lean` | PASS | `c-integrated-audit.log` |
| `make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics` | PASS, 1608 jobs | `c-integrated-semantics.log` |

```text
#axiom_audit: 183 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

Both C goals report proved, with zero next goals.
`Effect4.Run.h9_blocks` remains a goal at this checkpoint.
No behavior gate is reached.
[The C manifest](landing-evidence/c/manifest.json) retains exact evidence and source hashes.
