# HO-3b review: empty callback lists block checked TypeScript printing

Handle the empty callback list before asking for a checked context.
The current invocation draft otherwise refuses valid programs when an approved term or eliminator site selects checked TypeScript printing.
A probe that changes only this empty-list case restores printing and reconstruction in every reduced control.

## Reviewed state

The landed owner commit is `000bcd7ad68e7bbbe4f3478831982a7f9f2f1a42`, on `claude/ho3`.
Its eight changed source files match the HO-3a snapshot already checked at review commit `d5110c598a952b090d1939ef7a15f628c05a318a`.
This review examines the later working HO-3b invocation changes.
It does not present those changes as a completed landing.

The bounded Claude session tail verifies the repository working directory.
Claude is extending `Laws/Codegen/ReadPrint.lean` with invocation separation and reconstruction cases.
Two GPT-6.1 Sol reviews independently inspect name laws, captured environments, and the checked TypeScript printing route.
The implementation worktree and session remain unchanged by this review.

[PLAN.md](PLAN.md) places the work before the probes.
[PROOF-DAG.md](PROOF-DAG.md) records the smallest repairs and their existing proof consumers.
[The checkpoint](checkpoint.json) retains the reviewed files, hashes, and outstanding findings.

## HO3b-SPINE-01: a valid callback list ends without a context

`Templates.typedSitesAlg` in `src/Effect4/Codegen/PrintTyped.lean` checks for a context before dispatching each source family.
`Annotate.checkEffs` in `src/Effect4/Program/Typing/Annotate.lean` marks the tail after the final callback slot as unreached.
That terminal empty list has no context.
The printer therefore returns `internalAction "typed:missing context"` instead of the empty list.

[TypedSites.lean](TypedSites.lean) checks four failing source programs:

- an invocation whose request contains union-typed tuple fields;
- an invocation whose callback contains those fields;
- an ordinary invocation following an unrelated joined term;
- a closed invocation whose callback duplicates its union-typed argument.

Each program passes its source typing check.
The ordinary raw printer succeeds.
The checked TypeScript printer refuses all four with the same missing-context reason.
A non-joined context succeeds through the existing raw route.
An ordinary joined term outside an invocation also succeeds.

The failure requires `needsSitesAt = true`, which selects `typedSitesAlg` for the containing program.
A row-call annotation alone can remain on `typedAlg` and avoid this failure.
The packet does not claim that every union or every join triggers it.

The probe-only algebra overrides `effs_nil` with the empty successful output.
It introduces no stored syntax and changes no typing context.
That override restores printing, named erasure, and reconstruction in all four controls.
Keep the implementation repair equally narrow: actual callback bodies still need their checked contexts.
Preserve `Focus` and `Annotate`'s unreached terminal tail.

This is a confirmed failure in the working checked TypeScript printer.
It does not refute G6 or the landed HO-3a reconstruction result.
It also does not refute a theorem conditional on successful printing.

## HO3b-TERM-01: invocation requests bypass checked term printing

The empty-list repair exposes a smaller shared-structure gap.
`PrintEliminators.layer` in `src/Effect4/Codegen/PrintEliminators.lean` passes invocation requests to the raw `printInvoke` helper.
That helper calls raw `printTerm` in `src/Effect4/Codegen/PrintLeaf.lean`.

The checked term fold prints `tuple<number | string, number | string>(a0, a1)` in an ordinary term position.
The repaired invocation prints the same request as `tuple(a0, a1)`.
The callback body uses the checked term fold and receives the annotations correctly.

This is a checked insertion-policy inconsistency, not a demonstrated tsgo rejection.
Share invocation assembly while letting its caller supply the printed request expression.
The checked caller should reuse `PrintEliminators.term`; the raw caller should retain `printTerm`.
This removes a bypass without adding an author-facing option.

## Raw invocation controls pass

[Generated.lean](Generated.lean) builds ten closed programs through the existing API.
Every generated module reconstructs its original program.
All generated declarations remain unchanged when the runner prepends the explicit Effect import.

| Case | Checked exit value |
| --- | --- |
| Identity callback | 5 |
| Captured outer value | 11 |
| Callback request | 5 |
| Nested outer capture | 11 |
| Nested middle capture | 5 |
| Nested inner argument | 3 |
| Forwarded program parameter | 29 |
| First callback selected | 11 |
| Second callback selected | 17 |
| Captured value through a fork | 37 |

The Lean runner uses budget 600 for each case.
Effect rc.112 under Bun 1.4.2 returns the same ten values.
Pinned tsgo `7.0.0-dev.20260629.1` accepts the generated modules and runtime driver.
The source checker refuses missing callbacks, extra callbacks, a wrong callback result, and an out-of-scope variable.
The raw reader refuses a wrong callback binder while accepting its canonical twin.
The named erasure leaves the malformed binder unchanged.

These are finite observations, not a general execution or scheduling theorem.
The fork control establishes its recorded value only.
The controls use no host replies and establish no cleanup property.

## Landing support

The name-law changes retain the existing separation premises.
Each callback reads under the caller's typing signature and spelling map.
Each parameterized definition retains its own context in the paired module-body reconstruction route.

Claude is already updating the child-depth metadata and its proof for invocations.
Keep that repair with the existing implementation work.
The empty-tail exception also changes which successful print results imply the presence of a context.
[PROOF-DAG.md](PROOF-DAG.md) identifies those exact consumers before proof repair starts.

The earlier findings `HO3-REQ-01`, `HO3-NAME-01`, `HO3-SVC-01`, and `HO3-ANN-01` remain unchanged.
Their existing packets retain their controls and recommendations.
This review does not duplicate them or treat deferred HO-4 and HO-5 work as regressions.

## Reproduction and limits

Run these commands sequentially from the isolated review worktree:

```sh
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-2016/run_probes.py generate runtime
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-2016/run_probes.py typed
```

[The generation results](checked-results-generate-runtime.json) record each command, output, version, and expected exit.
[The typed results](checked-results-typed.json) record the refusal controls and the local algebra repair.
Source and imported-artifact hashes remain unchanged during both successful checks.
The runner reuses the owner's compiled imports and records their hashes.
The erasure source is newer than its owner artifact, so typed mode rebuilds that module into the review-only artifact directory.
No artifact is written into the owner worktree.
One verification attempt is interrupted by the owner build cleanup.
The final runner compiles a matching source copy from the review directory to keep process ownership clear.

The packet introduces no theorem or planned goal, and claims no new axiom gate.
The prior HO-3a audit remains attached to its exact earlier checkpoint.
No full sweep, merge, push, or message to Claude occurs.
