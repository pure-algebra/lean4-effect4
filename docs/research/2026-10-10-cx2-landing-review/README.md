# CX1 and CX2 landing review

The invocation and parameter-hop proofs no longer rest on an open goal.
The general typed-run result still rests on `crossScopeRef_builds`.
Keep that distinction when describing this landing.

## Reviewed tree

Production base: `f00008eeaef00b67fe93cfd0327754c9f42694ee`.
Reviewed landing: `9e818b39596971d62b89299ca9ccc4e96ad8ea07`.
Review branch: `codex/review-cx2-landing`.

The review reuses the attached isolated worktree.
The source diff check pins its production files to the landing.
Claude's session and primary working files remain unchanged.
The primary tree's separate `TyView.lean` change is outside this review.

The previous retained finding is:
`git:514a6d9f:docs/research/2026-10-10-cx-layer-context-review/README.md`.
This review does not report that cached-error observation as new.
The landing changes proof files without changing the runtime that produced that observation.
[Source scope](source-scope.json) records the changed library paths.

## Checked results

Evidence status: independently compiled and audited at the reviewed commit.
Proof role: verification of existing typing claims and their open dependencies.
Scope: the changed law modules and the direct M7 consumer.

[verification.json](verification.json) records commands, exits, timestamps, and source hashes.
[build.log](build.log) records the narrow build.
[audit.log](audit.log) records the cycle-aware trust audit and each inspected plan status.

The plan reports these results:

| Declaration | Path | Result |
| --- | --- | --- |
| `invoke_arm` | `src/Effect4/Laws/Program/Typed/Denotation.lean` | Proved under its stated hypotheses; no planned-goal dependency |
| `param_arm` | `src/Effect4/Laws/Program/Typed/Denotation.lean` | Proved under its stated hypotheses; no planned-goal dependency |
| `childDenotes_upto` | `src/Effect4/Laws/Program/Typed/Denotation.lean` | Proved with the layer arm as an explicit hypothesis |
| `denotesTyped_of_layerFree` | `src/Effect4/Laws/Program/Typed/Assembly.lean` | Proved on the named layer-free fragment; no planned-goal dependency |
| `denotesTyped` | `src/Effect4/Laws/Program/Typed/LayerArm.lean` | Modulo `crossScopeRef_builds` |
| `m7_proved` | `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean` | Modulo `crossScopeRef_builds` |

`childDenotes_upto` being proved does not discharge its `ProvideLayerArm` hypothesis.
The layer-free connector supplies that hypothesis for its own fragment.
The general connector still reaches the recorded cross-scope goal.

## Retained-environment review

A GPT-6.1 Sol reviewer independently inspected the changes without editing or running Lean.
The review covered the following consumers and their immediate dependencies.
The compilation and trust evidence comes from this packet's separate run.

| Consumer | Retained evidence | Source |
| --- | --- | --- |
| Loop entry and resumption | `LoopFrameTyped` retains `StackTyped`; entry, step closure, and world extension carry it | `src/Effect4/Laws/Program/Typed/Commands/Clauses/Loop.lean` |
| Generator suspension and resumption | `GenSt` and `WalkOk` retain stack typing; `genSt_closed` transports it | `src/Effect4/Laws/Program/Typed/Commands/Clauses/Gen.lean` |
| Delayed cleanup | `acquireIn_typed` retains the stack in the capture | `src/Effect4/Laws/Program/Typed/Body.lean` |
| Release entry | `capture_release` reconstructs the release point through `pointTyped_child` | `src/Effect4/Laws/Program/Typed/Assembly.lean` |
| Later worlds and appended row tables | `stackTyped_mono` and `stackTyped_rows_append` transport stored sites recursively | `src/Effect4/Laws/Program/Typed/Residual.lean` |
| Stored finalizers | Capture transport carries the stack with the captured values | `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` |

No new concrete defect was found in these changes.
The generator discharges its scope premise from the actual generator node through `scopeParams_prefix`.
The loop retains typed values, its checked body, the updated cursor, and the resumed completed view.
Row-table extension retains the same program and service declarations.
An empty lexical scope permits inactive stack frames without granting access to their parameters.

## Shared structure and authoring

`hop_typed` in `src/Effect4/Laws/Program/Typed/Denotation.lean` supplies the shared step for invocation and parameter entry.
It combines addressed code, the lexical check, captured values, the completed view, and the typed stack.
Both arms reuse its world-sensitive membership and answer/error widening.
This concentrates the proof work without adding another program representation or another author declaration.

The landing types stored sites and their environments.
It does not establish capture-avoiding substitution or an invocation-unfolding simulation.
Those connections remain the later CX3/CX4 work.
Layer identity remains an explicit premise for any later law transport that changes syntax.

## Placement and limits

The reviewed obligations retain the placement recorded in [PLAN.md](PLAN.md).
Their concept is `residual-program-typing`, serving the fundamental property `denote-typed` and requirement R4.
The consumers lie on the M5 to M6 to M7 dependency graph.
The reach and hypotheses are those of the declarations at the pinned commit.

The trust audit accepts the permitted axioms and explicitly reports declarations resting on the remaining goal.
It grants no proof of that goal.
This review establishes no progress, liveness, termination, or outside-runtime agreement.
The host boundary remains the one in `docs/core/host-boundary.md`.
No behavior gate is claimed by this proof-only review.
No full sweep, merge, or push runs.

## Reproduction

Run from the pinned review worktree:

```sh
python3 docs/research/2026-10-10-cx2-landing-review/verify.py
```

The verifier uses `LEAN_NUM_THREADS=3` and runs one Lake process at a time.
The changed module list is [modules.txt](modules.txt).
The M7 consumer is also built because the plan inspects it.
Only this packet's research files are committed by the review.

## Checkpoint

CX1/CX2's invocation and retained-stack contribution is independently checked at `9e818b39`.
The cached-error finding remains open and unchanged from `514a6d9f`.
The next design action remains choosing the cross-scope sharing contract before closing its goal.
The later substitution and unfolding work remains deferred.
