# Prepared graph motion receipt

The compatibility theorem covers arbitrary finite inputs, including duplicate keys and occurrence order.
The moving-bar mismatch remains inherited and unresolved.

Base: `d6285ddf8ab54ef7d5fc3bb32a23831173e45afe`.
Dependency: coordinator admission commit `859122814`, cherry-picked as `1c150fcc8`.
Branch: `codex/graph-api-depth`.
Implementation head: the coordinator receives the landing commit hash with this receipt.

## Changes

`GraphMotion.prepare` (`tools/Tools/View/GraphMotion.lean`) stores first-key matches, route membership, entry phases, and ordered exit selections.
`GraphMotion.Prepared.sample` in that file reads these data for each sample time.
The record contains data rather than lookup closures.
Preparation reuses `Laid.Ix` and `KeyMap` from `tools/Tools/View/Graph.lean` and `tools/Tools/View/KeyMap.lean`.
The target arrays retain their original interleaving and repeated occurrences.

`sampleLaid` (`tools/Tools/View/Motion.lean`) retains its public parameters and samples a prepared transition.
`preparePageMotion` in that file prepares the graph once and retains the existing line sampler.
`Drivers.View.writeFrames` (`tools/Drivers/View.lean`) prepares before its intermediate-frame loop.
Both specimen consumers in that file use `Specimen.checkedFrames` (`tools/Tools/View/Specimen.lean`).
Their errors retain the existing `graphRefusal` formatter.

`GraphTransitionProbe` (`tools/view/GraphTransitionProbe.lean`) holds finite controls and sampler timing measurements.
The assessment and placement plan are `docs/research/2026-10-13-graph-api-depth-assessment.md` and `docs/research/2026-10-13-graph-motion-plan.md`.

## Proof placement

Concept: `initial-algebras-folds`, concept 7 of `docs/core/semantics.md`.
Requirement: R14 view navigation.
Proof role: compatibility.
Evidence status: proved tool law.
Scope: every choreography, old layout, new layout, and natural sample time.

`GraphMotion.prepare_sample_eq_reference` (`tools/Tools/View/GraphMotion.lean`) observes equality of the full sampled layout.
`GraphMotion.reference` in that file retains the base sampler's computation.
The lookup helpers serve this law.
`preparePageMotion_sample` (`tools/Tools/View/Motion.lean`) connects the retained page graph to the existing page sampler.
The existing endpoint laws retain their statements and consume the reference agreement.

Decisions row 334 (3) and row 336 (8) place these named tool laws outside registry claims.
The coordinator can record the names under the existing R14 view plan.
They establish no schedule, curvature property, complexity bound, or host rendering equality.
No machine or program-syntax declaration changes.

## Commands and results

Each Lake command exports `LEAN_NUM_THREADS=3` in PowerShell.
Only one Lake command runs in this worktree at a time.

| Command | Result |
| --- | --- |
| `lake build Tools.View.GraphMotion Tools.View.Motion Drivers.View` | Pass after the checked specimen migration |
| `lake env lean -DwarningAsError=true --run tools/view/GraphTransitionProbe.lean 1` | Pass; finite controls and all sampled checksums agree |
| `lake env lean --run tools/view/GraphTransitionProbe.lean 3` | Pass; sampler measurements in `Benchmark.txt` |
| `lake env lean .lake/graph-motion-core-audit.lean` | Pass; strict audit in the next section |
| `lake env lean .lake/graph-motion-audit.lean` | Reports inherited host offenders; no new offender names |
| `git diff --check` | Pass |

The initial build stops before compilation because the local kit checkout lacks its manifest commit.
`git -C .lake/packages/whatwg fetch C:/Users/kokok/Dev/lean4-whatwg-svg-reconcile e51195721f47fa767fb84f918dc439e76d83071f` supplies that commit.
Lake then checks out the manifest commit and builds successfully.
The tracked manifest and dependency declaration remain unchanged.
Lake still reports the existing manifest/declaration mismatch warning.

## Axiom output

The retained output is `docs/research/2026-10-13-graph-motion-evidence/LandingAudit.txt`.
`#axiom_audit Tools.View.GraphMotion` reports 86 declarations inside `[propext, Quot.sound]`.
It reports no planned goals and no declarations modulo goals.

`#axiom_audit Tools.View.Motion` reports two inherited offenders among 62 declarations.
Their exact names are `Tools.View.underKey` and `Tools.View.keptUnchanged`.
Their boundary traverses `String.Slice.toString`.

`#axiom_audit Drivers.View` reports 25 inherited host offenders among 104 declarations.
The baseline reports the same offender names among 103 declarations.
`AuditComparison.json` records empty added and removed sets for both modules.
The baseline reads the frozen files at the base commit under separate namespaces.
`BaselineAudit.txt` retains that output.

The first proof attempt uses `List.isSome_find?`, whose toolchain proof reaches `Classical.choice`.
The final proof replaces that step with Boolean induction.
No new proof depends on that axiom.

## Bounded performance evidence

`Benchmark.txt` records preparation and sampling separately.
An `IO.Ref` forces preparation before its timestamp.
Every sampled layout contributes to the checksum.
Each case samples the actual 61 reveal times three times.
Preparation runs once per case.

The six actual graphs come from `FlowSpecimen.frames` (`tools/Tools/View/FlowSpecimen.lean`).
They are nested forks, wide race, race loop, await all, nested scopes, and handler scope.
The synthetic cases contain 128 and 512 placed nodes.

These measurements concern host sampler execution under `lake env lean --run`.
They exclude SVG serialization, file writes, browser playback, and line-sampler optimization.
They establish no general performance bound.
The coordinator measures complete exports after integration.

## Open observation

The moving-bar control uses matching port and mark keys at both endpoints.
The linear midpoint places the port at `y=50` and retains the target mark at `y=100`.
`Laid.onBar` (`tools/Tools/View/Graph.lean`) answers false at that midpoint.
It answers true at both endpoints.
`Controls.txt` records the values.
The prepared sampler retains this base observation under its compatibility law.
A later geometry or mark-motion change needs its own observation and agreement scope.

The caller's arbitrary `GraphMotion.Prepared` record carries no agreement certificate.
The compatibility law applies to `GraphMotion.prepare` output.
Line sampling still repeats its current line analysis.
The connector method and rendering arithmetic remain unchanged.
