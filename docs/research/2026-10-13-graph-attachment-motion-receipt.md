# Graph attachment motion receipt

Production sampling intentionally changes the legacy motion observation.
Legacy agreement applies only to `legacySample`, not production `sample`.
The caller can inspect the selected policy and its fallback reason.

Base: `26436e791`.
Source: `6476bd92f1373b3b2dda2e96bcbcc42261a5dc7e`.
Review corrections: `d61a7d373a5cf908cb455d0648f4030b5781e814`.
Dependencies: coordinator seeds `ad8b0075d`, `ed1783560`, and separation source `06adfec52ef472c2cdc6c14bfed77ae1bc19e1f7`.
The coordinator already integrates those dependencies.
The branch is `codex/graph-attachment-motion`.

## Changes and consumers

`GraphAttachmentMotion.prepare` (`tools/Tools/View/GraphAttachmentMotion.lean`) retains explicit attachment, mark, and region data.
It reuses `GraphAttachment.Index` and `GraphAttachment.markTable` (`tools/Tools/View/GraphAttachment.lean`).
Region lookup and route lookup reuse `KeyMap.firstBy` (`tools/Tools/View/KeyMap.lean`).
No operation parses point keys.

Kept marks interpolate matching constructors.
Added marks use target coordinates.
Removed marks remain while leaving points and routes retire.
Kept regions interpolate origin and size.
Mark and region progress stays inside the endpoint interval.

Attached kept points take the current mark height and a horizontal position inside its bar.
Entering and leaving points map their endpoint position onto the current mark.
Diamond attachments take the current diamond centre.
Source attachments survive only for points absent from the target placement array.
A kept point without target incidence detaches and follows ordinary position interpolation.
An unresolved first binding blocks later bindings on unchecked duplicate incidence.
Nodes retain their placement if invalid metadata names them.

`GraphMotion.choosePolicy` (`tools/Tools/View/GraphMotion.lean`) records direct motion or complete endpoint-family relocation.
It checks node-versus-point changes before the empty-family case.
For nonempty node families, changed membership, potentially overshooting movement, or conflicting sweep envelopes select relocation.
A single fixed endpoint node family can reveal directly with clipped growth.
The complete fallback selects old, empty, or target data.
Its marks, routes, regions, attachments, and routing span come from the selected family.
Canvas expansion keeps the selected family's original lane span.

`GraphMotion.Prepared.sample` in that file returns the exact target at or after the endpoint.
This return also covers malformed attachment data and non-resting target values.
The existing endpoint statement in `tools/Tools/View/Motion.lean` remains unchanged.
Its proof consumes the stronger prepared endpoint law.

No Driver, Flow, Graph, connector formula, Test, source-core, dependency declaration, or decisions file changes in this slice.
The existing exporters consume the updated prepared sampler.

## Laws and placement

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Requirement: R14 view navigation.
The placement plan precedes the proofs in `docs/research/2026-10-13-graph-attachment-motion-plan.md`.
Rows 334 (3) and 336 (8) place named tool laws outside registry claims.

| Declaration and path | Proof role | Observation and hypotheses |
| --- | --- | --- |
| `GraphAttachmentMotion.dock_bar`, `tools/Tools/View/GraphAttachmentMotion.lean` | Preservation | A non-node point lies at the current bar height and inside its ordered horizontal interval |
| `GraphAttachmentMotion.dock_diamond`, same file | Preservation | A non-node point lies at the current diamond centre |
| `GraphMotion.family_growth_le`, `tools/Tools/View/GraphMotion.lean` | Preservation | Generated growth or reveal never exceeds its full allocation factor |
| `GraphMotion.family_boxes_inside`, same file | Preservation | A scaled endpoint node box lies inside its allocated box, with nonnegative width |
| `GraphMotion.Prepared.sample_end`, same file | Compatibility | Production sampling returns its complete target at time 1000, for arbitrary prepared data |
| `GraphMotion.prepare_legacySample_eq_legacyReference`, same file | Compatibility | Prepared legacy sampling agrees with the frozen display computation after the named metadata extension |

The legacy extension carries target incidence and the separately retained routing span.
`GraphMotion.reference` keeps the earlier display computation.
No production compatibility theorem claims that its mid-transition values remain that reference.

The attachment laws do not establish caller metadata validity or lookup resolution.
The box law does not establish that supplied endpoint families are separated.
The separation module's fallback law requires separated endpoint envelope families.
No theorem in this slice establishes a complete `Laid.boxesApart` invariant for every valid production transition.
The node swap is a finite profile control.
No observation covers route, mark, region, or text ink clearance.
No scheduler or machine interpretation changes.

## Commands and evidence

Each Lake command exports `LEAN_NUM_THREADS=3` in PowerShell.
Commands run serially in this worktree.

| Command | Result |
| --- | --- |
| `lake build Tools.View.GraphAttachmentMotion Tools.View.GraphMotion Tools.View.Motion` | Pass after both review corrections |
| `lake build Tools.View.FlowSpecimen Tools.View.Motion` | Pass; refreshes the direct fixture dependency after metadata changes |
| `lake build Tools.View.Build Drivers.View` | Pass; direct exporter consumers |
| `lake env lean -DwarningAsError=true --run tools/view/GraphTransitionProbe.lean 0` | Pass; all guard controls run, timed sampling rounds are disabled |
| `lake env lean .lake/graph-attachment-motion-core-audit.lean` | Pass; strict checked audit of both new pure modules |
| `lake env lean .lake/graph-attachment-motion-audit.lean` | New pure modules pass; existing Motion text callers remain outside the ceiling |
| `git diff --check` | Pass |

`CoreAudit.txt` in `docs/research/2026-10-13-graph-attachment-motion-evidence/` reports 286 declarations within `[propext, Quot.sound]`.
It reports no goals and no declarations modulo goals.
The checked walk compares its answers at 2548 captured constants.
Its labels contain only `propext` and `Quot.sound`.

`LandingAudit.txt` in that directory reports two inherited Motion offenders among 57 declarations.
Their exact names are `Tools.View.underKey` and `Tools.View.keptUnchanged`.
Their path traverses `String.Slice.toString`.
No new pure declaration reaches `Classical.choice`.

The first box proof invokes arithmetic search on a conjunction.
Its generated negated-conjunction helper reaches `Classical.choice`.
The final proof splits the four arithmetic observations before search.
The strict checked audit verifies the final result.

`Controls.txt` in that directory retains the final finite-control run.
`ControlCount.json` records 50 guard commands and the two 1001-moment profiles.
The controls include insertion, deletion, moving bars, moving diamonds, detached kept points, regions, and malformed metadata.
They include a moving port at `y=50` on its mark at `y=50`.
The legacy mark stays at `y=100` in the control.
They check node swaps and point-to-node swaps at every integer time from 0 through 1000.
They also check exact target metadata at and after the endpoint.

The probe's timing section still benchmarks the explicitly named legacy sampler.
No performance conclusion about the new production policy follows from that section.
The coordinator owns generated SVG, browser, and complete-export measurements.
