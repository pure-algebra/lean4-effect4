# Board slice receipt

The coordinator must adapt Sheet callers to checked film results before merging.
`Score.film` and `Queue.film` return `Except String SvgNode`.
The rendering audit refuses the rendering declarations.
The observer proof audit passes under `[propext, Quot.sound]`.

## Commits and scope

Base: `25c97480f797c17cd89b2e7adb7e2c66c67d6c15`.
Implementation head: `feac6bc7608a5056fbbd02f632e9b68f33c7aff0`.
Branch: `codex/peg-board`.
Worktree: `C:/Users/kokok/Dev/effect4-peg-board`.

| Changed path | Change |
| --- | --- |
| `tools/Tools/View/Tube/Board.lean` | Generic observer fold and conditional projection law |
| `tools/Tools/View/Tube/Board/Film.lean` | Checked fixed structures, shared paths, kit changes-only channels |
| `tools/Tools/View/Tube/Score.lean` | Real trace consumer and fixed staff film |
| `tools/Tools/View/Tube/Queue.lean` | Evaluated cell snapshots and fixed pipework film |
| `tools/Tools/View/Tube/Physics.lean` | Retired unused sampled inertia implementation |
| `docs/research/2026-10-13-seat-board-*` | Plan, probes, command outputs, and this receipt |

No core semantics, root imports, batteries, lakefile, or decisions row changes land here.
The coordinator repairs stale Physics citations in Motion and Glyphs.
The coordinator replaces `Queue.run` and `Score.pictures` callers in Sheet.
`Queue.picture` drops its unused previous-marking parameter.

## Definitions and observations

`Board.fold` in `tools/Tools/View/Tube/Board.lean` uses caller state, command, marking, and change types.
The observer reads both existing states around the transition.
It evaluates a checked Score control once.
It derives fresh notes from that control's new trace suffix.

`Board.check` in `tools/Tools/View/Tube/Board/Film.lean` refuses repeated keys and changed invariant rendering fields.
The refusal names the snapshot and key.
Filled marks keep width and dash.
Stroke width and dash remain channels.
The unchecked writer stays private.
The kit owns `Smil.marking` and its replay law.
The writer shares fixed path definitions through SVG references.

The Score film fixes its final staffs before playing.
Structural elements appear at their recorded control boundary.
Units and hollows change at those boundaries.
Event columns retain trace order.
The film assigns no timing within a control.

The Queue film fixes its inlet at the greatest recorded waiting load.
Its contents come from evaluated cell snapshots and transient replies.
It omits sag interpolation, inertia, carried swells, and pressure surges.
It creates no store event from the trace.
The active films replace the sampled film consumers.
Rule 184 remains open because these recorded boundaries already specify the contents.

## Proof placement

The plan records placement before proof work in `docs/research/2026-10-13-seat-board-plan.md`.

| Theorem | Placement |
| --- | --- |
| `Board.fold_projection`, `tools/Tools/View/Tube/Board.lean` | `initial-algebras-folds`; proposed tool question `view-board-projection-fold`; role invariant; R14 groundwork |
| `Board.fold_append`, `tools/Tools/View/Tube/Board.lean` | Helper of that question; command-list composition |

The projection observation is equality after a finite command prefix.
Its hypothesis requires transition agreement for the chosen projection.
The conditional theorem leaves that hypothesis open for each real machine projection.
It establishes no event-only store projection, progress, liveness, or core requirement status.
The host boundary stays in `docs/core/host-boundary.md`.

The fixed-film formation check has a proposed tool placement in the plan.
This slice proves no theorem against an independent geometric judgment for that check.
Finite red controls show its changed-path and duplicate-key refusals.

## Checks and measured outputs

PowerShell sets `$env:LEAN_NUM_THREADS='3'` for each command below.

| Command | Result and retained output |
| --- | --- |
| `lake build Tools.View.Tube.Board Tools.View.Tube.Board.Film Tools.View.Tube.Score Tools.View.Tube.Queue` | Exit 0; `docs/research/2026-10-13-seat-board-build.txt` |
| `lake env lean -DwarningAsError=true docs/research/2026-10-13-seat-board-audit.lean` | Exit 0; `docs/research/2026-10-13-seat-board-audit.txt` |
| `lake env lean -DwarningAsError=true docs/research/2026-10-13-seat-board-render-audit.lean` | Exit 1; `docs/research/2026-10-13-seat-board-render-audit.txt` |
| `lake env lean -DwarningAsError=true docs/research/2026-10-13-seat-board-probe.lean` | Exit 0; `docs/research/2026-10-13-seat-board-probe.txt` |
| `git diff --check` | Exit 0 before the implementation commit |

The rendering audit names every exception.
`Board.reference` reaches `Classical.choice` through the kit's `SvgNode.raw` type and string traversal.
The still renderers also reach it through existing rational outline arithmetic.
The observer and its theorems reach no such exception.
The fixed-field checks and snapshot projections reach no such exception.
The raw audit output supplies the exact declarations and dependency paths.

The finite probes check real Score and Queue recordings.
They check distinct keys, fixed structures, hollow fibers, waiting offers, and waiting takers.
They check SVG content and XML writing for films and reduced-motion stills.
`Measure.costOf` in `tools/Tools/View/Tube/Measure.lean` supplies animation and path-byte counts.
The retained probe output supplies film byte counts.

## Open integration work

The coordinator builds Sheet and its driver after adapting the callers.
The coordinator measures page generation and full page sizes.
Browser observation remains open for this isolated slice.
The existing Effect behaviour gates have no changed source in this view-only slice.
No whole-tree battery or axiom sweep runs here.
No push occurs.
