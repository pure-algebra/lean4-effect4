# Graph bounds receipt

The coordinator must use the prepared drawing's dimensions when exporting a page.
`pageSize` remains an allocation estimate.
`PageDrawing.size` fits graph geometry and retains the other page allocations.
It certifies no text ink or arbitrary shifted-line geometry.

## Commits and scope

- Named base: `26436e79195664380bf7861c307395e093e91e48`.
- Root seed: `ad8b0075d`, applied locally as `de71a80ff`.
- Implementation: `0576f464087a94274c9988d52c1e563d73fda898`.
- Documentation and probe follow-up: `2fe622dae61e01b29e809846718f9b48c7ed1ff6`.
- Branch: `codex/graph-paint-bounds`.
- Worktree: `C:/Users/kokok/Dev/effect4-graph-performance`.

Cherry-pick the implementation and its follow-up.
Do not cherry-pick the local copy of the root seed.

The source commits change these files:

- `tools/Tools/View/PaintBounds.lean`.
- `tools/Tools/View/GraphBounds.lean`.
- `tools/Tools/View/Graph.lean`.
- `tools/Tools/View/Flow.lean`.
- `tools/Tools/View/Page.lean`.
- `tools/view/GraphBoundsAudit.lean`.
- `tools/view/GraphBoundsProbe.lean`.
- `docs/research/2026-10-13-graph-bounds-plan.md`.

## Geometry and consumers

`PaintBounds.loopSegment` in `tools/Tools/View/PaintBounds.lean` owns the existing self-loop's four controls.
The renderer and both allocation producers use that constructor.
The graph and flow producers reserve the loop control hull's right and bottom sides.
Both producers retain their original lane span in `Laid.routingWidth`, including layouts without expansion.
Legacy hand-built layouts retain the seed's fallback to their canvas width.

`PaintBounds.call` reports resolved geometry envelopes.
It uses the kit's integer control hull for cubics.
It adds the rounded half-weight margin for snapped curve strokes.
It rounds filled shape envelopes outward from milli-units.
It excludes clip and hit calls from the geometry observation.
Its report records text metrics as unmeasured.

`GraphBounds.viewport` in `tools/Tools/View/GraphBounds.lean` accepts already-resolved calls.
It unions their geometry envelope with the allocated canvas.
Its optional halo reserves a caller-selected margin.
It returns the fitted size and translation without changing the route coordinates.

`pageDrawingCached` in `tools/Tools/View/Page.lean` resolves the graph once.
`PageDrawing` retains its five call groups, graph origin, viewport, cache, size and text-metric observation.
`PageDrawing.calls` translates the graph group exactly once.
The coordinator migrates the live and batch consumers to those shared fields.

## Proof placement

Proof role: tool laws under decisions row 334 (3).
Evidence status: proved within the pure helper modules.
Scope: integer envelopes, list aggregation and nonnegative optional halo margins.

The placement plan precedes proof work.
It serves concept 7's fold congruence and aggregation, and R14's live authoring view.
The laws establish these observations:

- `PaintBounds.roundOut_covers`: outward unit conversion retains the stored sides.
- `PaintBounds.call_inside`: each reported call envelope lies inside the collected envelope.
- `PaintBounds.allocated_inside_fit`: fitting retains the allocated canvas.
- `PaintBounds.geometry_inside_fit`: fitting contains the reported geometry envelope.
- `PaintBounds.reserveCanvas_notShrink`: loop reservation retains both allocated far sides.

All five declarations live in `tools/Tools/View/PaintBounds.lean`.
The graph viewport consumes the fitting laws.
The graph and flow producers consume the reservation law.
No law states a curve sampling, font metric, antialiasing, clipping intersection or rasterization theorem.
The host boundary remains the boundary in `docs/core/host-boundary.md`.

## Commands and results

The commands run under PowerShell with `LEAN_NUM_THREADS=3`.

```powershell
lake build Tools.View.PaintBounds Tools.View.GraphBounds Tools.View.Graph Tools.View.Flow Tools.View.Page Tools.View.Program Tools.View.Run Tools.View.FlowSpecimen Tools.Document.Figure Tools.View.FlowLaws Tools.View.FlowOrder
lake env lean -DwarningAsError=true tools/view/GraphBoundsAudit.lean
lake env lean -DwarningAsError=true --run tools/view/GraphBoundsProbe.lean .lake/graph-bounds-controls
python scripts/check-language.py --strict docs/research/2026-10-13-graph-bounds-plan.md
```

The narrow build passes.
The plan passes the controlled-English check.
The pure helper audit passes.
The retained output is `docs/research/2026-10-13-graph-bounds-pure-audit.txt`.

```text
#axiom_audit: 93 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The finite probe passes allocation, unit conversion, viewport translation and page-panel geometry controls.
The retained output is `docs/research/2026-10-13-graph-bounds-controls.csv`.
Its cases include loops, back routes, noisy organic drawing, wide strokes, overshoot and negative origins.
It also checks exact call equality after canvas-only expansion.
The command generates SVG controls under `.lake/graph-bounds-controls`.
Those local files are regenerable outputs.

The whole rendering-module audit retains its String and program-text dependencies.
Its output is `docs/research/2026-10-13-graph-bounds-rendering-audit.txt`.
That audit reports `Classical.choice` through the existing String operations and program text rendering.
The new drawing preparation functions inherit those paths.
The pure helper audit above is a separate observation.

Lake reports the existing `whatwg` manifest revision warning.
The source commits change no dependency pin.

## Coordination and open work

A consumer build also exposes the root seed's missing metadata fields in `Motion.sampleLaid`.
Its end law fails because the sampled record omits `attachments` and `routingWidth`.
The coordinator assigns that repair to the motion lane.
This lane edits no motion file.
The previously retained ordering probe also needs the coordinator's allocation-metadata update.

The bounds slice introduces no Effect judgment or generated-code relation.
No outside-implementation behaviour gate reaches this view-only slice.
The pure helper observations have no open proof obligations.
Full text ink and raster bounds remain host-dependent observations.
