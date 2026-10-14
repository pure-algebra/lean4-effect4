# Peg geometry receipt

The coordinator must keep the SVG trust boundary explicit when merging this slice.
The data audit passes at `[propext, Quot.sound]`.
Three SVG declarations reach `Classical.choice` through the kit's raw-node value validator.
The final rendering boundary belongs to the coordinator.

## Landing

- Base: `25c97480f797c17cd89b2e7adb7e2c66c67d6c15`.
- Code head: `36d5b01401ce451a00b39c008679cc6d8388bb4d`.
- Branch: `codex/peg-geometry`.
- Worktree: `C:/Users/kokok/Dev/lean4-effect4-peg-geometry`.
- Receipt follows the code commit.
- No push runs.

Changed files:

- `tools/Tools/View/Tube/Belt.lean`: shared tangent normals for outline and casing.
- `tools/Tools/View/Tube/Skeleton.lean`: integer-grid contour trees, tours, tree walks, and translation.
- `tools/Tools/View/Tube/PegFigure.lean`: bodies, slot marking, depth, and the grid action.
- `tools/Tools/View/Tube/PegRender.lean`: rounded cubic paths and the SVG boundary.
- `tools/Tools/View/Tube/PegGlyphs.lean`: the authored peg vocabulary.
- `tools/Tools/View/Tube/Glyphs.lean`: `pegFigure` and `pegStill` for coordinator consumers.
- `tools/Tools/View/Tube/PegChecks.lean`: finite geometry controls.
- `docs/research/2026-10-13-peg-geometry-plan.md`: placement before proof.

## Proof placement

The placement note names concept 7, initial algebras and folds, in `docs/core/semantics.md`.
The properties are tool laws under decisions row 334, point 3.
They add no claim about Effect semantics.

| Declaration in `tools/Tools/View/Tube/Skeleton.lean` | Role | Evidence status | Scope | Consumer |
| --- | --- | --- | --- | --- |
| `Skeleton.tour_move` | Translation connector | Proved | Ordered peg lists, every finite skeleton and grid vector | Tile placement |
| `Skeleton.walk_head` | Helper | Proved | First vertex of every finite tree walk | `Skeleton.walk_closed` |
| `Skeleton.walk_last` | Helper | Proved | Last vertex of every finite tree walk | `Skeleton.walk_closed` |
| `Skeleton.walk_closed` | Closure connector | Proved | First and last tree vertex agree | Tour API |

The walk observation does not establish contour validity or an exact real-curve tangent law.
The host boundary remains the SVG kit's value validation and rendering.

## Commands and results

PowerShell sets `$env:LEAN_NUM_THREADS='3'` before each Lake command.

| Command | Result |
| --- | --- |
| `lake build Tools.View.Tube.PegChecks Tools.View.Tube.GlyphPage` | Passed, including direct consumers `Score` and `Sheet` |
| `lake env lean -DwarningAsError=true .lake/peg-audit.lean` | Passed for the modules listed below |
| `lake env lean -DwarningAsError=true tools/ProbePeg.lean` | Passed the finite smoothness probe and wrote a local preview |
| `git diff --check --cached` | Passed before the code commit |

The audit input is reproducible:

```lean
import Tools.View.Tube.PegChecks
import ProofGraph.AxiomAudit
#axiom_audit Tools.View.Tube.Belt Tools.View.Tube.Skeleton Tools.View.Tube.PegFigure
  Tools.View.Tube.PegGlyphs Tools.View.Tube.PegChecks
```

The audit output is:

```text
#axiom_audit: 330 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

A broader audit reports these exact SVG declarations:

- `Tools.View.Tube.PegFigure.nodes` in `tools/Tools/View/Tube/PegRender.lean`.
- `Tools.View.Tube.PegFigure.still` in `tools/Tools/View/Tube/PegRender.lean`.
- `Tools.View.Tube.Glyphs.pegStill` in `tools/Tools/View/Tube/Glyphs.lean`.

Each reaches `SvgNode.raw`, then `RawNode.valuesAnywhere`, then string validation and `Classical.choice`.
No exemption changes land in this branch.

## Finite evidence

`PegChecks` checks every authored glyph at the twelve-pixel slot step.
The checks observe closed rounded paths, tangent tolerance, casing distance, cell bounds, and distinct peg data.
The tangent tolerance is three thousandths of a pixel.
The casing distance tolerance is two thousandths of a pixel around `LINE`.

A control rejects contained pegs with no tangent.
A control renders a single cap as two semicircles.
The fork controls keep its nonconsecutive repeated bend visit and five cubics per original tour peg.
`pegOutlines` uses `List.eraseReps`, which removes adjacent equal pegs only.

The local preview rasterizes the authored SVG path data without a browser.
Visual review catches contour-intent defects and guides the fork, bracket, port, and series changes.
That review establishes no theorem and measures no browser rendering behaviour.

The old tube declarations remain the films' imported motion carrier.
The coordinator owns the static gallery and tile integration.
No Effect runtime or TypeScript target behaviour changes in this slice.
No outside-implementation behaviour gate applies to this view-only slice.

## Remaining work

- Move generic belt arithmetic, skeleton data, and figure data into the kit through explicit connectors.
- Integrate `Glyphs.pegFigure` and `Glyphs.pegStill` in the static gallery and tile fold.
- Resolve the exact SVG rendering boundary at the coordinator's audit anchor.
- Port films before deleting their tube geometry and motion declarations.
- State further geometric laws with their numerical hypotheses before proving them.

The kit seat receives the frozen source commit and reserves the generic move.
