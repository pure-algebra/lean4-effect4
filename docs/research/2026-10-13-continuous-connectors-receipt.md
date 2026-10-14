# Continuous connector landing

The coordinator must align `lakefile.toml` with the manifest pin when merging.
The PC fence leaves that file with the coordinator.
Both repositories contain local commits without pushes.

## Commits

| Item | Commit |
| --- | --- |
| Effect4 base | `98d32093d` |
| Effect4 implementation | `10b386fa9` |
| Kit base | `1ecaf5c1d422a1c98b9d61717ba777b7507d7bf6` |
| Kit source | `e77e9d0ed68d120ecce5477d16c086cc40cc3561` |
| Kit pin with projections and receipt | `e51195721f47fa767fb84f918dc439e76d83071f` |

The Effect4 branch is `codex/pegs-port`.
The kit branch is `codex/ribbon-edges`.
`2026-10-13-continuous-connectors-evidence/ChangedFiles.txt` lists the changed paths from the Effect4 base.

## Behaviour

The old renderer overlaps closed body and collar paths.
The retained scope specimen has an exposed tangent mismatch of approximately 43.256559 degrees.
`check_connectors.py --kink-fixture` measures that mismatch from the emitted cubics.

`Connector` in `tools/Tools/View/Connector.lean` reserves flare necks before constructing paired sides.
The adjacent cubics share their integer anchors and tangent handles.
`Whatwg.Svg.Scene.Ribbon` owns the paired carrier and perimeter assembly.
Each graph connector emits one closed path.
Bars and node frames remain separate drawing objects.

`ConnectorMemo` in `tools/Tools/View/ConnectorMemo.lean` caches each outline by all construction inputs.
The key includes both docking offsets and radii.
`SceneBridge` in `tools/Tools/View/SceneBridge.lean` converts integer records for graph and peg drawing.
The old peg-specific bridge is removed after its callers migrate.

The horizontal-route control checks the graph admission and its emitted body.
It prevents the replacement from dropping an admitted route with zero vertical drop.
The growing-contact controls retain the painted bar and box surfaces.

## Proof placement

The concept is `initial-algebras-folds`, serving R14 through the graph drawing.
These are tool laws under decisions row 334(3), not machine registry claims.
The placement precedes the proofs in `2026-10-13-continuous-connectors-plan.md` and `2026-10-13-connector-plan.md`.

| Declarations | Role | Observation and consumer |
| --- | --- | --- |
| `Connector.Cache.valid_empty`, `cached_eq`, `cached_valid` | Cache premise, observation and invariant | Exact integer outlines across graph frames |
| `SceneBridge.from_cubic`, `cubic_from` | Record conversion | Arbitrary integer cubic controls return unchanged |
| `Connector.catmull_shared`, `pinStart_handle`, `pinEnd_handle` | Geometry helpers | Equal handles for the constructed side and neck joins |

The recovery laws move from the connector module into the shared record bridge.
The kit receipt records the integer ribbon laws and their narrower endpoint observations.
The production connector imports no rational ribbon operations.

## Commands and results

All Lake commands use `LEAN_NUM_THREADS=3`.
The evidence directory is `2026-10-13-continuous-connectors-evidence/`.

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build Tools.View.Graph Tools.View.LiveChecks Drivers.View Tools.View.Tube.PegChecks Tools.View.Tube.PegRender` | Pass | `Build.txt`, `FinalBuild.txt` |
| `lake env lean docs/research/2026-10-13-connector-evidence/Controls.lean` | Pass | `Controls.txt` |
| `lake env lean docs/research/2026-10-13-continuous-connectors-evidence/Audit.lean` | 202 declarations within the strict ceiling, no planned goals | `Audit.txt` |
| `lake env lean docs/research/2026-10-13-organic-graph-evidence/Audit.lean` | Existing rendering dependencies remain; no new offender | `RenderingAudit.txt`, `AuditComparison.json` |
| `lake env lean docs/research/2026-10-13-continuous-connectors-evidence/PegAudit.lean` | Existing SVG dependencies remain; no new offender | `PegAudit.txt`, `PegAuditComparison.json` |
| `lake env lean --run tools/Drivers/View.lean --motion 1 flows tools/view/out/continuous-after` | 16 admitted graphs | `Flows.txt` |
| `lake env lean --run tools/Drivers/View.lean --motion 5 build pFork tools/view/out/continuous-motion` | Seven keyframes and 24 intermediate pictures | `Motion.txt` |
| `lake env lean --run tools/view/GraphDetails.lean tools/view/out/continuous-details` | Eight growing-contact pictures | `Details.txt` |
| `lake env lean --run tools/Drivers/View.lean --look organic --motion 1 flows tools/view/out/continuous-noise` | 16 admitted graphs with noise | `Noise.txt` |
| `python tools/view/check_connectors.py --self-test` | 18 controls pass | `CheckerControls.json` |

The exact contour gate runs on all four output directories.
The static and noisy directories also compare connector keys against `continuous-before`.
`Summary.json` measures 71 SVG files, 304 connector instances, and 2758 side joins without findings.
`Contours.json`, `AnimatedContours.json`, and `NoiseContours.json` retain the per-file observations.
The default tangent test uses exact decimal fractions, zero determinant, and positive dot product.
Every side segment must also have nonzero endpoint tangents.
The two transverse caps have deliberate corners.

`inspect_svg.py` validates XML, path syntax, identifiers, and local references in every output directory.
The static examples decrease from 467 paths to 290 paths.
This measures emitted paths, without claiming a measured browser speedup.
`AssemblyComparison.json` records unchanged SVG bytes across 55 files after the kit assembly replaces the temporary local assembly.

## Axiom boundaries

The new scene bridge, connector, memo and kit ribbon pass the strict audit.
The rendering audit still reports the same 46 declarations that reach `Classical.choice`.
The peg rendering audit still reports `PegFigure.nodes` and `PegFigure.still` through SVG raw-content parsing.
The retained baseline and comparison files identify both unchanged sets.
No axiom exemption or trust ceiling changes.

The kit's rational `Span.ofEdges` uses Geometry's existing ceiling.
Effect4's production connector uses the strict integer `Scene.Ribbon` instead.
The kit receipt records its full build, trust, generation, citation and scoped kernel-replay gates.

## Visual evidence and limits

The browser inspection uses the original SVG paths at 20 CSS pixels per logical pixel.
The scope, bar, growing-box, and noisy contacts receive close-up inspection.
Dark and paper backgrounds receive inspection.
`tools/view/out/continuous-inspection.html` retains the static before-and-after comparison.
`tools/view/out/continuous-animation-inspection.html` retains the growing-contact views.
The graph player is `tools/view/out/continuous-after/index.html`.

The SVG and browser observations are finite, host-only evidence.
The local laws do not establish universal simplicity, clearance, or real-circle exactness.
The kit's general chaining and real-curve obligations remain open.
This slice changes no program syntax, machine relation, or Effect runtime behaviour.
