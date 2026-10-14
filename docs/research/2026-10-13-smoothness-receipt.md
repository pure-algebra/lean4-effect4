# Connector curvature diagnostic

The coordinator must distinguish tangent agreement from curvature agreement in the viewer's acceptance report.
The measured production seams have exact tangent agreement and frequent curvature jumps.

Base: `68ab804cb`.
Branch: `codex/connector-smoothness`.
The source is `tools/view/check_smoothness.py`.
This slice changes no Lean geometry, proof, cache, or rendering source.

## Observation and scope

The diagnostic reads emitted decimal coordinates as exact fractions.
For a regular cubic endpoint, it computes velocity `v` and acceleration `a`.
Signed curvature is `cross(v, a) / |v|³` in reciprocal SVG user units.
The exact equality test compares signs and squared rational numerators and denominators.
Floating point supplies reported curvature magnitudes and angles only.

The diagnostic checks all joins within the paired sides.
It excludes the two deliberate transverse caps.
It reports flat bar and node contacts separately.
Those contacts establish exact point membership on a supplied flat boundary segment.
They establish no theorem about the whole graph's visible filled union.

Stationary endpoints have undefined regular curvature in this diagnostic.
A nonzero higher endpoint direction may still establish tangent agreement.
A constant cubic has no tangent and produces a diagnostic issue.
The self-test retains each case, plus a C1 seam with a curvature jump.

This is a finite host diagnostic, not a Lean theorem or scheduler simulation.
No Lake command runs for this Python-only slice.
No axiom audit applies to the Python diagnostic.

## Ranked findings

| Priority | Measured location | Diagnosis |
| --- | --- | --- |
| 1 | `after/001.svg`, `(160.848, 490.758)` | Exact C1, curvature `0 → -0.231253` |
| 1 | `after/001.svg`, `(145.2, 503.5)` and `(145.2, 514.5)` | Straight body and quarter-arc neck differ by `0.178216` |
| 2 | `after/009.svg`, `(90.8, 506)` | Neck curvature reverses sign, `-0.163364 → +0.681718` |
| 3 | `details/dark-655.svg`, `(55.163, 66.626)` | Short partial tip reverses curvature, `+0.919256 → -2.334961` |
| Separate contact | `after/001.svg`, `(150.7, 498)` | Connector lip meets flat bar tangentially, with curvature jump `0.178216` |

The supplied crop is `[139, 479, 24, 38]` in `after/001.svg`.
Every measured side seam in that crop has equal, nonzero integer derivative handles.
The slight join appearance therefore has a curvature discontinuity despite tangent agreement.
Noise does not explain the straight-body case.

`Connector.pinStart` and `Connector.pinEnd` in `tools/Tools/View/Connector.lean` constrain first derivative handles.
They do not constrain the adjacent second derivative.
`Grow.segmentThrough` in `tools/Tools/View/Organic.lean` supplies C1 Catmull–Rom segments.
Its shared-handle law states no curvature agreement.

The default connector's own joined perimeter does not combine bar or node contours into one perimeter.
Its lip's nonzero arc curvature also differs from a flat bar's zero curvature.
Changing neck handles alone cannot establish that separate contact observation.

## Measured runs

The retained `Report.json` covers 40 SVGs, 214 connectors, and 2052 side seams.
It reports zero exact tangent failures and 1412 exact signed-curvature mismatches.
The inputs contain final, noisy, and partial-detail fixtures.
All forty inputs are retained below `docs/research/2026-10-13-smoothness-evidence/`.

`AdvancedMotion.json` measures the coordinator's six production motion sequences.
It covers 366 SVGs, 1298 connectors, and 13032 side seams.
It reports zero exact tangent failures and 6043 curvature mismatches.
Its compact rows retain every input hash and ranked locations.

The largest motion curvature jump occurs in `handler-scope/053.svg` at `(174.887, 295.673)`.
The measured signed curvature changes from `16.230719` to `57.494199`.
The shared integer handle has length about `0.03766` SVG units.
That small denominator amplifies curvature at a tiny local feature.
This measurement alone does not establish a visible pixel defect.

## Study comparison

The coordinator's host G2 study remains outside production.
`StudyMotion.json` covers its 366 serialized SVGs and 44288 side seams.
The largest numerical curvature residual is about `9.7e-9`.
The exact decimal tangent test fails at 8730 seams after twelve-decimal serialization.
The exact decimal curvature test fails at 10751 seams.
These failures must not be reported as exact serialized G2 agreement.

The study still has high local curvature near the production micro-handle case.
Its reported curvature reaches about `66.302638` at an adjacent inserted seam.
The disappearance of a curvature jump does not establish shape fairness.

`HandlerShape32.json` retains finite shape samples for the original and study `handler-scope/053.svg`.
Neither sampled polyline has a proper crossing.
The minimum paired-side distance is about `0.481433` in both.
Neither sampled normal gap changes sign.
The sample excludes no possible intersection between its sample points.
Local chord backtracking counts depend on the subdivision's new chords.
They cannot by themselves establish improved fairness between these different subdivisions.

## Reproduction

Use Python 3 with the standard library.

```powershell
python tools/view/check_smoothness.py --self-test
python tools/view/check_smoothness.py docs/research/2026-10-13-smoothness-evidence/after docs/research/2026-10-13-smoothness-evidence/details docs/research/2026-10-13-smoothness-evidence/noise --crop 139 479 24 38 --compact --json .lake/smoothness.json
python tools/view/check_smoothness.py docs/research/2026-10-13-smoothness-evidence/after/001.svg --max-curvature-jump 0.05
python tools/view/check_smoothness.py docs/research/2026-10-13-smoothness-evidence/motion-original/handler-scope-053.svg docs/research/2026-10-13-smoothness-evidence/motion-study/handler-scope-053.svg --shape-key '[]/join/1→[]/join' --compact --json .lake/handler-shape.json
```

The self-test and ordinary production diagnostic return exit zero.
The requested curvature cutoff returns exit one on the retained production fixture.
The study's exact decimal diagnostic returns exit one, as described above.
The cutoff is an explicit finite diagnostic setting, not a new production requirement.

The coordinator retains the motion producer and study generation commands in its own receipt.
The compact broad motion report does not retain every source SVG in this slice.
The highest-ranked original and study fixture remains portable for focused reproduction.
