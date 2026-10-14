# D3 whole-side curve comparison

The coordinator must use the knot-guide candidate for visual review.
The control-guide candidate introduces sampled crossings that the supplied source contours do not have.
The advanced knot-guide candidate retains a local backtracking finding.

**Proof role:** none.
**Evidence status:** finite probe.
**Scope:** supplied filled forward connectors in SVG coordinates.

## Placement and boundaries

This work states no Lean theorem.
It changes no production declaration, program syntax, or machine definition.
It requires no proof placement or axiom gate.
The observation comprises contour format, exact endpoint coordinates, endpoint tangents, signed curvature, and sampled contour shape.

G1 means agreement of oriented tangent directions.
G2 means agreement of signed curvature at a regular G1 join.
The report distinguishes exact decimal comparisons from floating-point tolerances.
The probe establishes neither exact G2 after decimal serialization nor the topology of the visible filled union.
The endpoint line/cubic joins have unequal parameter speeds.
The original transverse caps remain unchanged.

## Source and attribution

`tools/view/d3_curve_study.mjs` invokes the actual `curveBasis` from pinned `d3-shape@3.2.0`.
It streams one whole side per D3 curve instance.
It converts each D3 line command to a linear cubic for the existing diagnostic format.

The default knot-guide strategy uses side vertices and the original endpoint tangent guides.
The explicit control-guide strategy uses the original cubic control polygons.
Both strategies remove consecutive duplicates only when both corresponding sides contain them.
Both retain original side endpoints and transverse caps.

The source is Mike Bostock's [D3 basis implementation](https://github.com/d3/d3-shape/blob/v3.2.0/src/curve/basis.js).
The package uses the ISC license.
Each retained JSON report includes the source digest and the package's full license notice.
The package installation lives under ignored `tools/view/out/d3-oracle`.

## Changes

- `tools/view/d3_curve_study.mjs` selects the pinned package and streams its curve API.
- `tools/view/d3_curve_study.py` handles XML, keeps caps, and invokes the existing finite diagnostics.
- `docs/research/2026-10-13-d3-study/*.json` retain the reports.
- This receipt records the scope and commands.

Base: `880aac65022f0ec0101e16fd29d34f39f3946780`.
Head: the commit adding this receipt on `codex/connector-smoothness`.
The pre-existing diagnostic and evidence changes in this worktree remain outside this landing.

## Commands and evidence

The JavaScript syntax check and Python bytecode check succeed.
The overlap control refuses an output directory inside the source directory.
The D3 commands finish and write reports.
The report's tolerance result and sampled-shape result remain separate.
Local-chord backtracking depends on subdivision.
Different source and candidate counts do not establish an improvement in a shared geometric observation.

```powershell
npm --prefix tools/view/out/d3-oracle install --ignore-scripts --no-audit --no-fund d3-shape@3.2.0
node --check tools/view/d3_curve_study.mjs
python -m py_compile tools/view/d3_curve_study.py
$study_root = 'C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/tools/view/out'
node tools/view/d3_curve_study.mjs --source "$study_root/continuous-after" --output "$study_root/continuous-d3" --guides controls --shape 001.svg --shape 009.svg
node tools/view/d3_curve_study.mjs --source "$study_root/continuous-after" --output "$study_root/continuous-d3-knots" --guides knots --shape 001.svg --shape 009.svg
node tools/view/d3_curve_study.mjs --source "$study_root/advanced-motion-before" --output "$study_root/advanced-motion-d3" --guides controls --shape handler-scope/001.svg --shape handler-scope/053.svg --shape await-all/053.svg --shape nested-forks/053.svg --shape nested-scopes/053.svg --shape race-loop/053.svg --shape wide-race/053.svg
node tools/view/d3_curve_study.mjs --source "$study_root/advanced-motion-before" --output "$study_root/advanced-motion-d3-knots" --guides knots --shape handler-scope/001.svg --shape handler-scope/053.svg --shape await-all/053.svg --shape nested-forks/053.svg --shape nested-scopes/053.svg --shape race-loop/053.svg --shape wide-race/053.svg
```

The producer copies SVG frames without connectors unchanged.
It also copies `look.css` and `motion.json` where the source supplies them.
The coordinator owns the comparison viewer.

| Retained evidence | Observation |
| --- | --- |
| [ContinuousControls.json](2026-10-13-d3-study/ContinuousControls.json) | Whole control polygons on static frames |
| [ContinuousKnots.json](2026-10-13-d3-study/ContinuousKnots.json) | Side vertices and endpoint guides on static frames |
| [AdvancedControls.json](2026-10-13-d3-study/AdvancedControls.json) | Whole control polygons on motion frames |
| [AdvancedKnots.json](2026-10-13-d3-study/AdvancedKnots.json) | Side vertices and endpoint guides on motion frames |

## Open work

Review the knot-guide candidate's moving shapes in the coordinator's viewer.
Resolve the remaining local backtracking finding before selecting a production construction.
Define a production construction and place any required geometry obligations before proving them.
No measured tolerance establishes exact decimal tangent or curvature agreement.
No finite sampling establishes the absence of intersections between all curves.
