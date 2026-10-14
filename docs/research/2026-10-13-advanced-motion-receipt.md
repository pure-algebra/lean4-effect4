# Advanced graph motion inspection

The coordinator must keep the comparison geometry outside production until contact, curvature, and motion checks agree.
This slice adds recorded motion and comparison tools.
It changes no production connector, machine semantics, or dependency pin.

Base: `68ab804cb4c1dd1bfcb0060652c4983827a7be5e`.
Branch: `codex/pegs-port`.
The commit containing this receipt records the source head.

## Changed files

- `tools/view/GraphMotion.lean` writes six recorded graph sequences.
- `tools/view/motion_inspector.py` shows synchronized full graphs and fork, join, and node crops.
- `tools/view/check_smoothness.py` measures side curvature separately from tangent agreement.
- `tools/view/curvature_study.py` constructs the host curvature comparison.
- `docs/research/2026-10-13-advanced-motion-evidence/` retains compact results and selected SVGs.

`GraphMotion.lean` calls the production choreography and SVG admission boundary.
Its frames reveal fixed program graphs.
They do not represent scheduler execution or decision tapes.
The examples include nested forks, a wide race, a loop, `awaitAll`, nested scopes, and a handler.

The inspector embeds original SVG paths unchanged.
It isolates identifiers and changes crop viewports.
Node contacts come from painted node bodies.
Dummy branch endpoints do not enter the node menu.
Final geometry determines contact classification throughout each reveal.

## Recorded observations

`ContoursSummary.json` records 366 production SVGs, 1298 connector instances, and 13032 side joins.
The exact decimal tangent check reports no issues.
The separate curvature diagnostic reports 6043 curvature mismatches on these frames.
The diagnostic receipt is `docs/research/2026-10-13-smoothness-receipt.md`.

`StudySummary.json` records 44288 exact rational G2 joins before decimal serialization.
G2 here means equal oriented tangent and signed curvature at regular side endpoints.
The study applies Yuksel's split-cubic construction to existing sides.
It leaves deliberate transverse caps unchanged.
The study's largest sampled displacement is about 0.761 SVG units.
That measurement samples 33 parameters per original cubic.
It is neither a continuous displacement bound nor a Hausdorff distance.

Twelve-decimal serialization does not retain exact rational G2 agreement.
The independent diagnostic reports a maximum numerical curvature residual below `1e-8` on the recorded study frames.
Small tangent handles still produce high curvature near the growing tip.
Matching curvature alone establishes no global simplicity, fairness, or collision bound.

The numbered retained SVGs have these roles:

| File | Source |
| --- | --- |
| `0-053.svg` | Production handler motion, sample 53 |
| `1-053.svg` | Curvature study of that sample |
| `2-001.svg` | Production static graph from the reported close-up |
| `3-001.svg` | Curvature study of that graph |
| `look.css` | Production dark and paper tokens |

## Reproduction

Run these commands from the worktree root.

```powershell
$env:LEAN_NUM_THREADS='3'
lake env lean --run tools/view/GraphMotion.lean tools/view/out/advanced-motion-before
python tools/view/curvature_study.py tools/view/out/advanced-motion-before tools/view/out/advanced-motion-study
python tools/view/motion_inspector.py tools/view/out/advanced-motion-before --compare tools/view/out/advanced-motion-study --label Production --compare-label 'G2 study' --out tools/view/out/advanced-motion-inspector.html
python tools/view/check_smoothness.py --self-test
python tools/view/motion_inspector.py --self-test
python -m py_compile tools/view/curvature_study.py tools/view/motion_inspector.py tools/view/check_smoothness.py
git diff --check
```

The Lean driver writes all six sequences successfully.
Both Python self-tests pass.
Python compilation and whitespace checks pass.
The motion inspector checks XML, SVG path grammar, and local references while loading all frames.

This slice adds no theorem or planned goal.
Its evidence consists of finite host checks and browser observations.
The existing production geometry and its axiom gate evidence remain at the base commit.
No whole-tree build or external runtime comparison applies to this tooling slice.

## D3 direction

The owner requests an implementation comparison against D3.
`curveBasis` builds a whole side from local control windows.
It approximates interior guides and retains the endpoint positions.
The existing kit declaration is `Curve.basisSegment` in `Whatwg/Svg/Geometry/Shape.lean`.
The eventual production change should reuse the kit's curve construction.
It should include collar guides in the same side and avoid pinning individual handles afterward.

This recommendation still needs measured clearance, width, motion stability, and the production coordinate conversion contract.
The separate D3 comparison records its source version, concrete outputs, and limitations.
