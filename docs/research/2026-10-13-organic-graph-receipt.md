# PC graph connector receipt

The coordinator must retain the SVG dependency pin already present in the manifest.
This landing changes graph rendering and its finite checks.
It changes no machine declaration or program syntax.

## Commits and files

The base is `e9cf615b5047ac3a4d1be053291434fd757b9b7d`.
The implementation head is `2ff01f9b4`.
The branch is `codex/pegs-port`.
The commits remain local.

| Files | Change |
| --- | --- |
| `tools/Tools/View/Graph.lean` | Shared painted box bounds and bar surfaces; collars bounded by visible room |
| `tools/Tools/View/LiveChecks.lean` | Finite controls for static and animated contacts |
| `tools/Tools/View/GraphCheck.lean` | Located input and allocation checks with exact observation laws |
| `tools/Tools/View/Flow.lean` | Addressed allocation for empty regions |
| `tools/Tools/View/FlowLaws.lean`, `tools/Tools/View/FlowOrder.lean` | Existing consumer proofs repaired in place |
| `tools/Tools/View/FlowSpecimen.lean` | Nested forks, races, loops, releases, unresolved waits and empty regions |
| `tools/Drivers/View.lean` | Refusal before output, per-pane SVG references, readable scales |
| `tools/view/GraphDetails.lean` | Reproducible animated contact specimens |
| `tools/view/inspect_svg.py` | Unchanged-path close-ups, themes, comparison and pixel probes |

## Observations

The join collar formerly stopped half a pixel above its painted bar.
The target collar now shares the bar painter's integer origin.
Box endpoints now follow the bounds used by the painter during growth.
A source collar no longer extends beyond a short revealed tip.

The browser probe samples SVG coordinate `(158.025, 494.775)` at twenty CSS pixels per unit.
The old dark sample is `[20,17,13,255]`; the new sample is `[236,230,220,255]`.
The old paper sample is `[247,244,238,255]`; the new sample is `[27,31,42,255]`.
These are bounded browser observations from the generated paths.

The close-ups also inspect a growing target, a short revealed tip and a cross-region wait arrow.
The player probe finds no repeated ID across its two rendered SVG panes.
Actual-size mode scrolls within the panes without page overflow.

## Commands and results

All Lake commands use `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Tools.View.FlowSpecimen Tools.View.FlowLaws Tools.View.FlowOrder Tools.View.LiveChecks Drivers.View` | Pass |
| `lake env lean docs/research/2026-10-13-organic-graph-evidence/DriverRefusal.lean` | Invalid back-route source refuses before writing |
| `lake env lean docs/research/2026-10-13-graph-check-evidence/Controls.lean` | All specimens pass; malformed controls refuse |
| `lake env lean docs/research/2026-10-13-empty-region-evidence/Controls.lean` | Empty, nested and sequential regions pass |
| `lake env lean --run tools/Drivers/View.lean --look organic --motion 1 flows tools/view/out/graph-flows-final` | Sixteen graph frames pass every reported check |
| `lake env lean --run tools/Drivers/View.lean --look organic --motion 5 build pFork tools/view/out/graph-motion-final` | Seven frames and twenty-four transition pictures render |
| `lake env lean --run tools/view/GraphDetails.lean tools/view/out/graph-details` | Eight contact specimens render |
| `python tools/view/inspect_svg.py --self-test` | Valid controls pass; malformed paths and SVG controls refuse |
| `python tools/view/inspect_svg.py tools/view/out/graph-flows-final --validate-only` | Sixteen SVGs, 467 paths and 149 references pass |
| `python tools/view/inspect_svg.py tools/view/out/graph-motion-final --validate-only` | Thirty-one SVGs, 410 paths and 181 references pass |
| `python tools/view/inspect_svg.py tools/view/out/graph-details --validate-only` | Eight SVGs and 48 paths pass |
| `git diff --check` | Pass |

## Axioms and placement

The checker serves concept `initial-algebras-folds`, R14, through its named finite rendering observations.
Its plan and receipt record each theorem's scope and consumer.
The empty-region proofs retain their existing layout claim and order consumer.
Their separate receipts contain the placement and commands.

The checker audit passes 219 declarations with no goals.
The layout-law audit passes 448 declarations with no goals.
`2026-10-13-organic-graph-evidence/RenderingAudit.txt` records the rendering audit.
`2026-10-13-organic-graph-evidence/AuditComparison.json` compares its exact offender set with the base.
Both sets contain the same 46 declarations reaching `Classical.choice` through existing rendering and host operations.
The contact exporter has one host-only `main` caller reaching that axiom through filesystem operations.
`2026-10-13-organic-graph-evidence/DetailsAudit.txt` records that boundary.
No exemption changes.

## Remaining boundaries

The graph checker tests allocation rectangles, endpoint lookup and downward order.
It excludes ink bounds, text bounds and arbitrary path self-intersection.
The SVG checker checks syntax and references, not geometric topology.
The fixtures read program structure; they establish no scheduling relation or program typing claim.
No external runtime behaviour gate is reached by these tool-only changes.

The generic consolidation opportunity remains `Grow.stroke` and the kit's `Geometry.Stroke` or `Geometry.Ribbon`.
A transfer needs an explicit observation for integer rounding and the existing stroke-cache laws.
Renaming the collar cannot repair a wrong application docking surface.
An oriented, single-outline connector remains a separate slice for arbitrary diagonal docking.

The earlier peg studies remain untracked and separate from this landing.

