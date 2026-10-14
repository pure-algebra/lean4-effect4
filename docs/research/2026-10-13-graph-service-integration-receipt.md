# Graph service integration receipt

The production connector geometry stays unchanged. The regenerated advanced SVGs match the retained production baseline byte for byte.
The strict checker, ordering, and prepared-motion audits pass.
The rendering producer still reaches the existing text-measurement trust boundary.

Base: `d6285ddf8ab54ef7d5fc3bb32a23831173e45afe`.
Branch: `codex/pegs-port`.
Head: the commit containing this receipt.
The work stays local for the Mac coordinator to merge.

## Integrated commits

| Commit on this branch | Change |
| --- | --- |
| `859122814` | Checked graph input and layout producer |
| `ff715164f` | Prepared rank scores and exact stable-order law |
| `dcc0d1512` | Ordering measurements and receipt |
| `9dd953e33` | Prepared graph and page motion, compatibility law, and driver adoption |

The final integration changes these paths:

- `tools/Tools/View/Flow.lean`: scope the prose to structural constraints and remove the runtime-deadlock claim.
- `tools/view/GraphMotion.lean`: retain one transition outside each recorded motion loop.
- `tools/view/GraphTransitionProbe.lean`: add kept-node measurements and a controls-only mode.
- `tools/view/GraphContractProbe.lean`: render bounded controls for docking, overlap, and canvas bounds.
- `tools/view/graph_contracts.py`: present the actual SVGs with synchronized samples and close-ups.
- `docs/research/2026-10-13-graph-service-assessment.md`: record ownership, mathematical limits, and the next concrete consumers.
- The input-check plan and receipt: apply the controlled-English qualifiers.
- `docs/research/2026-10-13-graph-library-evidence/`: retain the transition measurements and SVG comparison.

No change reaches the program syntax or machine semantics.
No new theorem enters this final integration slice.
The component plans place the landed laws under concept 7, R14, and decisions row 334 (3).

## Commands and results

Run with `LEAN_NUM_THREADS=3` from this worktree.

```powershell
lake build Tools.View.GraphLayout Tools.View.GraphOrdering Tools.View.GraphMotion Tools.View.Motion Tools.View.Specimen Tools.View.FlowSpecimen Tools.View.LiveChecks Tools.Document.Figure Tools.View.Run Drivers.View
lake env lean -DwarningAsError=true --run tools/view/GraphLibraryProbe.lean
lake env lean -DwarningAsError=true tools/view/GraphOrderingAudit.lean
lake env lean -DwarningAsError=true docs/research/2026-10-13-graph-motion-evidence/CoreAudit.lean
lake env lean -DwarningAsError=true --run tools/view/GraphOrderingProbe.lean controls
lake env lean -DwarningAsError=true --run tools/view/GraphTransitionProbe.lean 1
lake env lean -DwarningAsError=true --run tools/Drivers/View.lean --motion 5 specimen tools/view/out/graph-service-specimen
lake env lean -DwarningAsError=true --run tools/Drivers/View.lean --motion 3 flows tools/view/out/graph-service-flows
lake env lean -DwarningAsError=true --run tools/view/GraphMotion.lean tools/view/out/advanced-service-motion
lake env lean -DwarningAsError=true --run tools/view/GraphContractProbe.lean
python tools/view/graph_contracts.py
python tools/view/motion_inspector.py tools/view/out/advanced-service-motion --label Production --out tools/view/out/graph-service-motion.html
python -m py_compile tools/view/graph_contracts.py
git diff --check
```

The combined narrow build and finite controls pass.
The specimen driver reports that every still graph passes its box, descending-edge, allocation, and dimension checks.
The Flow driver reports the same still-graph observations for its specimens.
Those reports do not cover intermediate-frame collision freedom.

The pure module audits report:

```text
Tools.View.GraphCheck: 237 declarations within [propext, Quot.sound], 0 modulo planned goals, 0 planned goals
Tools.View.GraphOrdering: 5 declarations within [propext, Quot.sound], 0 modulo planned goals, 0 planned goals
Tools.View.GraphMotion: 86 declarations within [propext, Quot.sound], 0 modulo planned goals, 0 planned goals
```

The component receipts retain the rendering audit refusals and their dependency paths.
`GraphLayout.checked` inherits `Graph.boxWidth` and Lean's `String.length` path to `Classical.choice`.
The existing Motion and driver offender-name sets do not change in the prepared-motion slice.
No new trust exemption enters this branch.
The unchanged kit manifest warning remains visible in the logs.

## Measured observations

`docs/research/2026-10-13-graph-library-evidence/SvgComparison.json` records the XML and byte comparison.
The report compares every regenerated advanced SVG with `tools/view/out/advanced-motion-before`.
The motion inspector also reads every frame through its SVG inspection boundary.

`docs/research/2026-10-13-graph-library-evidence/TransitionBench.txt` records entry and kept-node sampling measurements.
The new kept-node cases exercise old-key lookup and position movement, without an entry-only workload.
The recorded checksums agree for each paired measurement.
The first small nested-fork sample is slower in this one-pass run.
The other recorded cases improve, including preparation cost.
These are workload-dependent host timings, not a general speed theorem or browser-latency measurement.

## Browser inspection

`tools/view/out/graph-contracts/index.html` displays actual production SVGs with the allocated canvas marked in red.
The browser inspection checks the midpoint, the target endpoint, playback, and the close-ups.
`tools/view/out/graph-contracts/inspection.png` retains the inspected midpoint view.
`tools/view/out/graph-service-motion.html` presents the advanced production flows with fork, join, and node contact navigation.

## Open obligations

The contract controls reproduce moving-bar docking loss, swapping-box overlap, and self-loop ink outside the allocated canvas.
They remain open functional gaps.
The assessment prioritizes explicit occurrence and port identities, shared query snapshots, painted bounds, and cache lifetime.
The next aesthetic pass follows those observations.

No outside Effect implementation gate reaches these view-only changes.
No whole-tree battery or whole-tree gate runs in this slice.
The user's untracked `tools/view/studies/` remains untouched.
