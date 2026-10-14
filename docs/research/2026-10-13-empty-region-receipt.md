# Empty Flow region receipt

The region allocates an addressed point before margins when its body has no items.
The coordinator can now render the empty-scope specimen without a negative region origin.

Base: `bf87bb067c9b7588078ab2bfbf53ae400c5b7c0d`.
Code head: `434b5f0ef25d9a1b9620cb77e139213dccee8b97`.
Branch: `codex/graph-renderability`.

## Change

`Flow.framed` in `tools/Tools/View/Flow.lean` normalizes an empty body to `point (k ++ "/empty")`.
The ordinary region margins then allocate its room.
Nested and sequential folds retain that point.
No final coordinate is clamped.

`good_framed` in `tools/Tools/View/FlowLaws.lean` uses the normalized body's existing `Good` invariant.
`lay_realizes` in `tools/Tools/View/FlowOrder.lean` handles the new empty case through `realizes_none`.
The nonempty case retains its original translation observation.

Changed source files:

- `tools/Tools/View/Flow.lean`
- `tools/Tools/View/FlowLaws.lean`
- `tools/Tools/View/FlowOrder.lean`

The repair also retains its plan and probes under `docs/research/2026-10-13-empty-region-evidence/`.
The GraphCheck control retains the former malformed region as data after its producer is repaired.
Its current source probe reports `PASS empty scoped generator`.

## Proof placement

Placement precedes repair in `docs/research/2026-10-13-empty-region-plan.md`.
Concept: `initial-algebras-folds`, concept 7.
Role: preservation of existing tool observations, serving R14.
Existing consumers are `lay_good`, `place_descends`, `place_apart`, and `place_keeps_order`.
The observations are `Good` and `Realizes`, under the existing nonnegative-width premise.
There is no new registry claim or planned goal.
The laws establish no schedule, program typing, ink bound, or general region-rectangle containment theorem.

## Commands and results

Run from `C:/Users/kokok/Dev/lean4-effect4-peg-geometry`:

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.FlowLaws Tools.View.FlowOrder Tools.View.FlowSpecimen Tools.View.GraphCheck Tools.View.Inc Tools.View.Build
lake env lean docs/research/2026-10-13-empty-region-evidence/Audit.lean
lake env lean docs/research/2026-10-13-empty-region-evidence/Controls.lean
lake env lean docs/research/2026-10-13-graph-check-evidence/Controls.lean
lake env lean docs/research/2026-10-13-empty-region-evidence/RenderingBoundary.lean
git diff --cached --check
```

The narrow build and its direct consumers pass with 413 jobs.
Both control probes and the strict law-module audit exit with code 0.
The staged diff check passes.
Lake reports the existing manifest-input revision mismatch for the coordinator's kit pin.
This slice changes no dependency configuration.

Measured strict audit:

```text
Tools.View.Flow.good_framed: proved; nearest []; 0 lemmas, 0 definitions
Tools.View.Flow.lay_realizes: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
#axiom_audit: 448 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The strict audit covers FlowLaws and FlowOrder, including the changed framing definition through their dependencies.
The separate whole-Flow diagnostic exits with code 1.
It reports eight rendering declarations reaching `Classical.choice` through two unchanged text paths.
Those roots are `nodeWidth` through `Graph.boxWidth` and `flowLayerWith` through `Program.ownText`.
`RenderingBoundary.txt` retains every declaration and dependency path.
This receipt does not claim that the whole Flow module passes the strict ceiling.

## Bounded behaviour evidence

The four source controls cover an empty scope, nested empty scopes, and an empty scope before or after a value.
Their allocations are `32 × 40`, `48 × 80`, and `136 × 112` for each sequential order.
Their routes resolve and their allocated rectangles pass GraphCheck.
All ten Flow specimens at the original base still pass.
The coordinator's newly added specimens await integration checks.
The original negative allocation remains a refused finite control.

No Effect runtime behaviour gate changes.
Driver enforcement and SVG content/XML validation remain the coordinator's integration work.
