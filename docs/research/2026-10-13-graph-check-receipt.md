# Graph rendering check receipt

The coordinator must call both checks and fail the driver on a refusal.
The empty-region probe locates a separate Flow allocation defect at `region[0].y = -32`.

Base: `e9cf615b5047ac3a4d1be053291434fd757b9b7d`.
Code head: `2f47ce67b20d8246c91311ced612f1b552b11a36`.
Branch: `codex/graph-renderability`.

## Interface and files

`GraphCheck.input` checks node keys and input edge ranges.
`GraphCheck.laid` checks placed keys, allocated rectangles, and every route kind's endpoint lookup.
Both declarations live in `tools/Tools/View/GraphCheck.lean`.
Both return `Except Refusal Unit`.
The refusal holds its site, index, field, and reason as first-order data.
The driver owns text formatting.

Changed files:

- `tools/Tools/View/GraphCheck.lean`
- `docs/research/2026-10-13-graph-check-plan.md`
- `docs/research/2026-10-13-graph-check-evidence/Audit.lean`
- `docs/research/2026-10-13-graph-check-evidence/Audit.txt`
- `docs/research/2026-10-13-graph-check-evidence/Controls.lean`
- `docs/research/2026-10-13-graph-check-evidence/Controls.txt`

## Placement and limits

Placement precedes the proof in `docs/research/2026-10-13-graph-check-plan.md`.
Concept: `initial-algebras-folds`, concept 7.
Proposed tool question: `view-graph-renderability-check`, under decisions row 334 (3).
Role: decidability of the stated finite rendering observation.
Requirement served: R14, through the graph driver.

`checks_iff` states acceptance exactly when every supplied Boolean test holds.
It serves `input_iff` and `laid_iff`, the two admission observations.
`InputOK` and `LaidOK` name those finite observations.
The proof graph comes from these proof terms, through retained `#plan_status` commands.
The coordinator owns any registry addition.

Keys use Boolean String comparison, matching the renderer's lookup.
The statements introduce no proposition equating keys by a separate semantic identity.
Rectangles describe allocated nodes, points, and regions.
The checker bounds no curve, stroke, text, arrowhead, or mark ink.
It proves no program typing, scheduling, deadlock, or source-to-graph relation.

## Commands and measured results

Run from `C:/Users/kokok/Dev/lean4-effect4-peg-geometry`:

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.GraphCheck Tools.View.FlowSpecimen
lake build ProofGraph.Plan ProofGraph.AxiomAudit
lake env lean docs/research/2026-10-13-graph-check-evidence/Audit.lean
lake env lean docs/research/2026-10-13-graph-check-evidence/Controls.lean
git diff --cached --check
```

The narrow builds pass, with 175 jobs and 17 jobs respectively.
The retained audit and controls exit with code 0.
The staged diff check passes.
Lake reports the existing manifest-input revision mismatch for the coordinator's kit pin.
This slice changes no dependency configuration.

Measured audit output:

```text
Tools.View.GraphCheck.checks_iff: proved; nearest []; 0 lemmas, 0 definitions
Tools.View.GraphCheck.input_iff: proved; nearest [Tools.View.GraphCheck.checks_iff]; 0 lemmas, 0 definitions
Tools.View.GraphCheck.laid_iff: proved; nearest [Tools.View.GraphCheck.checks_iff]; 0 lemmas, 0 definitions
next goals: 0
#axiom_audit: 219 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

All ten Flow specimens at the base pass the new layout check.
The malformed back-edge control passes the former checks while the new checks refuse it.
The controls refuse dangling downward, back, and loop endpoints, duplicate keys, and invalid allocation data.
The extra empty-scope probe reports the negative region allocation.
Its expected refusal is evidence of detection, not an unsuccessful control run.

## Remaining work

Driver integration remains with the coordinator and driver seat.
The empty-region repair lands separately through the existing Flow layout laws.
No Effect runtime behaviour gate changes in this slice.
SVG content-model and XML checks remain the existing writer's boundary.
