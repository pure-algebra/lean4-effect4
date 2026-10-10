# Downward route check receipt

**The one thing to know before merging:** The route check now rejects inverted and missing intermediate points.
The full module audit retains the same existing rendering dependencies.

## Base and head

Base: `9389e543ad1325a603732b7802344d79b3b98c61`.
Worktree: `/Users/pooks/.codex/worktrees/live-graph-routes/lean4-effect4`.
The local commit containing this receipt is the head.
`git rev-parse HEAD` gives its exact identity after the commit.

## Changed files

- `tools/Tools/View/Graph.lean`: check every adjacent downward pair and expose the named tool laws.
- `docs/research/2026-10-10-live-graph-support/routes/`: retain the plan, finite controls, baseline probe, audit probes, and logs.

## Commands and results

Run these commands from the worktree.
The retained logs give the measured results.

```sh
LEAN_NUM_THREADS=3 lake build Tools.View.Graph ProofGraph.AxiomAudit
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/routes/Baseline.lean
LEAN_NUM_THREADS=3 lake build Tools.View.Graph
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/routes/Controls.lean
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/routes/Audit.lean
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/routes/ChangedAudit.lean
LEAN_NUM_THREADS=3 lake build Tools.View.Page Tools.View.Run Tools.View.Flow Tools.View.Build Tools.View.Motion Tools.View.FlowLaws Tools.View.FlowOrder
LEAN_NUM_THREADS=3 lake build Tools.View.Specimen Tools.View.FlowSpecimen
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/routes/Specimens.lean
python3 scripts/check-language.py --strict docs/research/2026-10-10-live-graph-support/routes/PLAN.md docs/research/2026-10-10-live-graph-support/routes/RECEIPT.md
git diff --check
```

The baseline command runs before the repair.
`baseline-probe.lean.txt` retains its exact source.
The fixed source makes that old false-positive probe fail.
`baseline.log` retains the old result.
The baseline and repaired full module audits both fail on the same rendering declarations.
`verification.json` compares their exact names.
The focused builds, route controls, specimen controls, and changed-declaration audit pass.

## Axiom output

`Audit.lean` runs `#axiom_audit Tools.View.Graph`.
`baseline-audit.log` and `audit.log` retain the full output.
The existing rendering declarations reach `Classical.choice` through string operations.
This slice adds no exemption and changes no trust allowance.

`ChangedAudit.lean` uses the same cycle-aware walk for every changed declaration.
`changed-audit.log` records their dependencies within `[propext, Quot.sound]`.
The helper definitions and check reach `[propext]`.
The named tool laws reach `[propext, Quot.sound]`.

## Evidence

Tested: the baseline accepts an inverted chain and a chain with a missing intermediate key.
Tested: the repaired check rejects both chains.
Tested: valid chains and exact segment boundaries pass.
Tested: missing endpoints fail when an adjacent segment uses them.
Tested: duplicate keys retain the drawing lookup's first match.
Tested: empty and singleton routes retain their vacuous result.
Tested: back and loop routes remain outside the downward check.
Tested: negative coordinates can pass this check while the dimension check fails.
Tested: the existing graph and program-flow specimens pass.
These finite controls establish no outside-runtime agreement.

## Landed theorems and their placement

The placement in `PLAN.md` applies to both named tool laws.

| Name in `tools/Tools/View/Graph.lean` | Role | Consumer | Exact reach |
| --- | --- | --- | --- |
| `Laid.downRouteDescends_iff` | decidability | `Laid.edgesDescend_down_pairs` | The check answers `true` exactly when every adjacent pair answers `true` |
| `Laid.edgesDescend_down_pairs` | extraction | The view driver's result and the reader in `Controls.lean` | A passing layout check checks every adjacent pair of each listed downward route |

Concept: `initial-algebras-folds`; requirement: R14 finite view navigation.
Decisions rows 334(3) and 336(8) place these tool laws outside registry claims.
The fragment is one finite `Laid` value with the existing first-match lookup.
The laws establish no scheduler progress, runtime deadlock, route bounds, collision freedom, drawing correctness, or host behavior.

## Open obligations

The existing rendering dependencies remain in the full module audit.
This check counts no runtime cost and proves no drawing-algorithm complexity bound.
