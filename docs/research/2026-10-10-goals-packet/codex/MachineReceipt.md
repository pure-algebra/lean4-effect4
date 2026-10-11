# Machine structure receipt

The checked route needs assertions at every command boundary.
A resting host table fails the fuel-cut and forced-yield controls on `Workers.crew 1`.
No scenario goal is proved by this landing.

Base: `b74ebab6f`, branch `codex/machine-structure`.
The head is the commit containing this receipt.

## Files

- `src/Effect4/Laws/Machine/ControlSteps.lean`: arbitrary-evaluator iteration, loop and residual command rules.
- `src/Effect4/Laws/Program/ControlSteps.lean`: native store evaluation and commitment on an arbitrary fiber.
- `MachineDesign.md`: placement and the route comparison.
- `MachineRoutes.lean`: one symbolic command reader and six selected runs on the one-job crew.
- `MachineRoutes.out`: retained output.

## Commands

Every command runs in the isolated worktree with `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Test.Dogfood.Scenario.Workers Effect4.Laws.Machine.Lift Effect4.Laws.Program.Agreement.Machine` | exit 0, 1025 jobs |
| `lake build Effect4.Laws.Program.ControlSteps` | exit 0, 339 jobs |
| `lake build ProofGraph.AxiomAudit` | exit 0, 15 jobs |
| `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineRoutes.lean` | exit 0, six controls and the audit below |

```text
#axiom_audit: 6 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

## Placement and limits

The module docstrings and `MachineDesign.md` give each theorem's five-part placement.
The proposed question is `fiber-local-positions`, through `shop_stages` and `crew_invariant`.
The native store rules also serve `heap_sites_keep` and requirement R4.
The consumers are the command-boundary worker assertions on the R4, R10 and R11 paths.
The symbolic reader uses a representative write, without certifying its source point.
The runtime controls are finite Lean-machine evidence, not kernel proofs or host runs.

Open: program assertions, their command closure, control linearity, registration accounting, handle provenance and scenario assemblies.
Deferred: reached behavior gates after the major proof structure lands.
No core machine, existing goal statement, root import, decision register or lakefile changes.
No push.
