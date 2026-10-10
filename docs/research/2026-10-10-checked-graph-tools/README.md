# Checked graph paths and prepared placement

Keep the exact edge list when retaining an explanation.
A path stores edge occurrences, not a separately serialized graph or its digest.
A successful query proves a path through those edges.
An unsuccessful bounded query leaves other reachability questions open.

## Goal and state

The owner requests reusable graph operations with evidence carried by their interfaces.
This slice builds one shared path fold and uses it in Flow explanations.
It also removes repeated wait analysis from existing layout preparation.

Base: `969ed613b582bbdd4013ac21d949eb6f159369d8`.
Production commit: `30af611a6484edee548678f7b0a33a9697599477`.
Branch: `codex/host-followup-review`.
Worktree: `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.
The primary checkout remains unchanged by this slice.
Claude owns its ongoing program-parameter and printing work.

All narrow checks pass in `verification.json`.
The slice remains on the isolated review branch until the coordinator integrates it.

## What changes

`Tools.Graph.Walk`, in `tools/Tools/Graph/Path.lean`, fixes both endpoints in its type.
Its constructors retain the supplied edge identities.
Its `fold` interprets those constructors once for each consumer.
Edge extraction, composition, and the Flow reachability proof use that fold.

`Walk.read?` admits a supplied edge sequence.
A successful result contains the path, with the same occurrences in the same order.
`Walk.append` joins paths whose middle endpoint matches.
The consumer supplies the edge alphabet and its endpoint interpretation.
There is no new stored graph or program representation.

`explainReaches`, in `tools/Tools/View/FlowPath.lean`, reconstructs the existing bounded query.
`explainWait` fixes the direction for one candidate wait.
The returned path uses positions in the supplied edge list.
Parallel edges retain distinct positions.

The Boolean query and explanation share `searchNext` in `tools/Tools/View/Flow.lean`.
The explanation runs only when a caller requests it.
The ordinary layout adds no second path search or dense table.

`preparePlacement` analyzes waits once and materializes the height assignments.
Its result supplies both `PreparedPlacement.height` and the lane list.
The previous `assign` and `heightsOf` remain the independent recurrence that the laws describe.
`placeWith` uses the retained data.
The existing layout theorem statements retain their observations and hypotheses.

## Small interfaces

```lean
let prepared := Tools.View.Flow.preparePlacement box
let y := prepared.height position
let lanes := prepared.lanes

-- The list is the current constraint list at this candidate.
let reason := Tools.View.Flow.explainWait itemCount edges (exitPosition, awaitPosition)
-- A successful reason carries the path from the await to the exit.
```

A caller interpreting a path supplies the meaning of an empty path and one edge followed by a path.
`Walk.fold` then interprets the entire path.
The Flow instance produces the existing `Flow.Reach` judgment.
A different edge alphabet can explicitly reverse edges for weak connectedness.
Such a path does not establish directed reachability in the original graph.

## Proof placement

`PLAN.md` records each obligation before implementation.
Concept: `initial-algebras-folds`.
Placement: named tool laws under decisions row 336, point 8.
Consumer: Flow placement, bounded cycle explanations, and later proof dependency explanations.
Requirement connection: R14 navigation.
No new registry claim or machine progress claim is asserted.

| Law | Observation | Scope |
| --- | --- | --- |
| `Walk.read?_edges` | A path reads from its own occurrences | Every edge alphabet and decidable vertex equality |
| `Walk.edges_of_read?` | Admission retains the supplied occurrences | Every successful supplied-path read |
| `Walk.edges_append` | Composition concatenates occurrences | Paths with one shared endpoint |
| `assignHeights_agrees` | Materialized heights equal the old recurrence | Every order, initial table, and natural position |
| `preparePlacement_height` | Preparation equals `heightsOf` | Every raw box and natural position |
| `preparePlacement_lanes` | Preparation retains lane order | Every raw box |
| `explainReaches_isSome` | Explanation agrees with the existing bounded query | Every edge list, fuel, source, and target |
| `occurrenceWalk_reach` | A checked occurrence path implies `Flow.Reach` | The supplied edge interpretation |
| `reaches_reach` | Existing Boolean success implies `Flow.Reach` | The same fuel and singleton source |
| `explainWait_isSome` | Explanation selects the existing cycle branch | The exact accumulated constraints |

The generic laws live in `tools/Tools/Graph/Path.lean`.
Prepared placement laws live in `tools/Tools/View/FlowLaws.lean`.
The Flow query laws live in `tools/Tools/View/FlowPath.lean`.
The code of each tool names its laws.

## Controls and implementation findings

A raw box may reference positions outside its item list.
A fixed-size height array would lose those assignments and change the old total function.
The retained sparse table keeps every selected-order position, including repeated assignments.

The exact dependency check found classical choice behind a standard-library finite-index search theorem.
The search implementation stays unchanged; the proof connection is repaired constructively.
The final check enforces the existing `[propext, Quot.sound]` ceiling.

The controls cover repeated and parallel occurrences, wrong endpoints, changed edges, cycles, and bounded exhaustion.
The connectedness control uses `0 → 2 ← 1`.
A path exists after explicitly reversing the second edge; the original directed query fails.

`ProofPathControls.lean` reads actual declaration dependencies and admits a theorem-to-observation path.
That check is finite reflection evidence.
It establishes no theorem about environment extraction or source admission.

## Limits and next consumers

A view cycle proves no runtime deadlock, fairness, or schedule property.
Loop returns, structural order, accepted waits, proof dependencies, and runtime transitions retain separate meanings.
A typed path retains the endpoint interpretation, not a transport format or persistent graph identity.
Stored explanations need a snapshot identity and a reader that checks the path against that snapshot.

The sparse table removes repeated preparation; it does not provide constant-time lookup.
Compiler inspection checks retained call structure.
It establishes no timing speedup or asymptotic complexity theorem.

The next proof report can display a checked dependency path for an existing refusal.
Keep its current collector, environment, stopping policy, and verdict.
The next connectedness tool can use an explicitly symmetrized edge alphabet.
A shortest-path claim requires another placed obligation.
A claim that no path exists requires another placed obligation.

## Verification receipt

`verify.py` records exact commands, source hashes, log hashes, results, and timestamps in `verification.json`.
It runs one Lake process at a time with three threads.
It builds the changed modules and direct dependents.
It checks the independent old placement and query bodies in `Baseline.lean`.
No full sweep, merge, push, or Claude session message is part of this slice.

The final run passes 7 checks: the narrow build, baseline, path controls, placement controls, Flow controls, declaration controls, and compiler inspection.
The path audit covers every declaration in the new path module.
The Flow audit covers every declaration in the new explanation module.
The placement audit covers the new operations, connectors, and existing top layout laws.
`first-audit-refusal.log` retains the earlier rejected dependency and fixture errors.
The final logs supersede that failed attempt.

## Integration check

The production patch applies to the primary working files without editing them.
`integration.json` records the command, commit, file hashes, and result.
This establishes patch applicability only.
UNVERIFIED: compilation against the changing program-parameter work; checked: the isolated narrow build and read-only patch applicability.

`landing-audit.json` confirms that retained evidence matches the committed production sources.
It also compares the existing layout theorem statements with the pre-change base.
Their hypotheses and observations remain unchanged.

Integrate the production commit after reviewing the current owner work.
Run the narrow dependent build before treating the combined tree as checked.
Keep the baseline and controls as independent evidence when adapting the slice.
