# Graph region view adapter receipt

The coordinator can cherry-pick the adapter after the GraphRegions seed.
The adapter retains source graph data and every original edge occurrence.
The visible graph keeps uncollapsed self-loops and separate parallel edges.

## Commits and files

Original base: `5cd537aef9838da43d4f9377d033028bddf7403a`.
GraphRegions seed: `b1247fdae264c9ce8d502ecfb8ed86d41f238cd6`.
Its worktree copy is `72cea6fcbabbd98d8d51a8b6495389505f125662`.
Adapter head: `1baba37c878c286a4c24720bcd91d6642f1af7ff`.
Branch: `codex/graph-regions-view`.
Worktree: `C:/Users/kokok/Dev/lean4-effect4-graph-separation`.
The coordinator already owns the GraphRegions seed.
Do not cherry-pick its worktree copy again.

The adapter commit changes these explicit paths:

- `tools/Tools/View/GraphRegionsView.lean`
- `tools/view/GraphRegionsViewProbe.lean`
- `docs/research/2026-10-13-graph-regions-view-plan.md`

This receipt adds only `docs/research/2026-10-13-graph-regions-view-receipt.md`.

## API and placement

`GraphRegionsView.prepare` receives a Graph, membership, region selections, and optional ordinal labels.
It checks source input, owner count, and region projection in that order.
Its `Prepared` result exposes `source`, `prepared`, `edges`, and `graph`.
It stores no callback and imports no new program syntax.
The compound-graph gallery consumes this production adapter.

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Requirement: R14's compound graph navigation and selection.
Question: the finite collapse-provenance observation proposed in the graph-hierarchy research note.
Role: `ownerCount_iff` is a checker helper consumed by preparation.
Reach: exact equality between the owner array size and original node array size.
Limits: the helper establishes no forest validity, quotient-path lifting, program meaning, or layout performance bound.
The placement precedes the theorem in the adapter plan above.

`GraphRegions.project_provenance` in `tools/Tools/View/GraphRegions.lean` owns ordered original-occurrence retention.
The adapter retains those records unchanged, including hidden internal edges.
Visible edges copy their original payload and replace only source and target positions.
Visible node and region keys use disjoint `node:` and `region:` prefixes.
Region labels default to the declared region key when the caller omits an ordinal label.

The result contains retained view data, not a rendered-geometry certificate.
Raw public `Prepared` records establish no guarantee outside their preparation functions.
The existing source input checker scans prior key prefixes and claims no large-input time bound.
This slice claims no generic semantic edge-class interpretation for `GEdge`.

## Commands and results

Run these commands from the worktree above.

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.GraphRegionsView ProofGraph.AxiomAudit
lake env lean -DwarningAsError=true --run tools/view/GraphRegionsViewProbe.lean
python scripts/check-language.py --show docs/research/2026-10-13-graph-regions-view-plan.md
python scripts/check-language.py --show docs/research/2026-10-13-graph-regions-view-receipt.md
git diff --check
```

The narrow build succeeds with 36 jobs.
The probe succeeds with exit code zero.
It records these finite observations:

```text
graph-regions-view: labels, namespaces, loops, parallel and hidden records pass
graph-regions-view: owner count, source precedence and region refusal controls pass
```

The probe runs the checked strict audit over GraphRegionsView and GraphRegions.
Its measured output is:

```text
#axiom_audit: 377 declarations within [propext, Quot.sound],
0 of them modulo planned goals; 0 planned goals;
checked: the walk's answers at 2407 constants agree with their captured graph,
over the labels [propext, Quot.sound]
```

The controls use identical original-node and region key strings.
They also use original keys containing both reserved prefixes and an arrow.
The collapsed and expanded visible graphs pass the existing input check.
A source-copy control retains original target ordinal two when the visible parallel edge targets ordinal one.
Other controls check empty collapsed regions, nested selection, labels, hidden loops, and refusal precedence.

The language checks report no finding.
The whitespace check reports no finding.
Lake reports the existing dependency revision mismatch and modified dependency checkout.
The slice changes no dependency file or package content.

## Open parts

The controls concern the supplied finite graph and membership data.
The adapter supplies no original-reachability claim for arbitrary region collapse.
Compound boundary routing and painted expanded-region enclosures remain future consumers.
The slice establishes no rendering clearance or full-layout scale result.
It reaches no outside Effect runtime gate.
It changes no program core, library root, battery root, or decision register.
