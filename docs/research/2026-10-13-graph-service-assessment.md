# Graph service assessment after the preparation slices

Keep the production connector construction fixed while the graph contracts deepen.
The next boundary is identity and incidence shared by queries, layout, motion, and selection.
Incidence records which named ports an operation connects.
An occurrence records one supplied edge, including an edge parallel to another.

## Landed seams

| Seam | Consumer | Evidence |
| --- | --- | --- |
| `GraphCheck.Checked` in `tools/Tools/View/GraphCheck.lean` | `GraphLayout.checked` in `tools/Tools/View/GraphLayout.lean` | Input and allocation evidence returned together |
| `Graph.reorder` in `tools/Tools/View/GraphOrdering.lean` | `Graph.orders` in `tools/Tools/View/Graph.lean` | `Graph.reorder_eq` observes the exact previous key order |
| `GraphMotion.prepare` in `tools/Tools/View/GraphMotion.lean` | Page and advanced-motion exporters | `prepare_sample_eq_reference` observes the exact previous sampled layout |
| `Specimen.checkedFrames` in `tools/Tools/View/Specimen.lean` | Both specimen consumers in `tools/Drivers/View.lean` | Positive and negative finite admission controls |

The sorting and sampling laws include duplicate keys and retain occurrence order in their exact output observations.
The input checker now refuses repeated edge identities.
These scopes differ: compatibility covers old inputs, while the input checker defines the supported graph input.

The preparation data retain expensive analysis across samples.
The proof concerns returned data, not speed.
The timing reports remain host measurements under `lake env lean --run`.

## Mathematical boundaries

`Flow.ofProgram` in `tools/Tools/View/Flow.lean` projects the existing program through its fold.
It does not introduce a second program syntax.
The flow records structural constraints rather than scheduler events.
The revised module prose no longer identifies a static constraint cycle with runtime deadlock.

`AGraph.denote` in `tools/Tools/View/AlgGraph.lean` observes vertices and edges as predicates.
That observation forgets parallel multiplicity.
`Flow.order` in `tools/Tools/View/FlowOrder.lean` also forgets branching kind and loop structure.
Keep those observations for precedence laws.
Do not use them as the identity model for graph editing or machine execution.

`FlowPath.EdgeOccurrence` in `tools/Tools/View/FlowPath.lean` already distinguishes parallel occurrences.
`Flow.ReachTable` in `tools/Tools/View/FlowReach.lean` already answers checked finite reachability.
Reuse those declarations when adding queries.
Name the supplied relation: structural constraints, visible routes, loop returns, or recorded run dependencies.
A path in one relation establishes no path in another without an extraction law.

## Next functional slices

| Priority | Concrete gap | Module boundary and consumer |
| --- | --- | --- |
| 1 | Generated point names can collide; Flow route names can collapse parallel occurrences | Carry typed occurrence and port identities into layout, motion, and selection |
| 2 | Moving bars jump to target coordinates while their kept ports interpolate | Retain mark-to-port membership from `Flow.Box` and sample each connected group together |
| 3 | Allocated rectangles omit route ink; direct box interpolation can collide | Add separate painted-bound and intermediate-clearance observations for export and viewport fitting |
| 4 | Queries can silently mix constraint edges, visible edges, returns, and waits | Prepare a checked snapshot for each named relation over existing occurrence and reachability machinery |
| 5 | Inspection infers contact roles from route text and SVG contours | Export contact metadata from layout for selection, hit testing, and close-up navigation |
| 6 | Retained caches have correctness laws but no lifecycle policy | Give each retained scene an explicit cache lifetime, then measure memory across interrupted transitions |

The moving-bar fix needs explicit membership when branches enter or leave.
Interpolating only the bar handles stable membership, but new ports already occupy target coordinates.
That narrower patch would leave another docking gap.

The loop fix needs bounds shared by generic and program layout producers.
A conservative cubic control-hull bound can cover the centreline.
Stroke width and expansion overshoot need their own painted-bound contribution.

## Consolidation

The kit owns keyed joins, ribbon geometry, and the generic scene-order algebra.
Effect4 owns source projection, recorded-run observations, and source addresses.
The local `AGraph` declarations in `tools/Tools/View/AlgGraph.lean` overlap the kit's `Whatwg/Svg/Scene/Order.lean`.
Move their consumers through an agreement law before removing the local declarations.
Do not merge a precedence observation with an occurrence graph merely because both use edges.

The arithmetic preparation modules now hide repeated work behind narrow calls.
Further extraction should serve a concrete consumer, not create forwarding wrappers.
Keep the frozen motion reference as a compatibility witness while the new preparation seam settles.

## Executed visual controls

`tools/view/GraphContractProbe.lean` emits the production SVGs used by `tools/view/graph_contracts.py`.
The page presents synchronized sampled moments and close-ups.

The controls reproduce these gaps:

- Kept fork ports and their bar disagree at intermediate heights.
- Separated endpoint boxes overlap while their positions swap.
- A self-loop passes `GraphCheck.laid` and extends beyond its allocated canvas.

These are bounded controls, not general geometry theorems.
The accepted production connector remains unchanged.

## Aesthetic inventory after the contracts

Probe port collars, fork and join widths, choice diamonds, return arrows, loop lanes, labels, region corners, and clipping margins.
Inspect selected and hovered nodes, edges, and ports at the intended zoom levels.
Inspect parallel-edge separation and dense fan-out without changing occurrence identity.
Then choose the aesthetic changes from those views.

## Evidence and placement

The input-check, ordering, and motion receipts give their commands, axiom output, and proof placement.
They are `docs/research/2026-10-13-graph-library-receipt.md`, `2026-10-13-graph-ordering-receipt.md`, and `2026-10-13-graph-motion-receipt.md`.
The kit assessment is commit `a966858cb55f01e106c6fb76511feaf10843bf25` in `lean4-whatwg-svg`.
Its note is `docs/research/2026-10-13-service-graph-contract-assessment.md` in that repository.

Future proofs require placement under concept 7 and R14 before implementation.
A runtime equal-observation theorem additionally requires its explicit fragment, observation, and recorded-decision boundary.
No statement here changes a semantics registry status or closes a machine-semantic obligation.
