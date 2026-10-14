# Graph ordering: one barycentre per item

The change computes each barycentre before the stable sort.
`Graph.orders` in `tools/Tools/View/Graph.lean` consumes the order.
`Run.page` in `tools/Tools/View/Run.lean` consumes the resulting graph layout.
`Graph.reorder_eq` in `tools/Tools/View/GraphOrdering.lean` states the exact order observation.

## Placement before proof work

| Field | Placement |
| --- | --- |
| Concept | `initial-algebras-folds`, concept 7 in `docs/core/semantics.md` |
| Required property | Fold congruence over agreeing implementations, applied to the graph ordering tool |
| Question and role | `Graph.reorder_eq`: tool law under decisions row 334 (3), consumed by `Graph.orders` |
| Registry boundary | The theorem states no registry claim and adds no Effect judgment |
| Observation | The exact list of keys returned by the current key comparator's stable `List.mergeSort` |
| Fragment and hypotheses | Every order, beside order and neighbour function, including duplicate keys and absent neighbours |
| Scope limit | No claim about minimal crossings, ranking, separation, rendering, scheduling or the host boundary |
| Requirement | R14's live authoring tool, through `Run.page` |

The comparator retains the first position of a repeated key.
It filters neighbours through the beside order before computing their positions.
An item without neighbours in the beside order retains its current position as its score.
The cross product comparison retains ties under the same stable sort.

## Validation

Run the narrow builds for `Tools.View.Graph` and its direct consumers.
Audit `Tools.View.GraphOrdering` with `#axiom_audit`.
Run `tools/view/GraphOrderingProbe.lean` to compare exact orders and measure both implementations.
Report finite measurements for ordering and for synthetic layered graph layouts.
The benchmark consumes the results through checksums.
It records its input size, repetitions and measured duration.
