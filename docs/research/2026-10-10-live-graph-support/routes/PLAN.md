# Downward route validation

Status: research note, not authority.
Base: `9389e543ad1325a603732b7802344d79b3b98c61`.

## Question and placement

- Concept: `initial-algebras-folds`; property: finite graph navigation for R14.
- Question: named tool law `Laid.downRouteDescends_iff`; role: decidability; consumer: `Laid.edgesDescend` in `tools/Tools/View/Graph.lean`.
- Reach: finite route geometry on one `Laid` value; each adjacent downward pair resolves through `Laid.find` and satisfies the existing vertical inequality.
- Does not establish: scheduler progress, runtime deadlock, route bounds, collision freedom, drawing correctness, or host behavior.
- Unlocks: R14 view checks through the existing `graph-edges-descend` result in `tools/Drivers/View.lean`.

Decisions rows 334(3) and 336(8) place this named tool law outside registry claims.
The graph representation stays `Graph` in `tools/Tools/View/Graph.lean`.

## Existing contract and proposed repair

`Laid.edgesDescend` checks a downward route with two keys.
Other route lengths answer `true` without checking their pairs.
`Graph.chain` inserts intermediate keys for long forward edges.

Check every adjacent pair with the existing rule.
A source box contributes `ROWH * BOXROWS` to its bottom.
A source point contributes no height.
The target top must stand at or below that bottom.
A missing endpoint makes the pair fail.

Empty and singleton routes retain `true`.
These routes contain no segment to check.
A missing singleton key also retains `true`.
This check states no route-shape or dimension judgment.

Duplicate keys retain `Laid.find`'s first-match behavior.
Back and loop routes retain `true` under this downward-only check.

## Finishing criteria

1. Retain a finite reproduction of the old long-route false positives.
2. Accept a valid long chain and equality at a segment boundary.
3. Reject an inverted intermediate point and a missing intermediate point.
4. Retain empty, singleton, back, loop, and first-match behavior.
5. Prove the all-adjacent characterization used by `Laid.edgesDescend`.
6. Build the changed module and its direct view consumers.
7. Audit `Tools.View.Graph` with `#axiom_audit`.
8. Record existing rendering exemptions separately from the changed declarations.
9. Commit explicit assigned paths with logs and a receipt.

No behavior gate compares this finite geometry check with an outside implementation.
No whole-tree sweep or runtime gate applies to this slice.
