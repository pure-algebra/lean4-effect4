# Proof scouting follow-up, 2026-10-05

Status: advisory review at main `11e655c1`.
Proof role: tooling acceptance support.
Evidence status: source review and finite JavaScript controls.
Scope: proof-report validation and model construction. No Lean execution or kernel claim.

## Resolved findings

Commit `0373bcf6` requires the missing fields from the previous review.
The existing checker passes with four malformed-report controls and thirteen absent-field controls.
Each absent-field control has a present-empty control.
Our original statement, axiom, nearest-node and open-parts omissions now receive named refusals.

The same commit replaces the bounded traversal with `reachThrough` in `tools/Tools/Semantics.lean`.
It queues each name once and returns pending names when its bound ends.
The caller includes pending names explicitly in its Markdown output.
Its retained commands report four traversal controls and unchanged generated Markdown.
This review does not rerun Lean or regenerate that Markdown.

Commit `11e655c1` records the fold proof route and the mask registry reconciliation prerequisite.
It adds observation-separated migration acceptance, versioned witness joins and the proposed impact query.
Those are adopted plans, not completed proofs.

## New bounded finding: reference shape

`validatePlan` in `tools/Tools/ProofGraphView.js` accepts either a string or an object for every reference.
The same file's model construction requires different shapes at different fields.
Requirement `top` and `placed` entries must carry a `name` field.
Node `broughtIn.nearest` entries must be strings.

`reference-shapes.mjs` extracts the actual validator and pure model construction from that source.
It changes one reference in a copy of the retained report.
It does not execute the DOM drawing code.

| Control | Validation | Model construction |
| --- | --- | --- |
| Untouched report | Accepted | Succeeds |
| Empty nearest-edge list | Accepted | Succeeds |
| Unknown nearest string | Refused with its name | Not run |
| Known requirement top as a string | Accepted | Throws at parent-edge insertion |
| Known nearest edge as an object | Accepted | Throws at parent-edge insertion |

Both accepted malformed cases throw `TypeError: Cannot read properties of undefined (reading 'push')`.
Thus malformed input passes the named refusal boundary and fails during model construction.
The current retained report is valid and renders its model successfully in this probe.

Smallest correction: check reference element shapes per field before checking names.
Alternatively, normalize accepted shapes once and use that normalized representation throughout the model.
Extend `scripts/check-proofgraph-input.mjs` with these two mutants and their valid controls.
This needs no new gate and no owner ruling.

## Evidence

The runtime is Node `v22.23.2`.
`reference-shapes.json` retains hashes, exact outcomes and scope.
`recheck-missing-fields.json` retains the original omissions against the repaired validator.
No build, generator, installation or active-repository edit runs in this review.
