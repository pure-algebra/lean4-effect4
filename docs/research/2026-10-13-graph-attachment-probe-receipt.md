# Graph attachment probe receipt

The coordinator can cherry-pick the probe commit after the two metadata seeds.
The probe uses no checker extension.
The current Flow producers pass all contact controls.

## Commits and files

Worktree: `C:/Users/kokok/Dev/lean4-effect4-graph-separation`.
Branch: `codex/graph-separation`.
Previous head: `22c412cda66a696322ead47f0b0e8812b12ff35e`.
The seed `ad8b0075d` becomes `51481d2fd` in this worktree.
The seed `ed1783560` becomes `65c40f0f6` in this worktree.
Probe base: `65c40f0f6`.
Probe head: `6aa28760f04dcee53d7619e5f644a27eb0b3bd75`.

The probe commit changes only `tools/view/GraphAttachmentProbe.lean`.
This receipt adds only `docs/research/2026-10-13-graph-attachment-probe-receipt.md`.
The coordinator already owns both seed commits.
Do not cherry-pick their worktree copies again.

## Placement and scope

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Requirement: R14's contact inspection.
Question: the proposed `view-graph-renderability-check` in `docs/research/2026-10-13-graph-defects-plan.md`.
Role: readers of existing lookup helpers and finite producer controls.
Consumer: explicit point-to-mark lookup for checked layout, motion, and contact inspection.
Reach: the supplied duplicate metadata and every current `FlowSpecimen.frames` member.
Limits: no arbitrary-layout admission, continuous motion clearance, program meaning, or rendering-contact theorem follows.
The probe states no new universal theorem.

The readers apply `GraphAttachment.Index.findMark_of` and `GraphAttachment.Index.findAttachment_of` in `tools/Tools/View/GraphAttachment.lean`.
They use conflicting duplicate metadata as their real carrier.
The controls observe `GraphAttachment.markContains` at bar lips, singleton bars, reversed bars, diamond centers, and node boxes.
The lookup controls use keys containing both `→` and `->`.
They establish exact key lookup for these fixtures without a key parser.

`GraphAttachmentProbe.contactsAtRest` checks every explicit binding in the supplied layout.
It requires a resolved point, a resolved first-occurrence mark, and successful logical-coordinate contact.
`GraphAttachmentProbe.producerMetadata` also checks unique mark keys and unique attached-port keys.
It requires a binding for each mark and rest values for every placed item and route.
Generated source text stays inside guards rather than strict battery declarations.

## Commands and observations

Run the commands from the worktree above.

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.GraphAttachment Tools.View.FlowSpecimen ProofGraph.AxiomAudit
lake env lean -DwarningAsError=true --run tools/view/GraphAttachmentProbe.lean
git diff --check
```

The narrow build succeeds with 196 jobs.
The probe succeeds with exit code zero.
Its measured output records every current fixture:

```text
fork and join: 6 attachments, 2 marks
a wait inside a region: 3 attachments, 1 marks
a fiber awaits a fiber: 9 attachments, 3 marks
await all: 12 attachments, 4 marks
an item of a tuple: 6 attachments, 2 marks
a release at its scope's close: 0 attachments, 0 marks
an empty race: 1 attachments, 1 marks
a race: 8 attachments, 2 marks
a handler around a scope: 2 attachments, 2 marks
a loop: 0 attachments, 0 marks
nested forks: 12 attachments, 4 marks
a race inside a loop: 6 attachments, 2 marks
nested scopes and releases: 0 attachments, 0 marks
an unresolved wait: 0 attachments, 0 marks
a wide race with nested branches: 16 attachments, 4 marks
empty nested scopes: 0 attachments, 0 marks
graph-attachment: 16 frames, 81 attachments, 27 marks pass
graph-attachment: first lookup, contact boundaries, nodes, arbitrary keys controls pass
```

The probe runs `#axiom_audit checked Tools.View.GraphAttachment`.
Its output is:

```text
#axiom_audit: 26 declarations within [propext, Quot.sound],
0 of them modulo planned goals; 0 planned goals;
checked: the walk's answers at 1728 constants agree with their captured graph,
over the labels [propext, Quot.sound]
```

The audit covers the strict attachment module, including its imported dependency graph.
It does not audit generated page text or the probe's reporting function.
The build reports the existing manifest revision mismatch and modified dependency checkout.
This slice changes neither dependency pin nor package content.

## Findings and open parts

No producer metadata defect appears in the current fixture observation.
The empty race supplies a singleton bar contact.
The bar predicate accepts both endpoint contacts, including a zero-span bar's single coordinate.
Its reversed interval rejects contact.

`FlowMark` in `tools/Tools/View/Graph.lean` describes bar spans as `[x0, x1)`.
`GraphAttachment.markContains` uses the closed contact condition `x0 ≤ middle ≤ x1`.
The coordinator should distinguish painted extent from endpoint contact when it revises that description.

Unchecked duplicate mark identities and port bindings use first-occurrence lookup.
The contact predicate alone does not establish uniqueness or resolve missing references.
The checker remains the owner of those refusals.
The probe intentionally avoids the coordinator's uncommitted checker extension.

Moving contacts, painted connector contact, and unsupplied metadata remain outside this observation.
The slice reaches no outside Effect runtime gate.
It leaves production source, library roots, batteries, and register files unchanged.

The receipt language check reports no finding.
The whitespace check reports no finding.
