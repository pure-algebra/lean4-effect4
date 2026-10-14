# Graph defects and styling affordances

The production connector construction stays fixed.
Merge the view changes together: motion consumes explicit attachments, and output consumes prepared drawing dimensions.
Pure helper audits pass; rendering still reaches the existing String and host-data axiom dependencies.

## Base and head

Base: `26436e79195664380bf7861c307395e093e91e48`.
Code head: `cd623fb3ce2b83974cf1616825fa8e812b2c3fe2`.
Branch: `codex/pegs-port`.
The receipt commit follows the code head.
The work changes no dependency pin or program syntax.
The original development checkouts remain untouched.

`docs/research/2026-10-13-graph-defects-evidence/ChangedPaths.txt` records the changed paths through the code head.
The command is `git diff --name-only 26436e791 HEAD` at that head.

## Changes

- `PortAttachment` in `tools/Tools/View/Graph.lean` retains point-to-mark ownership from `Flow.layout` in `tools/Tools/View/Flow.lean`.
- `KeyMap.firstBy` in `tools/Tools/View/KeyMap.lean` shares first-occurrence indexing across placements, routes, marks, attachments, and regions.
- `GraphCheck.laid` in `tools/Tools/View/GraphCheck.lean` refuses malformed explicit bindings through located finite tests.
- `GraphAttachmentMotion.prepare` in `tools/Tools/View/GraphAttachmentMotion.lean` prepares mark, region, and attachment matches.
- `GraphMotion.Prepared.sample` in `tools/Tools/View/GraphMotion.lean` keeps attached points on moving marks and returns the exact target at the endpoint.
- `GraphMotion.choosePolicy` uses conservative node movement envelopes and explicit fallback reasons.
- Its fallback shrinks one endpoint family, hides relocation, and grows the other endpoint family.
- Kept detached points move freely; reused point-to-node identities select the endpoint-family fallback.
- `GraphBounds.viewport` in `tools/Tools/View/GraphBounds.lean` fits resolved geometry while retaining the routing span.
- `PageDrawing` in `tools/Tools/View/Page.lean` supplies calls, fitted dimensions, origins, cache, and unmeasured-text status.
- The batch driver and retained live groups consume that same prepared drawing.
- `GraphContact.collect` in `tools/Tools/View/GraphContact.lean` exposes logical contacts, surfaces, docking state, and directed-incidence roles.
- The inspector consumes validated contact records without decoding endpoint names.

## Commands and observations

Every Lean command runs with `LEAN_NUM_THREADS=3`.

```text
lake build Tools.View.GraphContact Tools.View.GraphCheck Tools.View.Motion Tools.View.FlowLaws Tools.View.FlowOrder Tools.View.Specimen Tools.View.FlowSpecimen Tools.View.Live Tools.View.LiveChecks Drivers.View
lake env lean tools/view/GraphContactProbe.lean
lake env lean --run tools/view/GraphAttachmentProbe.lean
lake env lean --run tools/view/GraphTransitionProbe.lean controls
lake env lean --run tools/view/GraphLibraryProbe.lean
lake env lean --run tools/view/GraphOrderingProbe.lean quick
lake env lean --run tools/view/GraphBoundsProbe.lean tools/view/out/graph-bounds-fixed
lake env lean --run tools/view/GraphContractProbe.lean tools/view/out/graph-contracts-fixed
python tools/view/graph_contracts.py tools/view/out/graph-contracts-fixed --before tools/view/out/graph-contracts
lake env lean --run tools/view/GraphMotion.lean tools/view/out/advanced-graph-cleanup
python tools/view/motion_inspector.py tools/view/out/advanced-graph-cleanup --out tools/view/out/advanced-graph-cleanup/motion.html
python tools/view/motion_inspector.py --self-test
python -m py_compile tools/view/motion_inspector.py tools/view/graph_contracts.py
```

The final narrow build passes with 520 jobs.
All listed finite probes pass.
The attachment probe checks 16 Flow specimens, with 81 bindings and 27 marks.
The bounds probe checks 28 style and geometry combinations.
The transition controls distinguish legacy sampling from production policy.
They include integer profiles for node swaps and reused point-to-node identities.
These profiles are finite evidence.
The ordering probe retains its comparison against the original ordering implementation.
Its updated baseline includes the producer's separate routing span.

The exporter emits 366 SVG frames across six flows.
The inspector validates those SVGs and reads 105 selectable final contacts.
The browser inspection checks nested-fork contacts at 20 times magnification in dark and paper looks.
It also checks wide-race playback and the repaired fork, swap, and self-loop controls.

The local outputs are regenerable and remain untracked.
The before controls remain available in `tools/view/out/graph-contracts`.

## Proof placement and audit boundary

The placement starts in `docs/research/2026-10-13-graph-defects-plan.md`.
Concept: `initial-algebras-folds`, concept 7.
Requirement: R14, through rendering checks and view navigation.
Role: tool lookup, finite-check characterization, docking, endpoint, and envelope observations.
The proposed rendering-check question remains a tool question under decisions row 334 (3).
No declaration changes the machine's relational meaning.

`KeyMap.get?_firstBy` supports the attachment lookup laws and the existing placed-point and route indices.
`GraphCheck.laid_iff` characterizes the expanded finite checker without a second statement.
Motion and bounds theorem placements appear in their lane receipts.

```text
lake env lean docs/research/2026-10-13-graph-defects-evidence/IntegrationAudit.lean
```

The pure-module audit passes for 1,037 declarations, with zero planned goals.
The rendering-module audit reports 45 of 1,396 declarations outside the strict axiom set.
Its paths reach existing String operations, program text, and host data.
The command therefore exits with an error for that second observation.
No axiom exemption is added.
The exact output is `docs/research/2026-10-13-graph-defects-evidence/IntegrationAudit.txt`.

The lane receipts retain stronger checked audit outputs and local proof scopes:

- `docs/research/2026-10-13-graph-attachment-motion-receipt.md`
- `docs/research/2026-10-13-graph-separation-receipt.md`
- `docs/research/2026-10-13-graph-bounds-receipt.md`
- `docs/research/2026-10-13-graph-attachment-probe-receipt.md`

This view-only slice reaches no outside Effect runtime or generated-code behaviour gate.
The existing manifest revision warning remains; no `lake update` runs.

## Next boundaries

Text ink needs host font measurements.
Node separation establishes no edge, label, or region clearance.
Local docking and envelope laws do not constitute a general theorem for every sampled layout.
Contact occurrence identities belong to one snapshot; arbitrary route reordering needs a stronger identity contract.
The motion pictures display structural reveals, not scheduler execution or decision tapes.

The next styling pass can consume explicit surfaces and junction roles for endpoint glyphs, selection, focus, and branch emphasis.
The viewport halo reserves caller-selected decoration room.
Nested regions, labels, arrows, and mixed junctions remain useful visual probes before adding new styles.
