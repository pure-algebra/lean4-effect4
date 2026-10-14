# Graph regions and packing receipt

The landing adds a view projection and independent component packing.
Compound boundary routing remains open.
The projection changes no program or machine meaning.

## Revisions and scope

Base: `5cd537aef9838da43d4f9377d033028bddf7403a`.
Code head: `f25c74f3e2c6acd2bf4ad85c7cbd205dcc8952e0`.
The attached `2026-10-13-graph-scale-evidence/ChangedPaths.txt` lists the changed paths.
The package pin remains `e51195721f47fa767fb84f918dc439e76d83071f`.

`GraphRegions.prepare` in `tools/Tools/View/GraphRegions.lean` checks an explicit region forest and selection.
`GraphRegions.project` retains original edge occurrences, payloads, and endpoints.
`GraphRegionsView.prepare` in `tools/Tools/View/GraphRegionsView.lean` joins that projection to the existing graph.
`GraphPacking.pack` in `tools/Tools/View/GraphPacking.lean` packs independent rectangles in stable height order.

## Commands and evidence

Run commands from this worktree with `LEAN_NUM_THREADS=3`.

```text
lake build Tools.View.GraphRegionsView Tools.View.GraphPacking
lake env lean docs/research/2026-10-13-graph-scale-evidence/IntegrationAudit.lean
lake env lean --run tools/view/GraphRegionsGallery.lean tools/view/out/graph-regions
python tools/view/graph_regions.py tools/view/out/graph-regions --measurements docs/research/2026-10-13-graph-packing-trial-1.csv --measurements docs/research/2026-10-13-graph-packing-trial-2.csv --measurements docs/research/2026-10-13-graph-packing-trial-3.csv --measurements docs/research/2026-10-13-graph-regions-evidence/Benchmarks.jsonl
python -m py_compile tools/view/graph_regions.py
git diff --check
```

The narrow build passes.
The attached `Build.txt`, `IntegrationAudit.txt`, and `Gallery.txt` record the Lean command results.
The checked axiom gate admits only `propext` and `Quot.sound`.
Its output reports 577 declarations, zero planned goals, and 2943 checked constants.
The gallery emits seven graph specimens and three packing specimens.
Each packing specimen contains twelve production drawings.
Python compilation and the whitespace check pass.

Browser inspection covers dark and paper looks, nested collapse, stable member selection, hidden edge provenance, packing, and node contact crops.
The generated screenshot is `tools/view/out/graph-regions/inspection.png`.
The generator owns the output directory.

## Proof placement

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Required property: each view operation agrees with its stated data observation.
Question role: tool laws under decisions row 334 (3) and row 336 (8).
Consumers: region projection, component packing, and the gallery.
Reach: successful finite checks, edge occurrence provenance, rectangle containment, separation, and occurrence retention.
Limits: these laws establish no machine judgment or optimal packing result.
Requirement: R14 view authoring.
The lane plans and receipts place each theorem and name its consumer.

## Measurements and limits

The packing trials measure input generation, packing, and digest computation together.
The region trials include input rotation that prevents compiler hoisting.
The gallery reads these measurements from the retained evidence files.
Neither measurement describes full graph layout or browser frame rates.

Arbitrary collapse can create displayed paths absent from the source graph.
The region controls include that counterexample.
The general ancestor selection and member partition properties remain finite controls.
Text ink remains unmeasured.
Compound enclosures and boundary ports need a separate layout contract.
The graph input checker and layered layout still contain repeated scans.

This slice reaches no Effect runtime comparison gate.
The source edits stay within the view tool and its specimens.
No whole-tree battery or dependency update runs.
