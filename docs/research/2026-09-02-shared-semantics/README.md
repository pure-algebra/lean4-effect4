# Shared semantics research evidence

This bundle supports the operator-requested research on ten questions connecting
Effect4 reification with web standards semantics, dated 2 September 2026. The
finished reading artifact is `output/pdf/effect4-web-standards-semantics.pdf`
at the repository root.

The research source is `report-source.md`. `source-ledger.json` records primary
sources, exact local source hashes, question mappings and remaining gaps.
`evidence-manifest.json` records bundle-file hashes. `verification/` records the
commands actually run, full frame axiom receipts, independent corpus
reconciliation and document checks. The proposed laws and exploratory
counterexamples do not constitute a newly frozen public contract or cutover
battery.

## Corpus evidence

`corpus/selected-pins.tsv` records the 30 selected repositories and their exact
commits. `summary.json` and `per-repo.tsv` retain aggregate and per-repository
results. `scan.json.gz` contains the complete site records and parse errors;
`inventory.json.gz` contains selected file lists and package declarations.
Both are deterministic gzip containers. Their uncompressed hashes are in
`verification/corpus-reconciliation.json`.

The original scripts are preserved without changing their measured bytes:
`inventory.py`, `scan.cjs` and `summarize.py`. Their original workspace root is
`/Users/pooks/Dev/foldlab/corpus`; their original scratch directory is
`/tmp/effect-q9-research`. The scanner uses TypeScript 5.9.2 from
`/Users/pooks/Dev/foldlab/experiments/lift-harness/node_modules/typescript`.
Its `Q9_INVENTORY` and `Q9_OUTPUT` environment variables override the default
JSON input and output paths. To reproduce on a different machine, restore the
recorded repositories and pins and adjust a working copy of the path settings.
Keep the archived measured inputs unchanged.

The original sequence was `python3 inventory.py`, `node scan.cjs`, then
`python3 summarize.py`. A second full scan agreed on the ordered source digest.
The alias, shadowing and loop fixture is retained under `corpus/fixture/`, with
its input inventory and actual scan output. The scan is syntax-based; it is
neither a project typecheck nor a control-flow reducibility analysis.

## Lean and runtime evidence

`rows/` retains every generated Lean input, timing script, trial and expected
failure. The timing scripts were run from `/Users/pooks/Dev/lean4-effects`,
using `/tmp/effect4-row-research-20260902` as their scratch directory. They
include process startup and imports. Some limit/transparency/association
experiments intentionally fail; those failures are evidence, not unresolved
report-build failures.

`rows/counterexamples.lean` contains the nine exploratory semantic witnesses.
It was independently checked from the Effect4 checkout with `lake env lean`.
The repository used sibling dependency overrides and reported a stale
dependency manifest; the report does not claim a clean fetched build.

`host/host-probes.mjs` contains the five runtime cases and a lazy-construction
assertion; `host/promise-order.mjs` contains the separate reaction-order case.
Their `.json` siblings retain actual outputs. Run them with Node v22.23.2;
the Effect imports name the installed rc.112 package in Foldlab's local
`library/effects/node_modules`. The source ledger records the equality of its
relevant source hashes with Effect4's pinned vendor files.

## Rebuilding the document

`render_report.py` takes a Markdown source path and a PDF destination path.
It uses ReportLab and the desktop's bundled DejaVu fonts; its font directory
is explicit at the top of the script. The original bundled Python was
`/Users/pooks/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3`.
The renderer does not fetch sources or run experiments. The PDF was checked
with pypdf, pdfplumber and Poppler, with sampled rendered-page inspection.

## Interpretation limits

Counts are sites in a selected, mixed-version corpus. They are not execution
frequency or a representative production sample. Row measurements are finite
front-end experiments. Host observations are finite Node results. Suggested
simulation, resource and backpressure laws remain proof obligations. The
report and ledger identify the boundaries for each question.
