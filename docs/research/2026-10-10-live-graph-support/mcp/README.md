# Explicit snapshot preview receipt

The adapter is an experimental stdio probe, not the proposed stable MCP server.
It changes no stored root and runs no application program.
Every tool request supplies its canonical program bytes, hole bytes, and selected path.
The application profile is empty.

## Files and entry points

- `tools/Tools/Session/Snapshot.lean` holds exact snapshot resolution and the cache invariant.
- [Preview.lean](Preview.lean) exposes inspection, replacement preview, omission preview, and SVG rendering.
- [Controls.lean](Controls.lean) reads the cache law and exercises its boundary cases.
- [probe.py](probe.py) drives the process interactively and checks responses against the public protocol schema.
- [schema-source.json](schema-source.json) pins that schema by upstream commit and SHA-256.
- [requests.jsonl](requests.jsonl) and [responses.jsonl](responses.jsonl) retain the actual protocol exchange.
- [preview.svg](preview.svg) and [preview.png](preview.png) retain the rendered typed-hole example.

The four tools are `effect4.inspect`, `effect4.fillPreview`, `effect4.omitPreview`, and `effect4.renderPreview`.
Their input schemas derive from `Op.fields` through the existing `Shape` alphabet.
The same field table checks the supplied arguments.
Unsupported shapes refuse schema generation.
The input validator accepts canonical lowercase hex, strings, and paths of safe nonnegative JSON integers.
Integral decimal notation receives the same reading as integer notation.

A resolved response carries the output snapshot, requested path, answer, and `published: false`.
An undecodable input returns a tool error; its original bytes remain in the request transcript.
A preview never becomes implicit input to the next request.
Clients must explicitly supply its returned bytes to continue from it.

## Proof placement

The five-point placement is in [../PLAN.md](../PLAN.md).
The concept is `initial-algebras-folds`; the proposed compatibility question is `cache-invisible`, serving R14.

`Snapshot.resolve_agrees` states equality of complete resolved sessions with fresh resolution.
Its premise is `Snapshot.Valid`, and its context is the empty application.
`Snapshot.prepare_valid` establishes the invariant for fresh preparation.
`Snapshot.resolved_valid` retains it after a successful lookup.
The adapter caches that input session before applying a preview operation.
These helpers serve the resolver and its adapter consumer.

Exact byte equality includes the hole table.
The proof needs no digest collision premise.
It establishes no shared-root publication, concurrent edit commutation, arbitrary application profile, or runtime migration.
The adapter's JSON construction and dispatch receive finite checks, not a general protocol theorem.

## Verification

[protocol-results.json](protocol-results.json) records the measured check count, request count, driver exit, source hashes, and schema identity.
The runner sends each request while keeping standard input open.
A reply must arrive before the next request is sent.
This exercises actual interactive stdio, rather than supplying an entire transcript followed by EOF.

The controls cover:

- discovery, the fixed tool list, and response schemas;
- replacement preview and the existing same-type splice result;
- old snapshots, explicitly adopted new snapshots, and alternating clients;
- omission, its retained hole table, and SVG rendering;
- malformed snapshots without cache contamination;
- negative, fractional, and excessive path indices;
- integral decimal paths and request identifiers;
- extra fields, missing fields, and noncanonical hex;
- version-error data, including discovery requests;
- missing per-request metadata, malformed identifiers, and unknown methods;
- notifications without responses.

The cache module's cycle-aware audit covers 28 declarations within `[propext, Quot.sound]`.
It reaches no planned goal.
[controls.log](controls.log) retains that narrow audit.
The combined branch repeats it in [../integration/snapshot.log](../integration/snapshot.log).

The existing `Tools.Session.answer` JSON and text path reaches `Classical.choice`.
The failed attempt to place a wrapper theorem over that whole path remains in [initial-wrapper-audit.log](initial-wrapper-audit.log).
The final cache law stops before that existing rendering boundary and compares every field of session data.
No trust exception or frozen theorem changes.

The independent review is [../routes/MCP-REVIEW.md](../routes/MCP-REVIEW.md).
Its four adapter defects have dedicated controls in the final protocol run.
The fifth finding narrows the response identity promise to resolved inputs.
The first interactive run also found buffered output; explicit flushing repairs it.
[initial-stdio-timeout.log](initial-stdio-timeout.log) retains the failed run.

## Reproduction

Install the independent validator in a temporary directory:

```sh
python3 -m pip install --target /private/tmp/effect4-mcp-jsonschema jsonschema==4.25.1
```

Fetch the immutable URL in `schema-source.json` to `/private/tmp/effect4-mcp-schema-2026-07-28.json`.
The probe checks its exact SHA-256 before validation.
`MCP_SCHEMA` and `MCP_VALIDATOR_PATH` can select other local paths.

Build the narrow imports and run the controls serially:

```sh
LEAN_NUM_THREADS=3 lake build Tools.Session.Snapshot Tools.Session Tools.View.Flow Tools.View.Output ProofGraph.AxiomAudit
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-live-graph-support/mcp/Controls.lean
LEAN_NUM_THREADS=3 python3 docs/research/2026-10-10-live-graph-support/mcp/probe.py
```

The driver itself runs with:

```sh
LEAN_NUM_THREADS=3 lake env lean --run docs/research/2026-10-10-live-graph-support/mcp/Preview.lean
```

Render the retained SVG without running browser content:

```sh
rsvg-convert docs/research/2026-10-10-live-graph-support/mcp/preview.svg -o /private/tmp/effect4-snapshot-preview.png
```

The inspected SVG contains only paths, rectangles, text, grouping, and clipping.
It has no external references or scripts.
The static image shows the typed hole, its source line, generated code, and structural flow.
The in-app browser refuses local file URLs, so visual inspection uses this local raster reading.
Font rendering remains platform-dependent; this check establishes no pixel equality across platforms.

## Remaining boundary

The prototype has no resource subscriptions, persistent store service, publication operation, authentication, cancellation of long work, or runtime execution.
It implements a finite MCP profile with an explicit one-MiB line bound.
The stable server still needs the choices in `docs/research/2026-10-09-mcp-code-mode-design.md`.
Its broader operation alphabet and schema-agreement theorem remain future work.
No production-server or complete-MCP claim follows from these finite checks.
