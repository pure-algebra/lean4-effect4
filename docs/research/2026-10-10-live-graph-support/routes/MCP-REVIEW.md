# Independent snapshot preview review

The parent fixes four adapter findings before landing.
The cache law matches its stated assumptions.
The parent scopes snapshot identity to resolved tool responses.

## Reviewed source

The parent checkout is `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.
Its measured head is `066a6bcf2463abb917fe60fd2cdda10443ed090a`.
The review reads `tools/Tools/Session/Snapshot.lean`, the packet's `mcp/Preview.lean`, and the packet's `PLAN.md`.
`mcp-review.json` records their measured source hashes.
The review changes no parent file and builds no parent module.

## Findings and smallest repairs

1. `LiveGraphPreview.dispatch` emits reserved error `-32022` without its required version data.
   Its discovery branch also accepts an unsupported declared version.
   Include `supported` and `requested` in `error.data`.
   Apply the version check to discovery too.
   The [MCP versioning rule](https://modelcontextprotocol.io/specification/2026-07-28/basic/versioning) requires this error for every unsupported request version.
2. `LiveGraphPreview.fieldValid` rejects integral decimal path values.
   `LiveGraphPreview.idValid` rejects integral decimal request identifiers too.
   Lean's readers reject `1.0` and `0.0`, but accept `1e0`.
   The [JSON Schema numeric rule](https://json-schema.org/understanding-json-schema/reference/numeric) treats these values as integers.
   Read exact integral decimal values before checking their bounds.
   Use that reader in both validation and argument reading.
3. `LiveGraphPreview.dispatch` handles a malformed method before validating its request identifier.
   A null or object identifier therefore appears in the error response.
   The [MCP error schema](https://raw.githubusercontent.com/modelcontextprotocol/modelcontextprotocol/main/schema/2026-07-28/schema.ts) permits only string or numeric identifiers.
   Sanitize the identifier in every error constructor.
4. The byte pattern accepts a trailing newline under the chosen Python validator.
   Lean's `canonicalHex?` refuses that value.
   JavaScript's regular expression reader also refuses it.
   This finding concerns agreement with the chosen independent validator.
   Forbid every nonhex character explicitly in the emitted byte schema.
5. An undecodable snapshot produces a tool error without snapshot, path, or publication fields.
   Scope the response identity promise to resolved tool responses.
   Keep the original rejected input in the request transcript.

## Evidence and limits

`mcp-review-numbers.lean.txt` runs against the installed Lean toolchain without repository imports.
`mcp-review-numbers.log` records its successful finite evaluations.
`mcp-review-schema.py` uses `jsonschema 4.25.1` and `Draft202012Validator`.
`mcp-review-schema.log` records its independent numeric and byte evaluations.

`mcp-review-adapter.lean.txt` reads the parent's existing compiled preview artifact from a temporary file.
The probe runs outside the parent checkout.
`mcp-review-adapter.log` retains its exact output.
It reproduces malformed error identifiers, omitted version data, and the rejected decimal identifier.
The probe neither rebuilds nor fingerprints that compiled artifact.
Its output does not establish a source-to-artifact correspondence.

The discovery evaluation stops at an existing missing interpreter specialization.
The call evaluation stops at another missing specialization.
The log names both declarations.
The review treats neither interpreter failure as an adapter defect.
The discovery and undecodable-snapshot findings therefore rest on source inspection.

The supplied cache audit reports 28 declarations within `[propext, Quot.sound]`, with no planned goals.
The review does not repeat that build or audit.
`Snapshot.resolve_agrees` states equality with fresh resolution under `Snapshot.Valid`.
Its proof compares both entire byte strings and retains the empty application context.
The driver caches the resolved input session before preview editing.
Each later request still supplies its own explicit snapshot.
The source reaches no root publication or application execution operation.
These observations establish no scheduler, host execution, or production-server property.

## Parent response

The parent reports four repairs and additional finite controls.
It also adds explicit output flushing after an interactive stdio check.
This review does not verify those later changes.
The parent owns their build, protocol checks, and final receipt.
