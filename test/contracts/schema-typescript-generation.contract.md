# Schema TypeScript generation contract

Status: implementation slice, 2026-08-31

Implementation: `Effect4/Target/TypeScript/Schema.lean`

Battery: `Effect4Test/Target/TypeScript/SchemaGenerationContract.lean`

Host harness: `scripts/check-schema-typescript-generation.sh`

Coverage corpus: `Effect4Test/Target/TypeScript/SchemaGenerationCoverage.lean`

## Boundary

The generator consumes the existing `Json`, `Representation`, `Check`,
`Document`, and `MultiDocument` carriers and produces the existing TypeScript
`Expr`, `Decl`, and `Module` syntax. It defines no second schema or document
type.

`jsonSource`, `representationSource`, `documentSource`, and
`multiDocumentSource` render individual raw values. `generate?` is the
high-level boundary for a complete module containing the raw
`Schema.Json`, the `SchemaRepresentation.Document` revived from it, and named
associated data. Callers do not need to assemble target syntax or invoke the
generic renderer.

Generation refuses illegal or colliding binding names, field-inadmissible
documents, duplicate reference/annotation/JSON object keys, and duplicate
data names. A `__proto__` data key lowers through `Object.fromEntries` so it
remains an own data property rather than activating object-literal prototype
semantics.

Binary64 JSON payloads lower to an explicit big-endian `DataView`
reconstruction. This pins the generated reconstruction instruction and does
not by itself claim that every JavaScript engine preserves every NaN payload
through later numeric operations.

## `Described`

Effect4 has no `Described` instance in this slice. Foldlab's `Described`
requires a well-formed code, a denotation, a two-way equivalence with a Lean
type, and both inverse laws. Raw persistence and source generation do not
satisfy that stronger contract. The later lossless-codec classification may
provide the native replacement without duplicating the Schema carrier.

## Proof graph

`TS-PG-SCHEMA-DOCUMENT-GENERATION` owns this nonlocal recursive bridge:

```text
Schema Json/Representation/Check/Document
  -> recursive target lowering
  -> generation admission
  -> TypeScript syntax and deterministic bytes
  -> direct TypeScript compiler
  -> pinned Effect fromJson
  -> Effect language-service diagnostics
```

The recursive lowering equations, exact source fixtures, rejection cases,
kernel dependency report, direct compiler check, host revival, and language
service diagnostics are required edges. The coverage corpus proves that its
22 top-level representatives map to the exact canonical tag census, embeds
both persisted check constructors, pins the generated-source digest, and
checks the same order after Effect revival. Source-target denotational
simulation remains a later edge. The higher-order authoring helpers attach
local equation receipts to the existing Schema graphs and do not receive a
ceremonial graph.

The kernel receipt makes the trust split explicit. Recursive lowering and
generation admission reach only `propext` and `Quot.sound`; final source
rendering also inherits `Classical.choice` from Lean's standard UTF-8 string
fold. The repository gate grants that dependency only to the six named
source-emission declarations, alongside the renderer module, and rejects a
stale exemption. Every other declaration in the Schema generation module
retains the tighter ceiling.
