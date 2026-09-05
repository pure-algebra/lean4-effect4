# Surface ingest contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.8)

Implementation (owed): `Effect4.Surface.Ingest (planned module; the packet remains red)`

Battery: `Test/Surface/IngestContract.lean`

Counterexamples: `E4-SURFACE-CE-053` through `E4-SURFACE-CE-057`,
`E4-SURFACE-CE-069`, and
`E4-SURFACE-CE-007`, `E4-SURFACE-CE-008` (shared with
`surface-jsonschema.contract.md`)

Witnesses: `Test/Counterexamples/Surface/Ingest.lean`

## Purpose

Wrapping: an existing resource enters the estate as rows. Four decoders, one
per wire form, each total on the fragment it admits and refusing everything
else **by constructor**, with the offending name inside the constructor and
never as a free-form string.

Totality on the admitted fragment plus refusal by name is the whole claim. A
decoder that silently drops a keyword it does not model turns an unmodeled
resource into a modeled-looking row, which is the failure this contract
exists to prevent; `E4-SURFACE-CE-008` is that attack.

## Frozen public declarations

All in namespace `Effect4.Surface`.

`Refusal` is the one closed alphabet of
`Test/contracts/surface-facts.contract.md`; the constructors this module uses
are `unknownKeyword`, `unsupportedContentType`, `unsupportedRefTarget`,
`unsupportedMethod`, `unsupportedParameterLocation`, `unsupportedBindingKind`,
`unsupportedShape`, `streamingResponse`, `recursiveSchema`,
`declarationSchema`, `missingField`, and the two semantic clauses
`identifierMissing` and `descriptionMissing`.

```lean
structure Ingested (refs : List Effect4.ReferenceEntry) where
  domain : Domain
  api    : Option (Api refs) := none
  server : Option (McpServer refs) := none

def ofOpenApi (j : Effect4.Json) :
    Except Refusal (Σ dom : Domain, Ingested (Domain.refs dom))
def ofMcpToolsList (j : Effect4.Json) :
    Except Refusal (Σ dom : Domain, Ingested (Domain.refs dom))
def ofWrangler (j : Effect4.Json) : Except Refusal Deployment
def ofJsonSchema (j : Effect4.Json) :
    Except Refusal Effect4.Representation
```

The `Σ` in the two rich decoders is forced: the decoded `Api` is indexed by
the reference table of the decoded `Domain`, and the plan's `Json → Except
Refusal (List (Tool refs))` leaves `refs` unbound. See finding 3 of the
wave-1b report; the builder may replace the sigma with an equivalent bundle
provided every counterexample below still observes only the `.error` side.

## Observations

1. `(ofX j).toOption.isNone`, the refusal observation, which is the one every
   counterexample in this packet uses.
2. The exact refusal value, for the four refusals the plan names explicitly:
   multipart, a `$ref` outside `#/$defs/`, an unknown keyword, and an
   unsupported binding kind.
3. `ofWrangler j : Except Refusal Deployment`, compared against a literal
   `Deployment` term on the positive fixture.
4. The round trip `ofWrangler (Deployment.wranglerJson d).get! = .ok d` on
   every fixture deployment.

## Acceptance conditions

- `ofOpenApi` admits: `paths`, the seven methods of `Method`, `parameters`
  with `in` in `{path, query, header}`, a `requestBody` whose content is
  exactly `application/json`, and `responses` keyed by a numeric status whose
  content is `application/json` or empty.
- `ofOpenApi` refuses, by these constructors:
  `multipart/form-data` and every other request-body content type with
  `unsupportedContentType` (`E4-SURFACE-CE-053`); `in: cookie` and any other
  location with `unsupportedParameterLocation` (`E4-SURFACE-CE-054`); a
  method outside `Method` with `unsupportedMethod`; a `text/event-stream`
  response with `streamingResponse`.
- `ofWrangler` admits `name`, `main`, `compatibility_date`, `kv_namespaces`,
  `d1_databases`, `r2_buckets`, `queues.producers`, `vars`, `services` and
  `durable_objects.bindings`, and refuses every other binding table with
  `unsupportedBindingKind` carrying the table's key
  (`E4-SURFACE-CE-055`). A missing `name` or `compatibility_date` is
  `missingField`, never a default.
- `ofMcpToolsList` admits a `tools` array of objects with `name`, optional
  `description` and an `inputSchema` that `ofJsonSchema` admits, and refuses
  a non-object `inputSchema` with `unsupportedShape`
  (`E4-SURFACE-CE-056`).
- `ofJsonSchema` refuses a `$ref` outside `#/$defs/` with
  `unsupportedRefTarget` carrying the pointer (`E4-SURFACE-CE-007`), and any
  unmodeled keyword with `unknownKeyword` carrying the keyword
  (`E4-SURFACE-CE-008`).
- **Every entity produced by any decoder carries `stance := .ingested`.**
  Not `canonical`, not `view`. An ingested row that presents as canonical is
  the same defect class as a silently dropped keyword
  (`E4-SURFACE-CE-057`).
- Plan §15.3: an ingested row carries the source's descriptions where the
  source has them, and the refusal names the ones it lacks. A source object
  with no `description` (OpenAPI `summary`/`description`, an MCP tool's
  `description`, a JSON Schema `description`) is refused with
  `descriptionMissing` naming the kind and the row, not decoded into an
  undescribed and therefore ill-formed entity (`E4-SURFACE-CE-069`).
- Where an emitter is a left inverse of a decoder on the admitted fragment,
  the round trip is a `#guard` on the fixtures. Where it is not, the battery
  names the refusal or the quotient instead; it does not assert a round trip
  that holds only on the chosen fixture.

## Assurance allocation

Graph edge `SURFACE-PG-INGEST`. A decoder from an external wire form is
admission and refusal plus an external-agreement claim, which is squarely on
the graph route of `AGENTS.md`.

| obligation | evidence at landing |
| --- | --- |
| admission | `#guard`s: each positive fixture decodes to a literal row set |
| refusal | the five counterexamples above, each an exact `.error` value |
| round trip | `ofWrangler ∘ wranglerJson = .ok` on the fixture deployments; the OpenAPI and MCP directions are `#guard`s over fixtures with their quotient named |
| stance | `E4-SURFACE-CE-057`: every decoded entity is `.ingested` |

## What this contract does not claim

It does not claim any decoder is total on its wire form: each is total on a
named fragment and refuses the rest. It does not claim the refusal alphabet is
minimal or final; a builder may add constructors, but may not replace one with
a string and may not remove one a counterexample names. It does not claim the
decoded rows reproduce the source resource's behaviour, only its shape on the
admitted fragment.
