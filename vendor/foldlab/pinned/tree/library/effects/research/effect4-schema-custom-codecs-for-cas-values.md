# Effect v4 Schema custom codecs for CAS values: an assessment

Status: conception-mode research, 2026-08-27. G0/G1 findings and
recommendations only; no ratified rule, model statement, or shipped API
changes here. Source is the pinned Effect study clone at
`.reference/clones/effect` (commit
`0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, the rc.111 correspondence
commit), read first-hand: `Schema.ts`, `SchemaTransformation.ts`,
`SchemaGetter.ts`, `SchemaRepresentation.ts`.

## Question

Certain CAS values need specific encode and decode behavior — bytes,
big integers, dates, optionals, branded domain types — beyond what a
plain struct schema gives. What does the v4 Schema implementation offer
for authoring such custom codecs, and what should the descriptor lane
adopt, constrain, or reject?

## Source-verified facts

- **The custom-codec machinery is `decodeTo`/`encodeTo` over
  `SchemaTransformation`** (`transform`, `transformOrFail`, `make`),
  with `SchemaGetter` carrying the directional halves, and
  `Schema.declare` / `declareConstructor` for foreign carriers with
  custom parse logic. Class-based schemas (`Schema.Class`,
  `TaggedClass`, `TaggedError`) give validated domain constructors;
  their instances are non-plain objects, but their **Encoded** forms
  are plain structs, which is the side the projection digests.
- **A vetted library of JSON-safe codec constructors already ships at
  the pin**: `Uint8ArrayFromHex` / `FromBase64` / `FromBase64Url`,
  `BigIntFromString`, `DateFromMillis` / `DateFromString`,
  `DateTimeUtcFromMillis` / `FromString`, `DateTimeZonedFromString`,
  and the `OptionFrom*` family, plus prebuilt transformations
  (`numberFromString`, `bigintFromString`, `dateFromMillis`, …).
- **`Schema.Json` is a type, and it is exactly the canonical-safe
  subset**: `null | number | boolean | string | JsonArray |
  JsonObject`, with `JsonObject` a readonly string-indexed interface.
  Finiteness of numbers is not in the type and stays a runtime
  property.
- No `Map`/`Set` codec constructors surfaced in the export sweep at
  this pin; set-like data needs explicit transformations regardless
  (see S2c).
- **`SchemaRepresentation`** is an open, compiler-extensible schema
  representation with a persistence-identity annotation
  (`{ id, payload: Schema.Json }`) and to/from JSON-Schema documents —
  nearby prior art for schema-shape identity, not a surface this lane
  uses today.

## How this meets the delivered projection

`Cas.value` digests the canonical JSON of the schema's **Encoded** form
inside the `{ revision, value }` envelope, and the canonical encoder
already rejects non-finite numbers, symbol keys, sparse or adorned
arrays, and non-plain prototypes — so a bad custom codec fails closed
at `put`, and the closed-input read (re-canonicalize and byte-compare)
refuses non-canonical payloads. The runtime guard is therefore already
the enforcement point; the recommendations below are about authoring
discipline and compile-time help, not new enforcement.

## Recommendations

**S1 — adopt the pin's constructors as the sanctioned vocabulary.**
Bytes as `Uint8ArrayFromHex` (or Base64 where size matters — pick ONE
per descriptor and never both), big integers as `BigIntFromString`,
instants as `DateTimeUtcFromMillis` (epoch number: no format or zone
ambiguity; prefer it over ISO strings), optionals via `OptionFromNullOr`
with the standing caveat that a nullable inner type must use a
distinguishing encoding instead. Document this as the CAS value schema
discipline in the README; spot-verify each adopted constructor's encode
determinism (e.g. hex casing) at the pin when first used.

**S2 — custom domain codecs enter through `decodeTo`/`encodeTo` under
three rules.** (a) *Deterministic total encode*: the encode direction is
a pure function of the Type value — the service-free bound already
blocks services, and discipline blocks impure lambdas (no clocks, no
randomness, no iteration-order dependence). (b) *Encoded lands in
`Schema.Json`* — with finiteness left to the runtime guard. (c)
*Round-trip stability as a per-descriptor fixture*: `put ∘ get ∘ put`
returns the same root. The runtime cannot see a normalizing decode
(e.g. case-folding hex) — it produces two roots for one logical value,
a dedup loss and an equal-roots subtlety rather than an error — so
every custom codec ships that fixture alongside PRJ-002's shape.
Set-like data encodes as explicitly sorted arrays; insertion-order
encodings are content-identity hazards.

**S3 — static tightening candidate (compile-time help).** Bound the
descriptor's schema as `Schema.Codec<A, Schema.Json, never, never>` so
a non-JSON Encoded form fails to compile, the same move as the
statically checked operation descriptions. Caveat to verify before
adopting: assignability of struct Encoded types to the `JsonObject`
index signature relies on implicit index signatures (mapped/alias types
carry them; hand-written interfaces do not), so the bound must be
checked against representative descriptors and dropped without loss if
it fights — the runtime guard already enforces the property.

**S4 — noted, not adopted:** `SchemaRepresentation`'s persistence
identity and JSON-Schema documents are prior art for a future question
— anchoring descriptor revisions to schema shapes — and nothing in this
lane should depend on it today.

## Rejected

- Digesting the **Type** side (class instances, branded carriers)
  instead of the Encoded form — the canonical encoder's plain-prototype
  rejection exists precisely to force the Encoded boundary.
- Ad-hoc `JSON.stringify` inside custom transformations — double
  encoding hides ordering and finiteness hazards from the guard.
- Any encode that reads ambient state; any Map/Set encoding that trusts
  insertion order.

## Obligations if adopted

S1/S2: README discipline section plus the per-descriptor round-trip
fixture pattern — documentation and test-shape only. S3: one type-level
change to `ValueOptions` behind a codex verification. S4: none.

## Source standing

The Effect clone is existing registered study material at its recorded
commit; no new sources, no new provenance entries required.
