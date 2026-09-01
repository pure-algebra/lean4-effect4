/-!
# Schema.Codec.lean

Owner: Decoded, encoded, decode-service, and encode-service codec indices.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

One four-index `Codec decoded encoded decodeRequirements encodeRequirements`.
`Schema`, `Decoder`, `Encoder`, and `Top` are existential **views** of that
codec, not additional carriers.

Decode and encode requirements stay distinct. The decode path is
`FE -> FT -> TE -> TT`; the encode path is `TT -> TE -> FT -> FE`.
Requirement rows and their normalization and union laws come solely from
`Effect4.Data.Row`; Context owns key interpretation and environments, not the
row carrier.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

`SC-CODEC-01` primitive codec, `SC-CODEC-02` decodeTo construction,
`SC-CODEC-03` exact decoded/encoded indices, `SC-CODEC-04` exact directional
requirement unions, `SC-CODEC-05` decode pipeline semantics, `SC-CODEC-06`
encode pipeline semantics, `SC-CODEC-07` law-grade classifier and witnesses,
`SC-CODEC-08` existential views.

`SC-CODEC-07` is why there is no universal round-trip theorem: codecs are
*classified* by which laws they satisfy, and each class needs a witness.

## Gated by

The getter proof lane and `DATA-ROW-01/02/03`. Empty requirements lower to
TypeScript `never` and row union lowers to a TypeScript union, so the row
carrier must be frozen before any lowering claim.

## Host evidence at the pin

Read off rc.112 source; not executed here, and host-local (see
`SC-REP-CENSUS-PIN` in `docs/SCHEMA-CUTOVER.md`). Reading source establishes
what the host *code says*. It closes no `SC-CODEC-*` obligation and is not a
compatibility result.

**The four indices are the host's own.** `Schema.ts:1041` declares
`Codec<out T, out E = T, out RD = never, out RE = never>`, carrying `Encoded`,
`DecodingServices`, and `EncodingServices` as separate members. The ownership
note above is therefore not an Effect4 invention; it matches the pin's arity,
and the two requirement indices default to `never` exactly as the lowering
claim in "Gated by" assumes. That the *defaults* are `never` is the reason the
lowering claim has a base case at all; it remains gated on `DATA-ROW-01/02/03`
because the default is not the union law.

**The document boundary is the trivial requirement case.**
`DocumentFromJson : Schema.Codec<Document, Schema.Json>` (`:1098`) and
`MultiDocumentFromJson` (`:1105`) leave both service indices defaulted, so at
the persisted boundary rc.112 requires no service in either direction. This is
a useful base case for `SC-CODEC-04` and nothing more: it fixes one point, not
the union law that `SC-CODEC-04` must state.

**Failure at that boundary is out-of-band.** The four document operations are
built with `Schema.encodeSync` / `Schema.decodeSync` (`:1112-1115`), which
signal failure by throwing rather than by returning a result. `toJson`
(`:1134`) and `fromJson` (`:1177`) inherit that. So the host's document codec
is a partial function whose failure mode is not in its return type, and
`SC-CODEC-05` / `SC-CODEC-06` must not model these as total.

**A separate host round-trip claim is semantic, not syntactic — and scoped.**
The JSON-Schema compiler/importer path, not the persisted document codec,
states a round-trip guarantee twice. Both statements restrict it to accepted
values and explicitly disclaim shape equality: "the emitted document and
reconstructed representation may have different shapes" (`:840`) and
"keyword layout, definitions, and annotations may be normalized" (`:1276`).
It further excludes opaque declarations from the exact subset (`:846`). This
is prior art for how `SC-CODEC-07` might classify laws, not evidence that an
Effect4 class is inhabited and not a law of `toJson`/`fromJson`.

**Where the recursive closure lives.** The recursion knot is
`RepresentationSchema = Schema.suspend(() => RepresentationUnion)` (`:912`),
a host closure in the *codec*. The `Suspend` field itself holds
`thunk : Representation` (`:162`, codec `:988`), which is first-order data.
This is narrow: live document annotations can still contain arbitrary values,
while persistence prunes non-JSON annotations (`:927-947`). Thus the recursive
closure is not part of persisted `Suspend` content, and replacing the codec
knot with structural recursion changes the decoder rather than that field's
wire content. The knot also widens its own encoded index to `unknown` (`:913`),
so the host gives up the encoded type precisely at the recursive occurrence.

**One vendored executable serialized-string probe exists and is small.** The sealed
vendor file
`vendor/foldlab/pinned/tree/library/effects/test/SchemaReferencesPin.test.ts:258-265`
asserts `JSON.stringify(toJson(fromJson(json)))` equals `JSON.stringify(json)`
for four fixtures inside one test. This packet does not execute that
TypeScript test. Even when run, it is finite evidence about those serialized
strings: it does not establish stable emission order in general (`SC-DOC-07`)
and is not a round-trip theorem.
-/
