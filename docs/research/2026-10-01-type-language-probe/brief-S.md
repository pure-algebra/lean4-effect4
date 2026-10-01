# Seat S: the Schema side, per form, and the readable profile

Read `README.md` here first. Your folder: `docs/research/2026-10-01-type-language-probe/S/`.
Worktree `/Users/pooks/Dev/lean4-effect4-probe-S`, branch `probe/S`. Read in full: synthesis §2
(NS0–NS5), R3.4, R3.5, §3.4's K2 rows, §8 Q6–Q7; the effect seat's `note.md` §1 (rc.112's
Schema AST, 21 node kinds), §3 (the usage counts, `member_histogram.log`), §4a–4e
(`2026-10-01-data-probe/effect/`); Codex's review of Gemini's scouting, its `probe-review.md`, and
the Gemini report itself (`/private/tmp/codex-schema-scout-review-2026-10-01/`: `review.md`,
`probe-review.md`, `gemini-report.md`, `SchemaExprProbe.reviewed.lean`, the host probes
`inference.ts`, `inference-red.ts`, `runtime.mjs`, `reuse.mjs` with logs); `src/Effect4/Schema/`
(`Bridge.lean`: `schema`, `ofSchema`, `requirementKey`; `Codec.lean`: `fields?`, `encodeRaw`,
`decodeRaw`, `tagged`; `OfShape.lean`; `Document.lean:101-111`), `src/Effect4/Codegen/Schema.lean`
(`RepresentationAlgebra`, `cata_representation` at `:235-309`, the references table written as a
JSON object at `:310-322`, `moduleSyntax`, the persisted-document contract at `:340-377`),
`src/Effect4/Laws/Schema/Codec.lean` (`decode_of_encode`, `encode_sub`, `hasTy_decode`),
`Test/Schema/` (the `schema-codec` gate, `DialectContract.lean`), `Test/contracts/schema-*.contract.md`;
decisions rows 39 (landed), 8 (the dedupe, option (C) recommended), 123 (the in-program decode
operation), 128.

**The one thing.** Two threads meet here. First, every form the data wave adds needs its K2 arms:
`schema`/`ofSchema` at records (`objects` with named properties only; refusing index signatures,
optional keys until stage 4, decoding annotations by name), at optional keys (`optionalKey` versus
`optional`), at maps (`Record`), at tagged unions (`Union` of structs with a `_tag` literal), at
`Number`/`Int` (stage 5 with row 108), and the JSON codec's object layout with `fields?`'s exact
field set, modulo the key-order normaliser `N_J`. Second, the owner wants the Schema face readable:
Gemini scouted a readable emission profile and Codex found the prototype changes accepted inputs,
lacks located refusals and asserting controls, and omits a bounded upstream route
(`fromRepresentation` with pinned revivers → `toCodeDocument`). Do Codex's "next slice of
scouting" properly, and tie it to the per-form arms so one profile serves records, optional keys,
maps, tagged unions and the checks `Bridge.schema` already writes for `nat`/`int`.

## Questions

1. **K2 per form, on copies.** For each form (record, optional key, map, tagged union, number/int):
   the `schema` arm (what `Representation` node, which annotations, which checks), the `ofSchema`
   arm (the exact admitted node shape, every refusal located by path and reason), the codec's
   encode/decode arms, and the three laws (`ofSchema_schema` modulo `N_S`; `decode_of_encode`;
   `encode_sub`) re-proved on a copy of `Bridge.lean`/`Codec.lean` with a copy of `Ty` that has
   the form (coordinate the copy's shape with seat P's `ProbeTy`: same constructor text). Measure
   lines. The `Success`/`Failure` branch-image confusion (row 128) at the new forms: does a record
   and a tagged union share an image? State the canonical-branch check that excludes it.
2. **rc.112's own behaviour at the edges**, tested with `bun` and the vendored rc.112 on files in
   your folder: `Schema.Struct` with a permuted object literal (accepted); extra keys (`onExcessProperty`);
   `optionalKey` versus `optional` on an explicit `undefined`; `Schema.Record` key order and
   duplicate keys; `Schema.Union` of tagged structs (`toTaggedUnion`); `__proto__`, `a-b` and
   Unicode property names in `Schema.Struct` (Codex: the computed-key spelling keeps precision;
   upstream `toCodeDocument` mis-emits `__proto__`). Record every command, version and exit.
3. **The readable profile.** Define, as a named admission profile (a predicate on `Representation`
   with a located refusal), the subset: strings, booleans, numbers with the checks `Bridge.schema`
   writes (`nat`: integer and non-negative; `int`: integer), nested required records, arrays,
   tuples, literal unions, tagged unions, optional keys, `Record`, with exact property spelling
   (identifier, quoted, computed) and an explicit policy per annotation and modifier (preserved
   or refused by name, never dropped). Write the readable emission as a second algebra over the
   same `cata_representation` (never replacing `moduleSyntax`), emitting `Schema.Struct({…})`,
   `Schema.Union([…])` (the array call shape), `Schema.Tuple([…])`, `Schema.Array`, `Schema.Record`,
   `Schema.optionalKey`, `Schema.mutableKey`, `Schema.Literal`, the checks by name. Asserting
   controls (`#guard`), not `#eval` prints: the admitted inputs emit the expected text; the refused
   inputs refuse with their path; a tuple is not an array; a union keeps the array call shape; a
   mutable field keeps `mutableKey`; an annotation on an unsupported node refuses.
4. **The bounded upstream route, compared.** Reproduce Codex's `reuse.mjs` (persisted document →
   `fromRepresentation` with the two built-in revivers → `toCodeDocument`), extend it to the
   profile's forms, and compare with the Lean emission on generated source types and decoder
   behaviour (`tsgo` at the harness's version for the types; `bun` for the decoders), on ordinary
   and adversarial names separately. Measure coverage per form, source size, and the refusals.
   Say which route the profile should take per form, and what the other is for (a reference, a
   test oracle, or nothing).
5. **Row 8's dedupe at the emitter** (option (C), recommended): the references table written as
   a JSON object (`Codegen/Schema.lean:310-322`) deduplicated by key with a located refusal for a
   conflicting repeat; which generated artefacts under `harness/schema-generation/` change (the
   unmeasured part of receipt G's item 1). Measure on a copy.

## Deliverable

`S/note.md`: per question the evidence; the per-form K2 table (form, `schema` arm, `ofSchema`
admitted shape and refusals, codec layout, the three laws' status on the copy, lines); the
readable profile's admission predicate and algebra as a probe under `S/probes/` with its
asserting controls and `tsgo`/`bun` logs under `S/host/`; the comparison table of the two routes;
the proposed decisions rows (a readable-profile row with the contract; row 8's (C) measured; row
123's input if the profile changes it) and the brief text for the data wave's commit 5 and for a
Schema-face slice.
