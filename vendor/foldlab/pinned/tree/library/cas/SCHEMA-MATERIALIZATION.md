# Effect Schema materialization — integration plan

**Status: RATIFIED by the operator 2026-08-29, in-session, with
stipulations:**

- **S1 — Metaprogramming-forward.** Take full advantage of Lean 4
  metaprogramming, macros, and `Expr` semantics for expressiveness and
  DX. Efficient modular design with a DEEP API: hide complexity and the
  risk of proof doom loops behind small public surfaces.
- **S2 — The DAG rides annotations.** The annotation surface at the
  expected API carries the DAG — addresses, related schemas, twenty
  encoded other schemas if wanted. That is the power of the
  metaprogramming position; the namespace is open by design (string
  keys, `foldlab/...`).
- **S3 — Custom schema declarations over brands.** Brands are a maybe
  (open ruling 4 stays open); the priority extension point is custom
  schema declarations (the `Declaration`/reviver/`toCode` contract).
- **S4 — THE stipulation: a schema is just another extension of the DAG
  language.** Schemas are minted from DAGs, and referenced AS schemas —
  by address — not only as concrete instances. This directs open ruling
  2 (references = content addresses; exact spelling confirmed at Slice
  C). Everything else is detail until the dev work lands.
- **S5 — One language, five seats (operator-directed 2026-08-29).**
  Naming patterns and descriptions stay aligned with estate language,
  the DSL goals, and the estate's design patterns. Every API designed
  on this codebase is judged from all five seats at once: USING the
  software, PROGRAMMING it, READING it, PROMPTING an agent with it,
  and RUNNING computations on it — all within the same language. A
  name or surface that works in one seat and jars in another is not
  done. (This is AE-8's expressibility principle and the verbal
  register's determinism law applied to API design.)
- Housekeeping ordered: the stale
  `.claude/worktrees/entity-store-parallelize-d0a1cd/` worktree is
  deleted.
- Implementation delegated to Opus 5 subagents per the standing
  coordinator order.

Evidence base: three reader passes over the pinned Effect 4 source
(`effect@4.0.0-rc.111`, commit `0dd7825e`, live in
`library/effects/node_modules/effect/src/`), the estate's schema plane
(`library/cas/Cas/Schema/`, `library/effects/src/cas/`), and the prior-art
record (`docs/entity-store/research/schema-ast-census.md`,
`.staging/scouts/2026-08-25-mapping/`, `experiments/entity-store-extract/`).
Line citations below are to the pinned source.

## The finding that shapes everything

Effect 4 ships the integration surface this lane was going to build.
`SchemaRepresentation.ts` is an **open, compiler-extensible, first-order
representation of Effect schemas** with:

- `toRepresentation` / `toJson` / `fromJson` — the persistent form
  (what our revision-1 `SelfCodec` already mirrors);
- `fromRepresentation(doc, {revivers})` — reconstruction of a **live,
  running validator** from stored content (validation-gen, native);
- `toCodeDocument` — a complete Representation → TypeScript **code
  generator** (codegen, native), with topological sorting, recursion via
  `Schema.suspend`, and import management;
- `fromJsonSchemaDocument` / `toJsonSchemaDocument` — JSON Schema
  draft-2020-12 in both directions with a semantic round-trip guarantee
  on the exact subset;
- three extension points, all annotation-borne, all reduced to
  `{id: string, payload: Json}`: opaque **Declarations**, opaque
  **Filter** checks, and per-id **revivers** — exactly the
  no-identity-in-a-function shape the estate's law already demands.

The estate has never called `fromRepresentation`, `toCodeDocument`, or
`fromJsonSchemaDocument`. The integration is therefore mostly *adoption
and confrontation*, not construction.

## Design position (the base)

**P1 — The Lean `Ast` grows toward the store-admissible subset of
`SchemaRepresentation.Representation`.** Effect has drawn the first-order
line (22 constructors, `SchemaRepresentation.ts:406-428`); the canonical
schema remains the ROOT and Effect Schema a CARRIER, never an authority
(IMPLEMENTATION-PLAN §13). The Lean side's job is unchanged in kind:
define the admissible subset, prove its discipline (WF, canonicality,
codec laws, round trip), and pin the persistent bytes. What changes is
the target: the subset is a subset *of Effect's own representation
algebra*, so the byte pin confronts Effect's `toJson` image directly.

**P2 — Store metadata rides annotations, never constructors.** String
keys only (symbol-keyed annotations are silently dropped at persistence
and codegen — `pruneAnnotations`, `SchemaRepresentation.ts:927`;
`renderAnnotations`, `toCodeDocument.ts:51`). Namespace: `foldlab/...`
slash-keys; never the reserved `~*` space. Persistence identities
(representation ids) follow the built-in convention:
`foldlab/cas/<name>`. Attachment discipline: the representation lowers
the **encoded** side (`toRepresentation.ts:113`), and `annotate` lands on
the last check when checks exist (`SchemaAST.ts:3369-3377`) — metadata
intended to persist attaches via `annotateEncoded` or before checks, and
reads via Effect's `resolve` semantics, not raw `Base.annotations`.

**P3 — Every foldlab declaration and check ships the full contract:**
`representation.id` + reviver + `toCode` + `toArbitrary` (and
`toEquivalence` where meaningful). That is what makes a foldlab construct
indistinguishable from a built-in across persistence, revival, codegen,
validation, and instance generation. Today `foldlab/cas/ref` has id +
reviver only; `toCodeDocument` and `toArbitrary` both throw on it.

**P4 — Reuse Effect's check ids verbatim.** All ~70 built-in filters
carry `{id, payload}` identities (`effect/schema/isInt`,
`effect/schema/isMinLength`, …) with revivers and `toCode` already
shipped. A Lean-emitted check that speaks those ids inherits Effect's
own revival and codegen for free. The check-id allowlist (46 check ids +
29 declaration ids, cataloged in `B-effect-identity.md`) is the admission
vocabulary; per the census verdict, an **allowlist is the only safe
admission rule** for the open annotation bag.

**P5 — Transformations never become content.** Effect erases them from
the representation by design (`getLastEncoding`, no `Link` counterpart);
the estate's law says no canonical identity lives in a function. The two
positions agree. If generated codecs ever need a transformation, it is a
named, registry-resolved link id on the TS side — a projection concern,
never store content.

**P6 — Dual conformance gates.** The estate's byte-identity gates keep
carrying identity (canonical payload bytes, addresses). On top:
*differential* gates against Effect's own machinery — our emitter vs
`toCodeDocument` (generator and reference emitter as each other's check,
never self-comparison — the R6 discipline applied to Effect itself), AST
structural equality via `TestSchema.Asserts`, and
`verifyLosslessTransformation` as the per-codec law.

## The admissible subset (proposed, for ruling)

| Representation node | Proposal | Notes |
|---|---|---|
| `Null, Boolean, Number, String` | admitted (already) | `.int` = `Number`+`isInt` check |
| `Literal` (bool/int/str) | admitted (already) | literal-null collapses to `Null` (register R13) |
| `Arrays` — full `elements` + `rest` | **grow** | tuples and array-with-rest; per-element `isOptional` |
| `Objects` — full: `isMutable` bit, `indexSignatures` | **grow** | records; do NOT collapse the four key bits (type/encoded × optional/mutable) |
| `Union` (`anyOf`/`oneOf`) | **grow** | the materializer-lane blocker; no v0 encoding tricks |
| `Enum` | **grow** | plain data, cheap |
| Checks layer: `Filter`/`FilterGroup` as data `{id, payload, aborted}` | **grow** | id allowlist per P4; `FilterGroup` nests left, identity is the tree |
| `Suspend` + `Reference` + `references` table | **grow** (recursion ruling below) | rev-1 `references` is emitted `{}` today — the table is unreachable from Lean |
| `Declaration` | admitted (already: `foldlab/cas/ref`) | contract completion per P3 |
| `Undefined, Void, Never, Unknown, Any, ObjectKeyword` | defer | TS-flavored keywords; no store meaning yet; admission is cheap when a consumer arrives |
| `BigInt` | defer | int-width semantics decision first |
| `TemplateLiteral` | defer | regex-adjacent hazards (Effect's own importer defaults `patterns:"error"`) |
| `Symbol, UniqueSymbol` | refuse | Effect's persistent codec itself rejects local symbols — no reconstructable identity |

## Slices

**Slice A — complete the declaration contract, TS side** (small; unblocks
Effect's native codegen today):
1. `toCode` + `toArbitrary` on `foldlab/cas/ref` (`Value.ts:263`).
2. Decide/fix the `representationOf` annotation-slot read
   (`CanonicalSchema.ts:139` reads `Base.annotations`; Effect resolves
   off the last check — census `:203-209`).
3. First differential gate: the four registered codes through
   `fromJson → fromRepresentation → toCodeDocument`, compared against
   `emitwire`'s output by AST equality after evaluation
   (`TestSchema.Asserts.ast.fields.equals`), plus
   `verifyLosslessTransformation` per code.

**Slice B — the revision-1 decoder and door, Lean side** (fixes a live
defect): `Ast.ofRepresentationJson` — strict decoder of the admitted
rev-1 subset — with round trip and injectivity (the named open
obligations of `SelfCodec`), then re-aim `ingest` at revision 1
(normalize → decode rev-1 → gate). Today's `ingest` decodes only the
retired rev-0 tagged spelling: it cannot ingest anything the live plane
emits. Rev-0 decode remains as the legacy/read-compatibility arm.
Also reconcile the Integer disagreement (ruling 3 below) so both
revisions project one code to one Document.

**Slice C — universe growth, one constructor per slice**, in commission
order: `Union` → `Arrays` (tuple/rest, unblocks the tree-sitter
materializer lane) → `Objects` completion (key bits + index signatures)
→ `Enum` → checks layer → `Suspend`/`Reference`/references table.
Each slice ripples through: `Ast` ctor + `WF` + codec laws + `El` +
`Described` + rev-1 mirror + `EmitAst` lowering + fixtures + pin + an
**admission-map row** (the A-1/ACC-2 discipline from the extract lane:
every inventory variant dispositioned, no bijection assumed, no field
undispositioned).

**Slice D — the materializer** (the codegen/validation-gen engine
proper): the dynamic door composing what exists —
`payload/address → decode → gate → materialize` — with two output
registers: Effect-native (`fromRepresentation` for live validators,
`toCodeDocument` for source, with the foldlab reviver/toCode registry)
and estate-native (`EmitAst`/`Ts` printer for provenance-stamped,
byte-gated committed modules). The two registers differentially test
each other (P6). "Materializer" owes a minting pass in CONTEXT.md
(MATERIALIZER-LANE.md names the debt).

**Slice E — foreign JSON Schema ingestion**: `fromJsonSchemaDocument →
toRepresentation → toJson → normalize → gate against the admitted subset
→ admit`. This is the "any well-formed JSON" door, using Effect's own
importer as the acquisition instrument (R15 loop; importer output is
evidence, the gates carry trust). `patterns: "error"` stays the default.

## Open rulings (operator)

1. **The admissible subset** — the table above.
2. **Recursion / references**: rev-1 `references` names are `$ref`
   strings; the deferred commission item says references carry their
   target schema's **address**. Proposal: reference name = the target's
   content address (or a name annotated with it), `Document.references`
   assembled from store words at materialization — DAG assembly as
   MultiDocument. This decides Slice C's last step.
3. **Integer semantics**: rev-0 decodes `Integer` as
   `Int.check(isBetween(MIN_SAFE, MAX_SAFE))` (matches Lean `SafeInt`);
   rev-1 emits bare `isInt`. One of them is the canonical meaning.
4. **Brands**: structurally identical, nominally distinct types collapse
   to one address (A-expressibility L-3509, "most consequential"). The
   named escape hatch — brand as an identity-bearing check
   (`{id: "effect/schema/brand", payload: name}`) — needs a yes/no.
5. **Variance defect D1** (grammar upgrade vs compiler-API carve-out):
   NOT blocking this lane — `SchemaRepresentation.ts` and
   `SchemaParser.ts` parse clean under the pinned grammar and the twin
   already gates them — but it blocks full R8 surface ingestion and
   should be decided before the first libfree corpus run.
   (Also: EFFECTS-BACKEND.md:247 "five of eight affected classes" is a
   misstatement of "five of eight affected modules.")

## Ruling queue — accumulated in-flight (2026-08-29, post-ratification)

Items surfaced by the landed slices, awaiting operator rulings; rulings
1-5 above stay open except where noted:

6. **Union identity — RULED 2026-08-29** (UNION-DESIGN.md, promoted):
   order is identity, both modes carried and admitted, Stage 1 landed
   to order. Stage 2 (discriminated denotation) joins
   deriving-for-inductives — LANDED.
15. **D1, the deriving handler's member spelling**: `deriving
    Described` orders a derived union's members by ascending tag
    string, not source order, so that shuffling an inductive's
    constructors does not move its address. Order stays identity to
    the CARRIER (nothing rearranges a code); the choice is the
    generator's, made once. R17's register row owes both clauses.
    Ratify or reject the sort.
16. **Parameter-free restriction on the alternatives path**: the
    structure path derives for parametric types; the
    constructor-alternative path refuses them, because the union code
    has nowhere to spell a type parameter and the emission reads
    constructor field types as closed expressions. Not a defect — a
    scoped restriction with a named refusal — but it is the obvious
    next growth request, and it wants the reference/`Suspend` slice
    (C6) more than it wants a handler change.
17. **`_tag` as the estate's discriminant name**: adopted verbatim
    from Effect's `TaggedStruct` so a derived union materializes as
    idiomatic TypeScript with no translation. It reserves the field
    name in every derived member, and it constrains member field names
    to sort at or after `_tag` (uppercase-initial JSON names are
    therefore refused on this path). Ratify the reservation.
18. **`Schema.TaggedUnion` is NOT the TypeScript mirror**: Effect's
    `TaggedUnion` constructor builds at the default `anyOf`, and a
    derived union's mode is `oneOf`, which is part of its identity. The
    hand mirror therefore spells `Schema.Union([...], { mode: "oneOf" })`.
    Confirmed live: the derived code regenerates faithfully through
    `toCodeDocument` (the literal-collapse defect of ruling 13 cannot
    fire, because no member is a bare literal).
7. **The three adopted Effect declaration rows** (`effect/schema/Date`,
   `URL`, `Option` — C-decl merge `78f38364`): ratify or reject.
   Adopted verbatim per P4 so the general constructor is inhabited; no
   estate identity minted.
8. **`Ast.ref` as sugar for `Ast.decl` row zero**: kept open by
   construction (the `DeclarationId.General` split costs nothing either
   way).
9. **Reserved annotation kind tag**: annotation nodes currently reside
   at caller-chosen tags (suite uses `0x41`); minting an
   `AnnotationKindTag` is plane identity and wants Lean and TS
   counterparts together.

   **SHARPENED by the exchange kind, 2026-08-29** (`Cas/Schema/
   Exchange.lean`): for the annotation kind the residence tag is
   genuinely the caller's, because nothing in the code refers to it.
   The exchange kind is not free that way. Its subject union has an
   `exchange` arm — the edge a conversation is walked along — and that
   arm has to name a tag, so `exchangeKindTag = 0x58` is spelled inside
   the code and is therefore PART OF THE FIXTURE'S ADDRESS. It is
   unreserved (`Cas.value` accepts it, `ReservedKindTags` does not list
   it), so today it is a working tag; but a kind whose own references
   are self-referential cannot leave its tag to callers, and moving it
   later moves the schema's address. Minting it is the same question as
   the annotation tag, one degree more forced.
10. **TS-side declaration rows**: `CanonicalSchema` does not yet admit
    Date/URL/Option-carrying schemas (Lean-root asymmetry; follow-on
    lane, not a defect).
11. **The parser dependency, named**: `cas_from_store` (DERIVING-DESIGN
    §4) requires a Lean-side strict JSON parser — none exists
    (`Values/Json.lean` is render-only). The parser slice is the SAME
    work as the standing "bytes determine the canonical value"
    obligation (ruling: injectivity of the canonical rendering), so one
    slice discharges both debts. Sequencing decision owed.

    **Narrowed, 2026-08-29** (`Values/JsonInj.lean`,
    `Schema/PayloadInj.lean`). The obligation is now ONE `Prop`,
    `Cas.Json.RenderPlainInjective`, and everything above it is wired:
    `payload_inj` (equal payloads, equal `repNorm`, under `WF`) and its
    `RepNormal` corollary are derived from it, and the schema-plane
    steps under it — `deNumNorm_numNorm_envelope`,
    `envelope_numNorm_inj` — are proved unconditionally. Three findings
    the wiring surfaced:
    - the naive statement is FALSE (`renderPlain_not_injective`): the
      value model has two number constructors with one decimal
      spelling, so injectivity holds only up to `Value.numNorm`;
    - the `WF` premise is LOAD-BEARING and not decoration —
      `Ast.decl .date (.nat 5) []` and `Ast.decl .date (.int 5) []` are
      two codes with one payload byte string, ruled out only by the
      registry's payload discipline;
    - the escape half is DISCHARGED (`escapeCompact_inj`,
      `renderPlain_str_inj`), which was the expected wall. What remains
      is `Nat.repr` injectivity (the toolchain ships no such lemma) and
      the self-delimiting/follow-set argument — i.e. the parser proper.
      The sequencing decision is therefore narrowed to: write the
      parser, or write the digits inverse plus the follow-set induction.

    **CLOSED, 2026-08-29** (`Values/Digits.lean`,
    `Values/JsonParse.lean`). The parser was written; it discharges
    both debts, and `payload_inj` / `payload_inj'` / `payloadBytes_inj`
    are unconditional theorems. What landed:
    - `Cas.Json.parse : String → Option Value`, structural on fuel (no
      `partial`, no well-founded recursion, no `native_decide`), with
      the fuel the entry point supplies being the input's own length.
      `String` rather than `ByteArray` because `Ast.payloadBytes` is
      `Ast.payload.toUTF8` and `String.toByteArray_inj` already carries
      the byte step; a `ByteArray` parser would owe a UTF-8 decoder
      proof nothing needs.
    - `parse_render` (adequacy): on canonical values, `parse
      (renderCompact v) = some v.numNorm`, with `parse_render'` on the
      nose for `NumNormal` values — the `repNorm` treatment, mirrored.
    - `parse_sound` (exactness): every accepted document IS the
      canonical rendering of the value answered, and that value is
      `NumNormal`. With adequacy, the image of `parse` is exactly the
      image of `renderPlain`.
    - `Cas.Json.renderPlain_injective : RenderPlainInjective`. Survey
      blocker B7 closed: "the node at this address IS this code" is a
      fact.
    - `Cas.Schema.ingestBytes` — the bytes-in door, `parse` composed
      with `ingest`, with `ingestBytes_wf` and `ingestBytes_payload`.
      The R15 loop's missing first step.

    Three findings worth the record:
    - `Nat.repr` injectivity cost almost nothing: the toolchain ships
      no such LEMMA, but Lean 4.33 ships the INVERSE
      (`Nat.ofDigitChars`, `Nat.ofDigitChars_ten_toDigits`), which was
      the expensive half. The narrowing above assumed otherwise.
    - `RenderPlainInjective`'s `Canonical` premises are NOT needed.
      `JsonParse.renderPlain_inj` is the unrestricted statement; the
      premises were an artefact of the anticipated proof route through
      the sort.
    - `unescapeOne` is a left inverse ON THE ENCODER'S IMAGE, which is
      less than a strict parser needs — it reads `A` as `A` and
      `` as a backspace, neither of which the encoder emits. A
      parser built on it directly would accept two spellings of one
      string and `parse_sound` would be FALSE.
      `JsonParse.unescapeCanon` closes it by re-encoding what it read
      and demanding the input spelled it that way.

    SORTED KEYS, decided: `parse` does not require them and does not
    impose them. It answers objects in the order the bytes carry them,
    and canonicality is the gate's question — the door's existing split
    ("Shape is the decoder's question; discipline is the gate's",
    `Ingest.lean`), and what keeps `parse` a left inverse of
    `renderPlain` rather than of `renderPlain` restricted to canonical
    values. `ingestBytes` runs `canonValue` exactly as `ingest` does.
12. **Declaration registry documentation home**: the wire-identity
    table lives in `Declarations.lean`'s docstring; `REGISTRY.md` is
    scoped to kind tags. Promote or leave.
13. **Effect upstream defect, confirmed by the C1 differential gate**
    (2026-08-29): `toCodeDocument` collapses an all-bare-literal union
    to `Schema.Literals([…])` (`toCodeDocument.ts:559-566`), and
    `Literals` carries no mode slot — a `oneOf` literal union
    regenerates as source meaning `anyOf`. Effect's generated TEXT is
    therefore not a faithful regeneration path for literal `oneOf`
    unions; the stored representation and the estate's own emitter
    are. Demonstrated live by the `union-pin` fixture's `exact`
    member, loss stated where it bites; not worked around. Decide:
    report upstream, and/or exclude literal-`oneOf` from any future
    reliance on Effect's text generation.

    **WEIGHED AT THE ADDRESS, 2026-08-29**
    (`MaterializeDifferential.test.ts`, items 17/18): with both
    registers committed and EVALUATED, the two printers agree on the
    denotation of every registered fixture except `union-pin`, and
    there they differ at exactly one datum — `exact`'s mode.
    Re-lowering each evaluated schema and admitting it answers the
    address `addresses.json` pins for all seven estate-emitted modules
    and for six of seven Effect-emitted ones; `union-pin` is the
    seventh. The loss is therefore a measured ADDRESS DRIFT, not a
    reading of the printer's source. It is a difference of identity and
    not of decision: `exact`'s members are disjoint literals, so
    `oneOf` and `anyOf` accept the same values, and the suite pins that
    too.
14. **Union refusal taxonomy**: empty `types` refuses as `illFormed`,
    unknown `mode` as `notASchema` — both `#guard`-pinned. A separate
    `emptyUnion` name would be a taxonomy change, available on order.
15. **THE FLOAT CEILING** (surfaced late from the 2026-08-25
    expressibility dossier, `A-expressibility.md:73` — belongs at the
    top of any "any Effect Schema" conversation): `Value` has no float
    (`Cas/Core/Node`-plane `Core.lean:30-32`). Effect's bare `Number`
    cannot type `1.5`, `Literal(1.5)` has no term, and non-integral
    check parameters (`greaterThan(1.5)`) are unwritable. This is
    rejection, not collapse — admission must turn such schemas away
    until a float ruling exists (representation, canonical spelling of
    doubles, NaN/±0/precision — a value-plane commission question, far
    upstream of the schema plane). Bounds what "full Effect Schema
    coverage" can ever mean; decide posture explicitly.
16. **Materializer-lane blocker, half-discharged**: the tree-sitter
    materializer lane (`.staging/treesitter/MATERIALIZER-LANE.md`) was
    blocked on union AND `mu`/named references. Union landed (C1);
    recursion/references (C6, ruling 2) is the remaining half.
17. **Materialized-source compile gate — CLOSED 2026-08-29**: both
    registers' output is committed under
    `library/effects/test/generated/materialized/` and therefore
    typechecked by `bun run typecheck` (`tsconfig.test.json`), with
    `MaterializeDifferential.test.ts` re-rendering the Effect-native
    snapshots so a stale one is a red suite rather than a stale file.
18. **The estate-native second register — CLOSED 2026-08-29**
    (`tools/Materialize.lean`): `lake exe materialize` reads each
    committed schema payload back through `ingestBytes` and prints the
    recovered code with the Lean printer into a provenance-stamped
    module per fixture under
    `library/effects/test/generated/materialized/estate/`, byte-gated by
    `--check` in `check:cas`.
19. **THE TWO DOORS DISAGREE** (JIT-substrate survey B8,
    `.staging/schema-materialization/JIT-SUBSTRATE-SURVEY.md`,
    2026-08-29): a stored schema Lean's `ingest` refuses `illFormed`
    can still materialize into a live TS validator — the TS door runs
    no `wf` gate and its reviver allowlist is a different list from
    `DeclarationId.all`, with unknown ids thrown rather than refused
    by name. The survey's staged proposal (0-6, blockers-first) fixes
    it at stages 1-2 (the disagreement-vector conformance gate, then
    the generated `wf` gate on the TS door under R11). Sequencing of
    the six stages is the operator's; stages 3+4 are ruling 11's
    slice.

    **STAGES 1-2 LANDED 2026-08-29.** `lake exe verdicts` emits
    `conformance/schema-verdicts.json` — 51 codes (28 admitted, 23
    refused) and 85 value triples, every verdict computed by running
    `ingest` and `decode` — under a `--check` byte gate in `check:cas`;
    `library/effects/test/SchemaVerdicts.test.ts` replays it through
    `Materialize`. The gate landed RED on 16 codes and closed at stage
    2 with `admitDocument`, the pre-revival admitted-subset gate on the
    TS door (`CanonicalSchema.ts`), which mirrors
    `Ast.ofRepresentationJson` and `Ast.wf` together, refuses through
    the caller's failure channel with `SchemaRefusal` carrying Lean's
    own five refusal names, and is checked name-for-name against the
    corpus. The allowlist is now ONE list: `DeclarationRegistry` rows
    carry their own reviver and payload discipline, and `Revivers`'
    declaration arm is derived from them. **The gate mechanism is now
    GENERATED** (2026-08-29): `admitDocument` is an interpreter over
    `Cas/Backend/Admission.lean`'s table — node tags, key lists, the
    admitted check spelling, the literal and enum value types, the
    union modes, the declaration columns, the safe-integer bound and
    every clause's refusal name — emitted by `lake exe emitgate` under a
    byte gate in `check:cas`, so the door's shape is typed once, in
    Lean. Two findings ride along —
    item 20 below, and this: ruling 3 predicts a value-plane Integer
    disagreement and there is none, because `Schema.isInt` runs
    `Number.isSafeInteger` (`Schema.ts:8227`), the bound `SafeInt`
    carries. Ruling 3 remains open as a SPELLING question only.
20. **Effect upstream defect — the empty struct admits excess**
    (confirmed by the stage-1 corpus, 2026-08-29): Effect's decoder
    skips the excess-property check entirely when an `Objects` node has
    no property signatures and no index signatures, so
    `Schema.Struct({})` accepts `{"a":1}` under
    `onExcessProperty: "error"` while the same schema with one field
    refuses it. Lean's `decodeFields [] (_ :: _)` answers `none`, so the
    empty struct is the one place the two doors still part on a VALUE.
    Not a `wf` question — the code is well-formed and both doors admit
    it — so no admission gate can close it. Pinned as
    `struct-empty/excess` in `SchemaVerdicts.test.ts`, which asserts it
    still disagrees. Decide: report upstream, and/or stop admitting the
    empty struct. Sibling of item 13.

21. **THE ANNOTATION-BAG DIVERGENCE** (found by the generated gate,
    2026-08-29, `1eda46c5`): Effect's own `toJson` persists an
    `annotations` bag on Declaration nodes (`Schema.Date` stores
    `{"annotations":{"expected":"a valid Date"},…}`). Lean's exact
    decoder would refuse all three adopted rows AS ACTUALLY STORED;
    the hand gate admitted them by ignoring extras; the disagreement
    corpus never caught it because corpus payloads are Lean-emitted —
    a structural blind spot in the vector, now visible. The generated
    interpreter keeps the tolerant reading (behavior preserved), keys
    consumed as REQUIRED. RULING: does the estate store Effect's
    annotation bag (grow the Lean decoder) or strip it at the door
    (normalize step)? Recorded in `Cas/Backend/Admission.lean`'s
    header.
22. **`cas_run`'s manifest scope** — RULED AND DISCHARGED, 2026-08-29
    (the brain-stem package). `RunParams` served the
    puts-with-answer-indices sub-fragment; the full `PProg` carries
    literal-address operands and `load`. The operator ruled the
    manifest GROWS, because a program stored at an address cannot be
    run unless the document can name an address. What landed:
    `RunOperand` (a `cas_union` of `answer | literal`), `RunRef.source`
    typed by it, `RunInstruction` a union of `load | put`, and
    `RunRefParams` for the new `cas_run_ref` row. `manifestVersion`
    bumped 0 → 1 and `implementedManifestVersion` followed in the same
    change — the boot gate's first real use. The two theorems that
    pinned the limit (`RunRef.ofPRef_lit`, `RunInstruction.ofPLine_load`,
    both refutations) FLIPPED to positive statements and collapsed into
    one totality theorem, `ofPProg_isSome`: every well-formed table has
    a document. `Law.registry`'s SM-22 row was amended in the same
    commit, which the law index forced rather than allowed. Manifest
    bytes moved, deliberately, and the emitter's TypeScript fragment
    widened to carry `Literal` and `Union` codes to render them.
23. **Route `EmitProg` through `PProg`**: triage found three spellings
    of the program document, not two — the emitter lowers trees
    straight to TypeScript and never builds a `PProg`. Routing it
    through the table turns the surviving prose claim into a theorem
    and collapses the third spelling. Its own slice, STILL OWED — but
    narrowed by the brain-stem package, and the narrowing is worth
    recording. `tools/EmitPrograms.lean` now computes each program's
    step and cont addresses from `treeProg tree` — the same `PProg`
    the lift document is built from — and stamps the cont address into
    the generated module's own docstring (R7's stamp clause, item O4 of
    the paperwork audit, discharged). So the emitter now READS the
    table even though it still does not LOWER from it. What remains is
    exactly the lowering: `progStmts` walking a `PProg` instead of a
    `Tree`, which is what makes "the emitter emits only puts whose
    references name earlier answers" a theorem instead of prose.
24. **Surface-ledger blind spot**: `meta/out/surface.META.json` walks
    the `Cas` library only — `Cas.Backend.*` is invisible to
    retrieval-before-generation. One-line fix in `tools/Surface.lean`'s
    import set when convenient.
25. **Replay-vocabulary reactivation precedes any `Utterance` slice**
    (Exchange landing, 2026-08-29, `dbcaa709`): the growth path for
    role-tagged multi-turn transcripts lands on the dormant
    effect-replay vocabulary — "Solicited delegation" IS a recorded
    invoke/outcome pair, "Decision trace" IS an ordered record of
    turns. The Exchange kind deliberately reused neither. Reactivating
    that vocabulary for the prose pillar is a ruling to make BEFORE an
    Utterance slice, not during one.

26. **REGISTRY.md omits the git sort** — CLOSED 2026-08-29 by the
    grammar manifest. REGISTRY.md is no longer hand-written: the whole
    file is the Markdown projection of `Cas.Grammar.manifestV0`,
    regenerated by `lake exe emitgrammar` and byte-gated in
    `check:cas`. The 0x47 row landed with it, and a `#guard` now says
    every `Ty` constructor has a row, so the omission class is closed,
    not just this instance. The row's versioning prose is DRAFTED, not
    ratified — the operator's to rule on.

    **The registry's last reconciliation debt is paid, 2026-08-29** (G3
    of the reification-substrate growth order): rows 14/15 (`step`,
    `cont`) were RESERVED tags spelled as bare `UInt8` defs in
    `Cas/Lang/Defun.lean` and held there by `#guard`s pinning
    `Ty.ofTag`'s refusal of both. They are now `Ty.step` and `Ty.cont`
    with real Node-witness forms, the refusal guards are gone with the
    reservation they pinned, and `Defun`'s two names are abbreviations
    of the sorts' own tags. No registry row is reserved or formless
    today; the `.reserved` row id, the `.reserved` status, and their
    guards are kept unpopulated for the next reservation.
27. **The rc.111/rc.112 split**: library/effects pins
    `effect@4.0.0-rc.111` (the provenance lock); the workbench and
    experiments/lift-harness are on rc.112 (foldkit peer-pins it
    exactly). The workbench's package.json carries an honest C6
    pending mark declaring its pin unresolved. RULING: upgrade the
    estate's lock to rc.112 (re-confronting the SchemaRepresentation
    surface the readers pinned) or hold the front-end lane on a
    version the lock does not record. The split is real and someone
    must own it.
28. **A generated grammar/sort surface is owed** — CLOSED 2026-08-29.
    `lake exe emitgrammar` emits
    `library/effects/src/cas/generated/grammar/manifest.json` (the
    front ends' surface) and `REGISTRY.md` from one described
    manifest, `Cas.Grammar.manifestV0`. Layouts are not transcribed:
    every form carries a `Tree` witness and the guards read the tag,
    the payload width, and the reference discipline off `Tree.node`,
    so an encoder change moves the bytes or turns the build red. Three
    of the reverse-engineered layouts were wrong and the manifest
    states the encoders instead (the `tree` sort's two forms, the
    `entry` sort's note payload, the `manifest` and `file` sorts'
    reference slots). Interpreting the JSON is the front ends' lane;
    nothing in TypeScript was written here.

29. **The node-document put register is owed**: `cas put` ships as
    bytes+tag (a strict subset, refs always empty — minting nothing),
    but IMPLEMENTATION-PLAN's CLI grill ruled put's input to be the
    described canonical node document; a node with links still cannot
    be spelled from the shell. Recorded in the verb's docstring.
30. **The `--json` second register is owed on every verb** (CLI grill
    round 2 ruling 2): only `show` has one; init/status/ls and the
    three new verbs match the existing state, not the ruling.

31. **The Architecture matrix is narrower than the shipped
    composition**: the SQL roots adapter exists and the kvs row still
    reads read/write only; the capability matrix is pinned two-sided
    (TS value + Cas/Architecture.lean + the shared pin), so the row
    addition is a paired change — owed.
32. **A9, the outputSchema drop** (salvage dossier, testable on
    rc.111): Effect's MCP pin emits outputSchema only for
    object-typed results; a tagged-union reply — the refusal
    envelope's exact shape — advertises none. Test before the host
    lane wires result schemas; if confirmed, the envelope may need an
    object wrapper, which is a Lean-side spelling decision.
33. **Law-ID-to-test binding** (salvaged from the old era's LAWS.md):
    the ruling queue records rulings but binds none to enforcing
    tests; the old-era check-laws gate failed in BOTH directions.
    Adopting the index is a discipline slice; the salvage carries the
    working prior art (attic/correctness-gating-laws).

## Defect register (found in passing, not part of the plan)

- `Ty.context` (0x0D) is a RATIFIED tag with no `Tree` constructor:
  nothing in `Cas/Grammar/Tree.lean` writes the sort's layout, and the
  only elaboration is `CasExamples.AgentStep.contextNode` at the `Node`
  layer (empty payload, open edge list). Found while building the
  grammar manifest, which states the gap rather than inventing a
  layout and `#guard`s that `context` is the ONE formless sort row.
- `Ingest.lean` is untracked, rev-0-only, unconsumed (fixed by Slice B).
- `representationOf` annotation-slot read (fixed by Slice A).
- Rev-0/rev-1 Integer disagreement (ruling 3).
- ~~`Cas/Backend/Ts.lean` imports `Cas.Schema.Foreign` and never uses it.~~
  **FIXED** in `34145109`; the file now carries no `import` line at all.
- `.claude/worktrees/entity-store-parallelize-d0a1cd/` holds a stale
  duplicate of `Foreign.lean` era files.
- Extractor promotion EXT-6 not wired into `mise run gen`.
- `Foreign.lean` type-expression strings remain rfl-proved against
  hand-written strings, confronted by nothing on the TS side (the known
  R8 note; Slice A's differential gate begins the confrontation).
