import Cas.Schema.Declarations
import Cas.Schema.Ast
import Cas.Schema.El
import Cas.Schema.Codec
import Cas.Schema.Described
import Cas.Schema.Foreign
import Cas.Schema.SelfCodec
import Cas.Schema.PayloadInj
import Cas.Schema.Ingest
import Cas.Schema.Basis
import Cas.Schema.Projection
import Cas.Schema.AdmissionMap

/-!
# The schema plane — layer above the values, root of the hierarchy

The canonical schema as a universe: codes (`Ast` — the Lean twin of
the TypeScript v0 constructor set), denotation (`El` — a code is a
type), and the generic codec with its laws proved once over all codes
(forward under canonical fields, exactness unconditionally,
injectivity). `Described` attaches ordinary Lean carriers to codes by
an explicit equivalence; `Foreign.RepresentedIn` attaches the decoded
and encoded target-language types plus their codec surface. Nothing
stands above these codes; Effect Schema carries them at runtime, and
every future tree type is meant to arrive through a described code.

Named increments, in order:

- **Recursion** — named definition environments (the shape tree-sitter
  `node-types.json` and JSON Schema `$defs` actually have), with
  conformance as an inductive predicate and a fueled sound-and-complete
  checker: the admission pattern applied to schemas.
- **Deriving extension** — the opt-in `Cas.Schema.Deriving` module
  generates `Described` instances for non-recursive structures while
  leaving compiler metaprogramming outside this runtime facade.
- **Self-description** — LANDED (2026-08-28): `SelfCodec` carries the
  codes' JSON projection, the schema-node envelope, and the canonical
  payload, cross-pinned byte-for-byte against the TypeScript
  `CanonicalSchema.payloadOf` (`lake exe schemas --check` +
  `test/CanonicalSchemaPin.test.ts`). What is proved:
  `encode_canonical`/`renderCompact_encode` (`Codec/Laws/Render.lean`)
  show the encode image is canonically spelled and the canonical
  rendering performs no reordering on it, and the RETIRED revision-0
  projection carries the full discipline —
  `toJson_canonical`/`legacyEnvelope_canonical`/
  `legacyEnvelope_renderPlain`, with `ofJson_toJson`/`toJson_inj`
  making it a proved round trip. The LIVE revision-1 representation
  now carries the same discipline (Slice B): `toRepresentationJson_-
  canonical`/`representationDocument_canonical`/`envelope_canonical`
  hold UNCONDITIONALLY — revision 1 keys every object alphabetically
  by construction and carries a struct's fields as an array, so `WF`
  is not a premise — and `payload_renderPlain` is the byte
  consequence. `Ast.ofRepresentationJson` is the strict decoder, with
  `ofRepresentationJson_toRepresentationJson`/
  `toRepresentationJson_inj` the round trip and injectivity, both
  stated modulo the literal-null collapse (`Ast.repNorm`,
  `Ast.RepNormal`) — the ONE identification the revision-1 projection
  makes, which no decoder can undo (register R13). The verified-parser
  argument that was named open here has LANDED
  (`Cas.Json.renderPlain_injective`, `Cas.Values.JsonParse`); what
  remains open is `Ast.ofRepresentationJson`'s image being `RepNormal`
  (true by inspection — the decoder has no `.lit .null` arm — but not
  yet proved as a theorem).
- **Payload injectivity** — LANDED (`PayloadInj`, unconditional since
  the parser slice): `payload_inj` — for well-formed codes, equal
  payload bytes give equal `repNorm`, with `payload_inj'` the
  on-the-nose `RepNormal` corollary and `payloadBytes_inj` the same at
  the schema node's bytes. Two things the derivation pins: the
  rendering identifies `Value.nat n` with `Value.int n`, so the value
  plane can only conclude equality up to `Value.numNorm` and the
  schema plane undoes that collapse by key; and the `WF` premise is
  LOAD-BEARING there — without the registry's payload discipline,
  `Ast.decl .date (.nat 5) []` and `Ast.decl .date (.int 5) []` are
  two codes with one payload (`payload_inj_needs_wf`).
- **Ingestion** — LANDED (Slice B): `Ingest` is the door. `ingest`
  normalizes, decodes the revision-1 envelope, and gates on `Ast.wf`,
  with named refusals (`notASchema`/`illFormed`/`wrongRevision`/
  `nonEmptyReferences`/`unknownDeclaration`), soundness (`ingest_wf`)
  and exactness on the canonical image (`ingest_envelope`).
  `ingestLegacy` keeps the retired revision-0 spelling readable.
- **Custom declarations** — LANDED (increment C-decl, stipulation S3):
  `Declarations` is the ALLOWLIST as first-order data
  (`DeclarationId`, row zero `foldlab/cas/ref`), and `Ast.decl` is the
  general declaration code — a registry id, a first-order
  `DeclPayload`, and the type parameters, in Effect's persisted shape.
  Admission is BY CONSTRUCTION (`DeclarationId.General` is the carrier's
  index), the row's own discipline — payload shape, arity — is what
  `Ast.WF` reads off the registry, and `declOfRepresentation` is the
  single registry-driven gate every persisted `Declaration` passes
  through. Every revision-1 law extends arm-wise with its STATEMENT
  UNCHANGED, and `Ast.repNorm_decl`/`decl_wire_ne_casRef` say why: the
  general code cannot spell row zero, so it adds no second collapse.
  Named obligation, deliberately parked: the general declaration's
  DENOTATION. `El` of a `.decl` is `Empty` — the rows are admitted as
  CONTENT, and Lean has no carrier for their instances yet — so every
  value-plane law holds over the grown carrier vacuously rather than
  falsely, and the codec's own arms never fire. `Cas/Schema/El.lean`
  carries the design note: a typeclass cannot serve here (`El` consumes
  a runtime id), so the denotation wants a carrier table, as its own
  increment.
- **Union, stage 1 — carriage** — LANDED (increment C1, `UNION-DESIGN.md`,
  operator-ratified 2026-08-29): `Union` is the two modes as a registry
  table (`UnionMode`, wire spellings `anyOf`/`oneOf` verbatim), and
  `Ast.union` is the code — an ORDERED member list and the mode.
  **ORDER IS IDENTITY**: members are never sorted, never flattened,
  never deduplicated, so `union [a, b]` and `union [b, a]` are two
  codes at two addresses. `WF` asks for nonemptiness and well-formed
  members and nothing about the order (`union_nil_not_wf` states the
  empty union's refusal — that is `Never`'s job, and `Never` is not
  admitted). Every revision-1 law extends arm-wise with its STATEMENT
  UNCHANGED, and `Ast.repNorm_union` says why: the normal form rewrites
  the members positionwise and leaves mode, count, and order alone, so
  no third collapse is owed.
- **Union, stage 2 — denotation, discriminated first** — LANDED
  (`UNION-DESIGN.md`, joined with the deriving growth as ratified):
  `Discriminated` is Effect's sentinel property as first-order data
  (`discriminatedB`/`Discriminated`/`discriminatedB_iff`, the house
  wf-idiom), and `El (.union ms m)` is `ElMembers ms` — the iterated
  member sum — when the members are discriminated and `Empty` when they
  are not. That guard is what keeps every stage-1 law TRUE over the
  grown carrier rather than merely unchanged: an undiscriminated union
  still denotes nothing, so its value-plane arms stay vacuous, while a
  discriminated one gets tag dispatch (`encodeMembers`/`decodeMembers`)
  whose forward law is a THEOREM because distinct `_tag` literals make
  the members' images disjoint (`decode_head_encodeMembers_tail`).
  Discrimination is deliberately NOT part of `Ast.WF`: `WF` is the
  store's admission discipline and stage 1 already admits every union,
  the pathological ones included. `deriving Described` grows the same
  slice: a non-recursive, non-mutual, parameter-free inductive derives
  as `Ast.union […] .oneOf` of per-constructor tagged structs, with
  members ordered by tag (the ONE spelling a generator may pick — D1)
  and `<T>.schemaDiscriminated` emitted beside the instance as the
  proof that the code is discriminated. `cas_union` is the authoring
  notation. Named obligation, deliberately parked: the GENERAL union's
  denotation — the try-order dependent sum for undiscriminated members,
  owed only when a consumer demands it (`Cas/Schema/El.lean` carries
  the note). Stage 3, `oneOf` uniqueness as a checkable property,
  belongs to the validation-gen lane and owes a statement only when a
  gate consumes it.
- **Enum** — LANDED (increment C4): `Ast.enum` is Effect's `Enum` as
  content — an ORDERED list of `(name, value)` members over `EnumValue`,
  the two value rows Effect can persist (string, number) and no others.
  **ORDER IS IDENTITY** here for a reason visible in Effect's own
  constructor: `Schema.Enum` reads its members as `Object.keys` order
  (`Schema.ts:3021-3030`), which for a TypeScript enum is SOURCE order,
  and the wire carries them as a positional array rather than a keyed
  record, so no canonical rendering has anything to say about their
  arrangement. `WF` asks for nonemptiness and pairwise-distinct member
  NAMES (`enum_nil_not_wf`, `enum_names_nodup`) and deliberately NOT for
  distinct values: TypeScript spells alias members, Effect persists
  them, and refusing them here would retire content the source language
  has. Every revision-1 law extends arm-wise with its STATEMENT
  UNCHANGED, and `Ast.repNorm_enum` says why nothing more is owed: the
  enum carries no sub-code, so it is a FIXED POINT of the normal form
  and adds no collapse at all. Named obligation, deliberately parked:
  the enum's DENOTATION. `El` of an `.enum` is `Empty`, because under
  aliasing the index a value carries would be a function of member ORDER
  rather than of the value — the general union's pathology exactly, and
  it takes the same staged answer (`Cas/Schema/El.lean`, obligation
  `enumEl`).
- **Arrays completion — tuples** — LANDED (increment C2): `Ast.tuple` is
  Effect's `Arrays` node in its POSITIONAL form — a first element, the
  rest of the elements, and an optional rest type — each element
  carrying its own optionality bit, exactly the persisted shape.
  Two calls the carrier makes STRUCTURAL rather than clausal, and each
  is why a law did not have to move. Growing `.arr` would have been an
  ARITY change to a landed code, so the increment is ADDITIVE: `.arr`
  keeps its meaning and its bytes. And the tuple's element list is
  nonempty BY CONSTRUCTION, because `{elements:[], rest:[t]}` is already
  `.arr t`'s representation — a tuple able to spell it would be a SECOND
  two-to-one map from codes to representations, and
  `toRepresentationJson_inj`, which holds unconditionally up to the one
  literal-null collapse, would become false as stated
  (`Ast.repNorm_tuple` says what the normal form does instead: element
  types positionwise, the rest type, and nothing else). The rest is an
  `Option`, so "at most one rest type" is structural too, and the
  trailing-rest semantics the admission map defers are refused by shape.
  What stays out: `Schema.Tuple([])`, the empty tuple, has no spelling —
  it had none before this increment either, so nothing is retired.
  Named obligation, deliberately parked: the tuple's DENOTATION. `El` of
  a `.tuple` is `Empty`, because an absent optional element SHORTENS a
  JSON array rather than leaving a hole in it, so a non-trailing optional
  has no positional encoding at all and the round trip would be false on
  a code `WF` admits. That is the general union's situation exactly and
  takes the ratified answer — a boolean guard in `El`, not a new clause
  in `WF` (`Cas/Schema/El.lean`, obligation `tupleEl`).
- **Projection — a described VALUE to a store node** — LANDED
  (`Projection`): the path `El a → RValue → (payload, refs) → Node`,
  which is what makes a described kind PUTTABLE from Lean rather than
  only mintable. Before it, the `$link` sentinel and the typed-DAG
  layer's `RValue` never met, and every reification target was a
  generator Lean could not drive. `elR` is `encode` with exactly one
  arm changed — `.ref` yields a LINK, not a sentinel — and
  `eraseR_elR` proves the bridge factors through the ratified
  projection, so it cannot fork the wire shape. `project` renders the
  runtime's own `{revision, value}` envelope; the scheme VERSION byte
  is a parameter, because a value node's version is the store's fact
  and this plane has never reached across to the grammar's. The
  forced-index law comes for free from `Cas.markerScan_lower` and is
  restated at this grain (`project_wellRefIndexed`, `project_refs`) so
  no projection has to guard it per kind. Named obligation: the READ
  path — `Node → RValue → El a`, needing an inverse to `lower` this
  model does not yet carry (`Cas/Schema/Projection.lean` states its
  signature and what it owes).
-/
