# Schema cutover ruling

Status: frozen design input, 2026-09-02. The structural lane is closed.
`generated/schema-structural-assurance.tsv` joins the six tag declarations,
the payload carrier, the recursive field-admission judgment, the general
recursor, the optic and annotation-data laws, and the effectful-field
marker, admission, program equations, and host harness, and records
`SCHEMA-PG-REPRESENTATION-TAG`, `SCHEMA-PG-PAYLOAD`,
`SCHEMA-PG-FIELD-ADMISSION`, `DATA-PG-OPTIC`, `SCHEMA-PG-ANNOTATION-DATA`,
and `SCHEMA-PG-EFFECTFUL-FIELD` as `required-closed` (`:2675-2680`). Cutover remains open for the denotation,
getter, transformation, codec, registry, host-reviver, wire, and CAS
compatibility lanes; the projection's own open rows are `SCHEMA-PG-DOCUMENT`
reference semantics and `SCHEMA-PG-WIRE` codec and canonicalization
(`:2681-2682`). The rulings below are unchanged.

## Decision

Effect4 will not extract Foldlab's `Cas.Schema.Ast`, `Cas.Schema.El`, or pure
`Cas.Schema.Codec` as its Schema foundation. Effect4 will own one portable,
first-order representation family modeled on Effect's persisted
`SchemaRepresentation.Document`, one document-relative relational
interpretation, and one directional four-index codec calculus. Its proof-level
Getter semantics reuse the existing `Signature` and `Program`; a later,
separate face reifies the admitted first-order fragment as `CheckedFlow` and
elaborates it back to that proof semantics.

Foldlab retains its CAS envelope, profile, identities, canonical bytes,
content addresses, store operations, and `IngestRefusal`. Its current Schema
types become checked profile or compatibility views. A Foldlab type may be
retired only after its own embedding, retraction, semantic agreement, refusal
mapping, and byte-compatibility edges close.

This ruling prevents duplicate carriers:

- Effect's runtime `SchemaAST.AST` is not persisted Schema content because its
  declarations and checks contain executable functions.
- Foldlab's `Ast` is an admitted CAS subset, not the full Effect surface.
- A partial function `Representation -> Type` is not the denotation; several
  existing cases currently map to `Empty` because their meaning depends on a
  document, registry, or relational choice.
- Schema introduces no additional type-code or service-code carrier beside the
  existing effect algebra. Decoded and encoded values are indexed by ordinary
  Lean types; service operations and their answer types are already expressed
  by `Signature.Op` and `Signature.Answer`.

## Exact authority state

| Authority | Pin or digest | Use |
| --- | --- | --- |
| Foldlab source | `feb29321fd50204aa338209d313e84a3f8b71c66` | downstream compatibility authority |
| Foldlab Schema tree | Git tree `169e05310b4f21550b0644455d730d50165ea8ec`; recursive listing SHA-256 `dbd9960b85b633ce30876f003f9b33098f10fe39b24c73cd0bacb8f6c9877795` | extraction boundary |
| `CanonicalSchema.ts` | Git blob `ceadbb1a75eb61d92e7c09f3d99c5aea917b0ee4`; SHA-256 `aa3911009d8d21d3b654ccd441a8899ccb7f6ba3aeb5c03c1daaad919e591d6a` | downstream bridge evidence, never Effect4 semantic authority |
| Effect semantic revision | `2600f62f4532026928454dcea8d1c48557b3f942` | source-level rc.112 model |
| resolved package | `effect@4.0.0-rc.112`; integrity `sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==` | exact host bytes to exercise |

The semantic revision and resolved package are separate pins. They must not be
described as byte-identical. In particular:

| File | upstream SHA-256 | installed SHA-256 | Ruling |
| --- | --- | --- | --- |
| `Schema.ts` | `f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f` | `9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784` | different bytes; inspected core signatures agree, but direct package tests remain required |
| `SchemaRepresentation.ts` | `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc` | same | byte match |
| `SchemaAST.ts` | `7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8` | same | byte match |
| `SchemaTransformation.ts` | `4050859c4d340b3580c5e58aceeb9984339eed1dfadb1a2e86f18a9c0ac110f5` | same | byte match |
| `SchemaParser.ts` | `492dfbb294e24b2f3ebd949abbb9ba73cc19a71b4c35f290fd0137d52f8aaaaa` | same | byte match |
| `SchemaIssue.ts` | `b4cb0ada18aef01083f9179dd827fb46aea4c625c2c63308d43cae5d3a86328e` | same | byte match |
| `SchemaGetter.ts` | `a2f2c85c41eceb1e8092ca15fd6ded1ac90c23a4c44be610200d3feefe1d6682` | same | byte match |
| `internal/schema/toRepresentation.ts` | not asserted | `677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2` | independently pinned installed-package evidence; not an upstream byte-match claim |
| `internal/schema/fromRepresentation.ts` | not asserted | `0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e` | independently pinned installed-package evidence; not an upstream byte-match claim |
| `internal/schema/annotations.ts` | not asserted | `4b3bedcae279fcb3a1dff4e8eb718d42f450d59c8b45912070a586adcdcb077c` | independently pinned installed-package evidence; not an upstream byte-match claim |

Installed declaration digests are also pinned independently:

```text
Schema.d.ts                347a8f933474b506ca5d82d2478626a25a8d8f09d620424a3eb223c6617e68f9
SchemaRepresentation.d.ts  5df3b47d63b3494faca11ead725e50dfaed5ed5e52b35af20bcf2a05b9c1e91b
SchemaTransformation.d.ts  867a31347e0bae4e4750f0e3ce1e14323606182f6cafa78469266c2b02b8ec6f
SchemaAST.d.ts             0022045f8023e1b5df96171419f72c5eb6ebde92b0c91a9d997527fe0eca377
```

Primary source anchors are the pinned Effect files
[`SchemaRepresentation.ts`](https://github.com/Effect-TS/effect/blob/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src/SchemaRepresentation.ts),
[`Schema.ts`](https://github.com/Effect-TS/effect/blob/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src/Schema.ts),
[`SchemaGetter.ts`](https://github.com/Effect-TS/effect/blob/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src/SchemaGetter.ts), and
[`SchemaTransformation.ts`](https://github.com/Effect-TS/effect/blob/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src/SchemaTransformation.ts).

## Five distinct layers

### 1. Structural representation

`Effect4.Schema.Representation` is small, first-order data. It includes the
complete rc.112 persisted alphabet:

```text
Declaration Reference Suspend Null Undefined Void Never Unknown Any String
Number Boolean BigInt Symbol Literal UniqueSymbol ObjectKeyword Enum
TemplateLiteral Arrays Objects Union
```

`Check`, persisted annotations, references, `Document`, and `MultiDocument`
belong to the same structural layer. The carrier contains no `Lean.Expr`, Lean
continuation, JavaScript function, promise, runtime object, or reviver closure.

Declarations and checks carry open stable identifiers. Closedness is evidence
from a checked registry or target profile; it is not a new constructor family.
Foldlab's `.ref` is therefore profile sugar for a `foldlab/cas/ref` declaration
row, not a second representation node.

Raw, admitted, and canonical forms are one carrier plus checked evidence:

```text
Representation
Checked profile Representation
Canonical wire Representation
```

#### When a standalone proof graph is required

A public type needs its own `proofGraphId` when it owns a nonlocal obligation:
a source or downstream cutover boundary, checked construction or rejection,
denotational or operational meaning, a claimed algebraic law that is not a
finite local case split, a bridge or compatibility theorem, target lowering,
a host boundary, or a nontrivial invariant or trust admission. Those edges can
change independently and must remain visible as a graph.

A `leafReceipt` record is sufficient only for a closed finite helper alphabet
whose evidence is local to its declaration: exact constructors, census and
duplicate freedom, local spelling laws where a spelling is pinned, registered
counterexamples, and an axiom receipt. A leaf may have no independent
admission, denotation, bridge, target, compatibility, or host meaning. Its
source and cross-type edges must be explicit in a named parent graph. “Leaf”
therefore means one compact closure record, not no evidence.

The exact declaration rows are authoritative in `PORT-MANIFEST.md`.
`Effect4.RepresentationTag` receives
`proofGraphId = SCHEMA-PG-REPRESENTATION-TAG` because it is the source-facing
Schema tag cutover boundary. `Effect4.UnionMode`, `Effect4.CheckTag`,
`Effect4.LiteralKind`, `Effect4.EnumValueKind`, and
`Effect4.PropertyKeyKind` receive named `leafReceipt`, theorem-receipt, and evidence
IDs under that parent, with no standalone graph. The parent graph owns
`SCHEMA-REL-ENUM-TO-LITERAL-KIND`: an injective **kind-level** relation and an
explicit separation from the total injective raw value embedding and from the
D7 field-admission judgment. The kind relation alone decides neither value
admission nor persistence. If a leaf later gains a nonlocal obligation, its
disposition must be promoted before that declaration changes.

#### Frozen rc.112 persisted census

The source census is the following exact, case-sensitive 22-tag set. It is a
membership census, not a claim that this source order is parser precedence:

| # | Tag | Persisted fields beyond `_tag` |
| ---: | --- | --- |
| 1 | `Declaration` | required `representation`; optional persisted `annotations`; ordered `typeParameters`; ordered `checks` |
| 2 | `Reference` | non-empty `$ref` |
| 3 | `Suspend` | optional persisted `annotations`; exactly empty `checks`; `thunk` |
| 4 | `Null` | optional persisted `annotations`; ordered `checks` |
| 5 | `Undefined` | optional persisted `annotations`; ordered `checks` |
| 6 | `Void` | optional persisted `annotations`; ordered `checks` |
| 7 | `Never` | optional persisted `annotations`; ordered `checks` |
| 8 | `Unknown` | optional persisted `annotations`; ordered `checks` |
| 9 | `Any` | optional persisted `annotations`; ordered `checks` |
| 10 | `String` | optional persisted `annotations`; ordered `checks` |
| 11 | `Number` | optional persisted `annotations`; ordered `checks` |
| 12 | `Boolean` | optional persisted `annotations`; ordered `checks` |
| 13 | `BigInt` | optional persisted `annotations`; ordered `checks` |
| 14 | `Symbol` | optional persisted `annotations`; ordered `checks` |
| 15 | `Literal` | keyword fields plus one tagged string, finite-number, bigint, or boolean literal; never `null` |
| 16 | `UniqueSymbol` | keyword fields plus a persistable global symbol |
| 17 | `ObjectKeyword` | optional persisted `annotations`; ordered `checks` |
| 18 | `Enum` | keyword fields plus ordered `[name, value]` entries; values are tagged strings or numbers and aliases are permitted |
| 19 | `TemplateLiteral` | keyword fields plus ordered `parts` |
| 20 | `Arrays` | keyword fields plus ordered `elements` and arbitrary ordered `rest` representations |
| 21 | `Objects` | keyword fields plus property-signature and index-signature collections |
| 22 | `Union` | keyword fields plus ordered `types` and mode `anyOf` or `oneOf` |

These cross-tag persisted field constraints are frozen with the census:

- A representation annotation is a non-empty stable `id` plus JSON `payload`.
  `Declaration.representation` is optional in the live interface but required
  by the persisted rc.112 codec.
- `Check` is exactly `Filter | FilterGroup`. A persisted `Filter` has a
  required representation annotation (optionally with ordered referenced
  schemas), optional persisted annotations, and `aborted : Bool`.
  `FilterGroup.representation` is optional and its ordered `checks` are
  non-empty.
- Persisted annotations contain only JSON-valued entries; unsupported entries
  are pruned and an empty result is omitted.
- The `number` spelling does not denote one numeric domain. The `Literal`
  number leg is `Schema.Finite` (`SchemaRepresentation.ts:1005`), while the
  `Enum` and property-name number legs are `Schema.Number` (`:999`, used at
  `:1020` and `:1042`). A non-finite number is a legal enum value and a legal
  property key, and is not a legal literal. See `E4-SCHEMA-CE-023`.
- An array element records `isOptional`, its representation, and optional
  persisted annotations. Both `elements` and `rest` are arrays; the model must
  not collapse `rest` to a single optional node.
- An object property records a string, number, or global-symbol key, its
  representation, `isOptional`, `isMutable`, and optional persisted
  annotations. An index signature records a parameter representation and a
  value representation. Local symbols are live-only and fail portable
  lowering.
- A `Document` has one root representation and a keyed references table. A
  `MultiDocument` has a non-empty ordered root list and the same kind of keyed
  references table. Duplicate JSON keys are rejected before either table is
  constructed.
- Non-emptiness constrains the **pointer, not the key**. `Reference.$ref` is a
  non-empty string while the references-table key type is plain `String`. An
  empty `$ref` is refused by rc.112 itself; an empty table key is not.
- A non-empty references table does **not** mean the document is recursive. A
  shared non-recursive name allocates a table entry with no `Suspend` node
  anywhere. No admission rule may infer recursion from table non-emptiness.
- Union members, tuple `elements`/`rest`, checks, enum entries, index
  signatures, reference occurrences, and multi-document roots retain order.
  Object property declaration order is normalized as a keyed structural
  collection only after representation admission establishes unique property
  keys. References-table entry order is likewise not semantic after raw JSON
  duplicate-key rejection. Any theorem about operational issue order is a
  separate parsing theorem.

#### Verified persisted-field snapshot

The field constraints above were frozen from the source census by reading the
pinned bytes (`SchemaRepresentation.ts`, SHA-256
`a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`).

Two claims are made here and they have different strength. **Field content** —
the field names, their order within each codec, requiredness, and the codec
constructor each field is given — was read off the pinned bytes and has since
been re-derived independently. **Line numbers** are a navigation aid whose
citations were re-derived, one binding at a time, on 2026-08-31, after eight of
the twenty-three were found wrong; see the fired finding below. Neither claim is
mechanically checked: no script in this repository compares this block against
the pin, so a later edit to either column can drift silently.

This is pinned source-reading evidence for the cited field names and codec
shapes. It is not a Lean theorem, a decoder result, or a claim of semantic
faithfulness for the future carrier.

The exact persisted field names and codecs are pinned below so the payload
packet implements names rather than paraphrases. Line numbers are in the
pinned file.

```text
RepresentationAnnotation      :917  { id : NonEmptyString, payload : Json }
CheckRepresentationAnnotation :922  RepresentationAnnotation + schemas? : Representation[]
Annotations                   :939  optional Record(String, Unknown)
                                     encoded as optionalKey(JsonObject), pruned
KeywordFields                 :952  { annotations, checks }

Filter        :956  { _tag, representation (REQUIRED), annotations, aborted : Boolean }
FilterGroup   :962  { _tag, representation?, annotations, checks : NonEmptyArray }

Declaration   :977  { _tag, representation (REQUIRED), annotations,
                      typeParameters : Representation[], checks }
Suspend       :984  { _tag, annotations, checks : Tuple([]), thunk : Representation }
Reference    :1066  { _tag, $ref : NonEmptyString }
Literal      :1000  KeywordFields + literal : String | Finite | BigInt | Boolean
UniqueSymbol :1010  KeywordFields + symbol : Symbol
Enum         :1015  KeywordFields + enums : Array(Tuple([String, String | Number]))
TemplateLit  :1023  KeywordFields + parts : Representation[]
Element      :1028  { isOptional : Boolean, type : Representation, annotations }
Arrays       :1033  KeywordFields + elements : Array(Element), rest : Representation[]
PropertySig  :1039  { name : String | Number | Symbol, type, isOptional, isMutable,
                      annotations }
IndexSig     :1050  { parameter : Representation, type : Representation }
Objects      :1054  KeywordFields + propertySignatures, indexSignatures
Union        :1060  KeywordFields + types : Representation[], mode : "anyOf" | "oneOf"
keyword tags  :970  { _tag } + KeywordFields          -- 12 tags share this shape

References   :1096  Record(String, Representation)
Document     :1098  { representation : Representation, references : References }
MultiDocument:1105  { representations : NonEmptyArray, references : References }
```

Each number is the line of the **binding that introduces the named codec** —
`const <Name>Schema = Schema.Struct({`, or the `function` line for
`makeKeywordSchema`. Field lines follow it. `Document` and `MultiDocument`
name `DocumentFromJson` (`:1098`) and `MultiDocumentFromJson` (`:1105`); their
`Schema.Struct` field bodies are at `:1099-1102` and `:1106-1109`.

Six facts a paraphrase of the table would lose, all pinned:

1. `Reference` is the only representation with **no** `annotations` and **no**
   `checks`. It is exactly `_tag` and `$ref`.
2. `Filter` has **no** direct `checks` field, but it is not a leaf. Checks have
   two recursive field forms and three constructor routes:
   `Filter.representation.schemas`, optional
   `FilterGroup.representation.schemas`, and `FilterGroup.checks`. Field
   admission and traversal must enumerate all three.
3. `Declaration.representation` and `Filter.representation` are **required in
   the codec** while the live TypeScript interfaces mark them optional. A
   model that reads optionality off the interfaces admits two document shapes
   rc.112 rejects.
4. `IndexSignature` carries **no** annotations — it is exactly `parameter` and
   `type`. Array elements and property signatures do carry them.
5. `MultiDocument`'s root field is named `representations` (plural), not
   `representation`. The two document shapes are not distinguished by a tag.
6. Numeric data occurs in four source positions with directional policies:
   `Literal` uses `Finite`; `Enum` and property names use `Number` and encode
   non-finites through three string escapes; representation/check annotation
   payloads are retained JSON and reject non-finite leaves on decode; retained
   ordinary annotation bags have the same decode-side finite-JSON condition,
   while encode from wider live values prunes unsupported entries. See
   `E4-SCHEMA-CE-023` and `E4-SCHEMA-CE-028`.

`Element` and `PropertySignature` name the child field `type`, not
`representation`. `Suspend` names it `thunk`, and it is a nested
`Representation` — no closure is persisted.

This snapshot is evidence for `SC-REP-01`. It does not by itself close that
row: the row also requires the Lean declaration and its admission theorems.

### 2. Dependent interpretation

Schema introduces no type-code or service-code universe. A decoded index `T`
and encoded index `E` are ordinary Lean types in the existing algebra's answer
universe. When meaning requires services, choose an existing `S : Signature`;
its operation family is `S.Op` and the answer to an operation is
`S.Answer op`.
The required finite subset is a canonical `Effect4.Data.Row S.Op`; Context may
interpret that row against an environment, but it does not own a second row
carrier or row union.

Meaning is given by document-relative judgments, not by a partial closed type
function or an `El` field:

```text
Gamma |- representation represents T
Gamma |- representation accepts value
rho |- codec.decode encodedValue ⇓ outcome
rho |- codec.encode decodedValue ⇓ outcome
```

`Gamma` owns document references and registry evidence. `Accepts` is
relational: overlapping unions, enum aliases, recursive references, and
declarations are not faithfully modeled by one total function.

### 3. Directional transformations

Schema defines no effect monad and no free-program carrier. It has two related
program faces, in this order:

1. **Proof semantics.** Before full Flow semantics closes, a Getter can denote
   a function of the Effect shape
   `Option E × ParseOptions → Effect (Option T) Issue R` using the existing
   `Program`. Its Lean semantic shape is
   `Option E × ParseOptions → Program (SchemaIssueSig ⊕ₛ S) (Option T)`, where
   services use `S.Op`/`S.Answer`, `SchemaIssueSig.Answer _ = Empty`, and
   `R : Data.Row S.Op` plus an operation-membership judgment certifies the
   permitted service operations. This higher-order function is a proof carrier
   and is not serialized as canonical program content.
2. **First-order reification.** After checked Flow has its relational
   semantics, the admitted Getter language stores blocks as `CheckedFlow`.
   Elaboration interprets that checked graph into the proof-level Getter
   semantics. The inverse is required only for the selected generated Getter
   syntax; Effect4 does not claim to serialize an arbitrary Lean function or
   arbitrary `Program` continuation.

The public indices are:

```text
Getter         decoded encoded requirements
Transformation decoded encoded decodeRequirements encodeRequirements
Codec          decoded encoded decodeRequirements encodeRequirements
```

A getter denotes the shape above from an optional encoded value and explicit
parse options to an optional decoded value. Its operation signature includes
typed service lookup and schema issue exit; first the semantic function is a
`Program` interpretation, and later its canonical stored content is a checked
first-order Flow.

A transformation is a directional pair:

```text
decode : Getter decoded encoded decodeRequirements
encode : Getter encoded decoded encodeRequirements
```

Composition reverses the encoding path:

```text
(f then g).decode = f.decode then g.decode
(f then g).encode = g.encode then f.encode
```

Required transformation laws are `flip (flip t) = t`, reversal of composition
under `flip`, left and right identity, and associativity at the relational
big-step observation. Structural equality is not promised before a canonical
graph normalizer exists.

For `from : Codec FT FE FRD FRE`, `to : Codec TT TE TRD TRE`, and a link
`Transformation TE FT RD RE`, `decodeTo to link from` has:

```text
decoded            = TT
encoded            = FE
decodeRequirements = TRD union FRD union RD
encodeRequirements = TRE union FRE union RE
```

The decode path is `FE -> FT -> TE -> TT`; the encode path is
`TT -> TE -> FT -> FE`. Requirement rows and their normalization/union laws
come solely from `Effect4.Data.Row`. Context owns key interpretation and
environments, not the row carrier. Empty requirements lower to TypeScript
`never`; row union lowers to a TypeScript union.

Effect's erased convenience views do not become additional carriers:

```text
Schema T     = exists E RD RE, Codec T E RD RE
Decoder T RD = exists E RE, Codec T E RD RE
Encoder E RE = exists T RD, Codec T E RD RE
Top          = exists T E RD RE, Codec T E RD RE
```

Whole-pipeline middleware remains a handler/program transformation. It is not
a value getter. Arbitrary JavaScript middleware remains a registered host
boundary.

### 4. Host revivers

Lean owns first-order `ReviverKind`, `ReviverId`, `ReviverSpec`, declaration
and check specifications, and the registry. A specification records stable
identity, payload representation, referenced-schema contract, arity, and
result classification; it stores no function.

The host harness must show finite registry coverage:

```text
every admitted row has exactly one host reviver
no host reviver exists without an admitted row
reviver IDs are unique
payload decoding agrees with the generated contract
```

These are host conformance results. They do not prove that an arbitrary
JavaScript callback implements its informal intention.

### 5. Canonical wire profile

The stable `Effect4Rc112` profile identity belongs to
`Effect4.Protocol.Profile`, and generic profile membership and admission policy
belong to `Effect4.Protocol.Admission`. The future Schema wire adapter under
that identity owns the 22-tag JSON shape, document envelopes, annotation
pruning, global-symbol encoding, normalization, source coverage, and wire
round trips. `Effect4.Schema.Check` owns Schema-specific structural predicates.
No issue or diagnostic API is precommitted merely because a predicate can
fail; a later public classification boundary needs its own contract.
`Schema.Check` does not own `SC-PROFILE` identity or mint a second profile carrier. None of these
owners absorbs Foldlab's schema kind, revision, content address, node bytes, or
store operations.

Raw JSON must preserve ordered duplicate keys until the profile rejects them.
A map-only parser such as a final `Lean.Json` value cannot be the sole byte
door because it has already discarded the evidence required by that refusal.

Required wire results are:

```text
decode (encode canonicalDocument) = canonicalDocument
encode (decode acceptedBytes) = canonicalize acceptedBytes
normalization is idempotent
canonical encoding is injective on canonical documents
the decoder accepts only source-census tags
duplicate keys are rejected before map construction
```

`normalization_preserves_denotation` remains an open obligation. It is not a
well-formed theorem statement until the document-relative denotation judgment
and its observations are frozen. Normalization may be implemented and proved
idempotent first, but no semantic-preservation claim follows from that result.

## Operational semantic rulings

- `anyOf` retains member order and operationally chooses the first successful
  member.
- `oneOf` succeeds exactly when one member succeeds; multiple successful
  members are an issue.
- Enum aliases induce a many-to-one relation and can defeat encoding
  injectivity.
- References are interpreted relative to the enclosing `Document`.
- Recursive meaning is an inductive or fixed-point judgment over the
  document, not a closed recursive `El` definition.
- Executable decoding is proved sound against `Accepts`; completeness is
  claimed only for an explicitly checked profile.
- `ParseOptions` are first-order inputs. Error collection, excess-property
  policy, property order, check disabling, concurrency, and input reporting
  remain observable. Concurrency is interpreted by the scheduler/decision
  semantics.
- Fixed-fuel execution is evidence only. Codec meaning and composition live at
  the relational big-step or interpreter face.
- Local symbols and non-JSON annotations are not assigned invented portable
  identities. A local symbol fails lowering; unsupported annotations are
  pruned according to the versioned profile.

## Codec law classification

No universal round-trip law is attached to `Codec`; lossy transforms such as
trimming directly refute it. Each codec records independent proof status for:

```text
decode soundness             encode soundness
decode completeness          encode completeness
left inverse                 right inverse
decode normalization         encode normalization
lossless equivalence         fixed-decision determinism
totality
```

Foldlab's existing `Described` corresponds only to the strongest service-free,
lossless-equivalence class. It is not the native codec carrier.

There is therefore no Effect4 `Described` instance at the raw-authoring or
TypeScript-generation layer. Such an instance becomes meaningful only after a
native denotation and both inverse laws close; until then, the existing
`Representation`, `Document`, and `Codec` families remain the only carriers.

## Refusal and failure ownership

The following are distinct and must not share a constructor merely because all
can stop execution:

| Kind | Owner | Meaning |
| --- | --- | --- |
| Schema issue | Effect4 Schema calculus | typed decode or encode failure |
| wire issue | versioned wire profile | malformed or noncanonical raw representation |
| profile issue | checked profile | structurally valid representation outside an admitted subset |
| Foldlab `IngestRefusal` | Foldlab | downstream CAS door result |
| cutover refusal | Effect4 audit | organizational/proof-closure status, never runtime meaning |
| Cause/Exit | general effect semantics | typed failure, defect, interruption, and combined exits |
| live frontier | flow semantics | execution requires more decisions or steps; not an error or refusal |

Foldlab currently has six, not five, Schema ingest refusal constructors:
`notASchema`, `illFormed`, `wrongRevision`, `nonEmptyReferences`,
`unguardedCycle`, and `unknownDeclaration`. Effect4 does not duplicate them.

`¬ FieldAdmissible value` is a failed structural predicate, not a refusal
value. A later checked boundary may classify that failure as a profile issue,
but the issue carrier and its scan order are separate declarations.
Property-key uniqueness is a future Effect4 profile narrowing, deferred until
the key-equivalence relation decides `+0`/`-0` and NaN payload cases.
Reference-key uniqueness for both `Document` and `MultiDocument` is instead a
future `Protocol.Bytes` raw-wire condition, before either references table is
constructed. Host `SchemaError` and `RangeError` results remain observations
of named host calls and do not become Effect4 refusal constructors.
Unknown-profile behavior belongs to `Protocol.Admission`; a profile identity
is passive data.

## Proof graph

This is the category graph for nonlocal Schema obligations, not a demand for
one standalone graph per finite helper enum or record. The allocation is
conditional and explicit:

- `SCHEMA-PG-REPRESENTATION-TAG` exists because exact tag coverage is itself a
  cutover condition. Its five passive auxiliary alphabets attach as leaf
  receipts.
- `SCHEMA-PG-PAYLOAD` owns the mutually recursive `Representation`/`Check`
  family, its exact constructor coverage, tag projection, and structural
  equality. Passive wrappers, nonrecursive scalar sums, and plain record
  children attach as leaf receipts. Recursive JSON finiteness is a node in
  this graph, not a new standalone graph.
- `SCHEMA-PG-FIELD-ADMISSION` owns the recursive persisted/decode-side field
  predicate, including finite retained annotation bags. It is required because
  this judgment decides a structural condition and recurses through the
  payload. Property-key uniqueness is not yet a node.
- `DATA-PG-OPTIC` owns the nontrivial higher-order composition and conversion
  laws for `Lens`, `Optional`, and `Traversal`. Carrier projections and direct
  field lenses remain local receipts.
- `SCHEMA-PG-ANNOTATION-DATA` owns exact typed-key reconstruction and the
  exhaustive recursive annotation walk through representations, checks, and
  documents. It reuses the existing Schema carriers and closed recursor.
- `SCHEMA-PG-EFFECTFUL-FIELD` owns exact raw marker admission, resolution
  against one closed signature, generated read/write/modify programs, and the
  corresponding big-step interpreter equations. It introduces no new effect
  or optic carrier.
- `SCHEMA-PG-DOCUMENT` owns reference interpretation, reachability,
  guardedness, and productivity. The plain `Document` and `MultiDocument`
  record declarations are leaves until those meanings are attached.
- `SCHEMA-PG-WIRE` owns duplicate-preserving raw data, decoding,
  canonicalization, and encoding. Finite host fixtures attach as receipts;
  they do not receive graphs.
- `TS-PG-SCHEMA-DOCUMENT-GENERATION` owns the recursive bridge from those
  existing raw carriers to checked TypeScript module generation and the exact
  host harness. Higher-order predicate combinators and raw constructor helpers
  attach equations to existing Schema graphs; they do not receive a graph.
- A versioned profile identity is passive data and receives a leaf receipt.
  `Protocol.Admission` crosses the graph threshold when it classifies an
  unknown profile or an out-of-profile value.

Empty breadth stubs receive neither a graph nor a leaf receipt. Every graph
node below is required unless a later contract explicitly marks it outside a
selected profile. An asserted status cannot close an edge, and a local leaf
receipt cannot close a denotation, bridge, target, or host edge.

```text
SCHEMA-PG-REPRESENTATION-TAG
  -> SCHEMA-LEAF-UNION-MODE
  -> SCHEMA-LEAF-CHECK-TAG
  -> SCHEMA-LEAF-LITERAL-KIND
  -> SCHEMA-LEAF-ENUM-VALUE-KIND
  -> SCHEMA-LEAF-PROPERTY-KEY-KIND
  -> SCHEMA-REL-ENUM-TO-LITERAL-KIND

SCHEMA-PG-PAYLOAD
  -> SCHEMA-LEAF-FLOAT64-BITS
  -> SCHEMA-NODE-JSON-FINITENESS
  -> SCHEMA-LEAF-PAYLOAD-SCALARS
  -> SCHEMA-LEAF-PAYLOAD-RECORDS
  -> SC-REP-01 payload declaration and constructor coverage
  -> SC-REP-03 structural equality, elimination, and tag projection

SCHEMA-PG-FIELD-ADMISSION
  -> SC-REP-04 recursive field admission matches the frozen rc.112 constraints

DATA-PG-OPTIC
  -> lawful Lens and Optional composition
  -> lawful Lens-to-Optional and Optional-to-Traversal conversion
  -> lawful Traversal composition

SCHEMA-PG-ANNOTATION-DATA
  -> exact typed AnnotationKey reconstruction
  -> ordered raw and typed annotation traversal
  -> exhaustive Representation and Check traversal
  -> structural Document and MultiDocument traversal
  -> E4-SCHEMA-CE-044 through E4-SCHEMA-CE-048
  -> TypeScript, Effect runtime, and Effect language-service host gate

SCHEMA-PG-EFFECTFUL-FIELD
  -> exact first-order marker codec
  -> exact raw occurrence admission
  -> closed alphabet and operation identity agreement
  -> generated get, set, and modify Program equations
  -> interpreter preservation at interpret
  -> E4-SCHEMA-CE-049 through E4-SCHEMA-CE-052

SC-SRC-01 exact upstream and resolved-package pins
SC-SRC-02 generated 22-tag source census
  -> SCHEMA-PG-REPRESENTATION-TAG
  -> SCHEMA-PG-PAYLOAD
  -> SC-REP-02 tag Nodup and source completeness
  -> SC-REP-CENSUS-PIN census re-derived from the pinned rc.112 bytes

SCHEMA-PG-WIRE
  -> SC-WIRE-REFERENCE-KEY-UNIQUE for Document and MultiDocument
  -> SC-WIRE-01 duplicate-preserving raw JSON
  -> SC-WIRE-02 decoder soundness
  -> SC-WIRE-03 encoder/decoder round trip
  -> SC-WIRE-04 canonicalization idempotence
  -> SC-WIRE-05 canonical encoding injectivity

SC-REP
  -> SC-PROFILE-01 total classifier on all tags
  -> SC-PROFILE-02 Boolean classifier iff propositional admission
  -> SC-PROFILE-03 source-census exhaustiveness

SCHEMA-PG-DOCUMENT
  -> SC-DOC-01 reference graph
  -> SC-DOC-02 guarded checker soundness
  -> SC-DOC-03 guarded checker completeness
  -> SC-DOC-04 memoized checker equivalence
  -> SC-DOC-05 retained complexity counterexample
  -> SC-DOC-06 productivity is not guardedness [OPEN]
  -> SC-DOC-07 canonical emission order for unions [OPEN]

TS-PG-SCHEMA-DOCUMENT-GENERATION
  -> recursive Json/Representation/Check/Document lowering
  -> target binding and duplicate-key admission
  -> exact TypeScript source fixture
  -> direct TypeScript compiler
  -> pinned Effect document revival
  -> Effect language-service diagnostics
  -> raw 22-representation / 2-check generation and revival coverage
  -> raw Json target reification and lowering injectivity [CLOSED]
  -> document revival / decoded-value denotational simulation [OPEN]

DATA-ROW-01 canonical row declaration and normalization
  -> DATA-ROW-02 row union associativity, commutativity, and idempotence
  -> DATA-ROW-03 membership and requirement weakening

SC-REP-CLOSED + SC-DOC-CLOSED + SC-REG-01 + SC-REG-02
  -> SC-DEN-01 representation/type/value judgments
  -> SC-DEN-02 primitive/product/array/object semantics
  -> SC-DEN-03 ordered anyOf theorem
  -> SC-DEN-04 exactly-one oneOf theorem
  -> SC-DEN-05 enum-alias relation
  -> SC-DEN-06 document-relative references
  -> SC-DEN-07 recursive evaluator soundness
  -> SC-DEN-08 evaluator completeness for the named guarded profile

SC-DEN-01 + SC-WIRE-04
  -> SC-WIRE-06 normalization_preserves_denotation [OPEN until SC-DEN-01 freezes]

P3-ALGEBRA-CLOSED + DATA-ROW-01/02/03 + SC-ISSUE-01 typed issue exit
  -> SC-GET-P-01 Program-based getter declaration and denotation
  -> SC-GET-P-02 identity
  -> SC-GET-P-03 associative composition
  -> SC-GET-P-04 requirement weakening and row union
  -> SC-TR-01 transformation declaration
  -> SC-TR-02 flip involution
  -> SC-TR-03 reversed encoding composition
  -> SC-TR-04 composition associativity
  -> SC-CODEC-01 primitive codec
  -> SC-CODEC-02 decodeTo construction
  -> SC-CODEC-03 exact decoded/encoded indices
  -> SC-CODEC-04 exact directional requirement unions
  -> SC-CODEC-05 decode pipeline semantics
  -> SC-CODEC-06 encode pipeline semantics
  -> SC-CODEC-07 law-grade classifier and witnesses
  -> SC-CODEC-08 existential views

P4-FLOW-SEMANTICS-CLOSED + SC-GET-P-01
  -> SC-GET-F-01 first-order Getter Flow alphabet and payloads
  -> SC-GET-F-02 checked Getter admission
  -> SC-GET-F-03 CheckedFlow-to-Program elaboration
  -> SC-GET-F-04 elaboration preserves Getter denotation
  -> SC-GET-F-05 reify/elaborate round trip for the selected generated syntax
  -> SC-GET-F-06 fixed-compatible-tape determinism
  -> SC-GET-F-07 arbitrary Program reification explicitly not claimed

SC-REG-01 first-order declaration/check registry
  -> SC-REG-02 uniqueness, arity, payload admission
  -> SC-REG-03 denotation lookup agreement
  -> SC-HOST-01 generated TypeScript registry
  -> SC-HOST-02 reviver bijection and negative tests
  -> SC-HOST-03 direct rc.112 typecheck plus diagnostic gate
  -> SC-HOST-04 runtime differential vectors
  -> SC-HOST-05 source/profile drift gate

SC-REP-CLOSED + SC-WIRE-CLOSED + SC-PROFILE-CLOSED
+ SC-DOC-CLOSED + SC-DEN-CLOSED + DATA-ROW-CLOSED
+ SC-CODEC-CLOSED + SC-GET-F-CLOSED + SC-REG-CLOSED + SC-HOST-CLOSED
  -> SC-CAS-01 Foldlab profile embedding
  -> SC-CAS-02 injective on existing well-formed values
  -> SC-CAS-03 profile retraction
  -> SC-CAS-04 refusal mapping
  -> SC-CAS-05 payload/address/byte compatibility
  -> SC-CAS-06 both builds and axiom receipts
  -> SC-CUTOVER
```

Each `*-CLOSED` name is the generated conjunction of every required node in
that family, including retained counterexamples and axiom receipts. It is not
a manually assignable status. In particular, the open `SC-WIRE-06` edge keeps
`SC-WIRE-CLOSED` and therefore full Schema cutover open.

## Required counterexamples

The breaker packet must allocate these stable IDs in the central register and
retain executable or immutable witnesses:

```text
E4-SCHEMA-CE-001 overlapping anyOf chooses first success
E4-SCHEMA-CE-002 overlapping oneOf rejects multiple successes
E4-SCHEMA-CE-003 enum aliases defeat encode injectivity
E4-SCHEMA-CE-004 optional tuple member before a required member
E4-SCHEMA-CE-005 trim refutes universal round trip
E4-SCHEMA-CE-006 decode-only service does not leak into encode requirements
E4-SCHEMA-CE-007 encoding composition is reversed
E4-SCHEMA-CE-008 missing declaration reviver
E4-SCHEMA-CE-009 duplicate reviver identity
E4-SCHEMA-CE-010 local symbol cannot enter portable wire data
E4-SCHEMA-CE-011 non-JSON annotation pruning
E4-SCHEMA-CE-012 duplicate key becomes invisible after map parsing
E4-SCHEMA-CE-013 bare self-reference cycle
E4-SCHEMA-CE-014 guarded recursive reference
E4-SCHEMA-CE-015 bounded naive-guardedness fan-out cost witness; asymptotic claim open
E4-SCHEMA-CE-016 middleware is not a value getter
```

CAS address, revision, content-binding, and exact refusal-precedence witnesses
remain in Foldlab's counterexample register.

## Existing Foldlab type disposition

| Source family | Disposition |
| --- | --- |
| `Union`, generic guardedness, and discriminated-union analysis | refactor algorithms and proofs over the new representation; retain order and `anyOf`/`oneOf` distinction |
| `Guarded` complexity witness | move the bounded fan-out cost witness to Effect4's central counterexample suite; prove any asymptotic classification separately |
| `Foreign` | reuse four-index TypeScript API names only after the target type IR can express them |
| `Described` | preserve as an explicitly lossless equivalence classification |
| deriving utilities | reuse metaprogramming technique; `Lean.Expr` is input only and emitters produce checked rows |
| `SelfCodec` | split into proof seeds for the full rc.112 profile, normalization, strict decoding, round trip, injectivity, and decoder normality |
| `Ast` and `El` | do not port as base carrier or denotation |
| pure codec and codec laws | retain as downstream CAS codec; reuse theorem patterns and compatibility tests only |
| declaration registry | keep CAS scalar restrictions and closed rows downstream; Effect4 owns an open first-order registry plus checked profiles |
| admission map and ingest | downstream policy/refusal door; generic table and audit techniques may be reimplemented without copying ownership |
| projection, payload injection, basis, references, scalars | downstream CAS store/value/byte compatibility |
| annotation, exchange, system, notation, facade | downstream domain schemas and API |

The reusable current tests are the rc.112 structural/cycle pins, guardedness
cost regression, generic union/materialization cases, and registry/reviver
coverage. CAS byte pins, the 79-case Foldlab verdict corpus, content-address
reference assembly, and CAS source snapshots stay downstream and become
compatibility gates.

## Entry gate for implementation

No declaration enters the Schema stubs until the breaker freezes:

1. the exact 22-tag representation and persisted-field snapshot above;
2. ordinary decoded/encoded Lean indices, reuse of
   `Signature.Op`/`Signature.Answer`, and sole `Data.Row` ownership of
   requirements;
3. the Program-based Getter semantics and the later CheckedFlow
   reification/elaboration boundary;
4. the four-index getter/transformation/codec signatures and directional
   composition equations;
5. the refusal boundaries above; and
6. the sixteen `E4-SCHEMA-CE-*` central counterexamples.

Conditions 2 through 5 gate the denotation, getter, transformation, codec, and
checked refusal boundaries. They do not gate the tag alphabet or passive
payload data merely because those declarations will later be consumed there.
The structural payload slice may begin once its D0-D6 breaker freezes exact
bits, constructors, recursive edges, equality, and document container shapes.
The D7 field-admission slice may begin only after its breaker freezes the
recursive characterization above and keeps structural failure, profile
narrowing, wire duplication, and host errors distinct.

The first implementation slice is structural representation and source census.
Its current boundary is split as follows:

- **Tag declarations — structurally closed.** The six exact type rows, their
  one-parent-graph/five-leaf allocation, and their native contract origins are
  recorded in `PORT-MANIFEST.md`.
  `Test/contracts/schema-representation.contract.md` and
  `Test/contracts/schema-subalphabets.contract.md` are the frozen breaker
  packets, preserved separately in commit `f487774`, with counterexamples
  `E4-SCHEMA-CE-017` through `E4-SCHEMA-CE-022`. The implementation, axiom
  report, lexical source evidence, and bounded mutation receipt are present.
  `generated/schema-structural-assurance.tsv` now joins those inputs against
  the complete owned-declaration census, so every applicable edge of
  `SCHEMA-PG-REPRESENTATION-TAG` and the tag/source share of `SC-REP-02` are
  closed. Its semantics, laws, bridges, and targets remain the four frozen
  `not-applicable` edges of this tag-only graph.
- **Payload and field admission — structurally implemented and joined.** The frozen
  D0-D6 structural slice and D7 recursive-admission slice are intentionally
  the only two graph-bearing families in this packet. The module DAG is
  `Data.Json` (D0-D1) -> `Schema.Payload` (D2-D3) ->
  `Schema.Representation` (D4-D5) -> `Schema.Document` (D6) ->
  `Schema.Check` (D7); `Schema.Value` owns later denotation only. The repaired
  mechanical reaction gate kills an ordinary extra constructor, an
  uninhabited extra constructor, a constructor permutation, a field-type
  drift, an unallocated alias, an ordinary public type-valued definition, four
  D7 owner drifts, a declaration-free upward `Schema.Value` import, and two
  source overrides. Its fixed production half also materializes
  the packet's `payloadBoundaryImportProbe` from an isolated module whose only
  library import is `Effect4.Schema.Payload`: D0-D3 must resolve, D4-D7 must
  remain unreachable, ownership inspection must assign D0-D1 to
  `Effect4.Data.Json` and D2-D3 to `Effect4.Schema.Payload`, and an upward
  Payload import must be rejected. The production half and all 13 reactions
  are green. The generated join covers all 1,298 declarations owned by the
  seven joined modules, all 493 theorem and axiom receipts, 32 counterexamples, nine
  duplicate-prevention names, and all leaf routes. It closes
  `SCHEMA-PG-FIELD-ADMISSION`, `SC-REP-01`, and the structural equality,
  tag-projection, and general-recursor shares of `SC-REP-03`. The recursor's
  24 public equations, two rebuild identities, empty axiom receipts, and
  all-route counterexample are joined. Denotation, document interpretation,
  wire form, and host conformance remain their separate later graphs.
- **Optics and annotation data — closed.** `DATA-PG-OPTIC` and
  `SCHEMA-PG-ANNOTATION-DATA` join the generic composition laws, exact typed
  annotation codecs, local field views, and exhaustive structural traversals.
  Only those higher-order and recursive obligations receive graphs; direct
  getters, setters, and constructor equations remain ordinary receipts. The
  joined host gate generates the field-admission witness from Lean and checks
  it with TypeScript, Effect rc.112, and the Effect language service.

The pinned bytes needed by `SC-REP-CENSUS-PIN` are now local to this library at
`vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts`, verified at SHA-256
`a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`.
`./scripts/check-schema-census.sh` lexically extracts the closed source unions
and the `Schema.tag(...)` / `makeKeywordSchema(...)` call-site spellings, then
compares their exact set with the Lean `tagName` set. On the pinned bytes, a
passing run supplies spelling-set evidence for 22 representation tags and 2
check tags, with no additions or removals. It does not check payloads, decoding,
semantics, or full host faithfulness, and it does not assign cutover status.

The gate requires the pinned digest before it reports pin-matched evidence and
refuses other bytes unless `--dry-run` is passed.

It takes two independent extractions from the source and refuses to report
agreement unless they match each other: the closed `export type Representation`
and `export type Check` unions, and the `Schema.tag` / `makeKeywordSchema`
codec call sites. An earlier version used only the call sites, and an
independent reviewer showed that a 23rd tag could be added past it.

The **source shape** is what makes the union route worth having: at the pin,
`export type Representation =` occurs exactly once (`:406`) and
`export type Check =` exactly once (`:436`), so each family has one declaration
site to read, and the 22 members are listed there with no comments interleaved.
That is a statement about the pinned bytes, and it is checked.

What the **detector** rejects is a separate question, answered only by the
enumerated reaction-test mutants below. It is not answered by the shape of the
source. An earlier wording here said the union route "rejects that mutation";
that was falsified by execution against a copy of the real pinned bytes and is
recorded as a fired finding.

`./scripts/test-schema-census-gate.sh` is a finite reaction suite. It shows
that the detector rejects fourteen specified defects: a renamed, added, or
deleted codec tag; a 23rd member in the union alone; a 23rd member in **both**
the union and the codec; a check tag copied into the representation family; a
23rd union member hidden behind a comment inside the union; the same with a
single-quoted codec tag; a Lean spelling hidden behind a trailing Lean comment;
`--lean-source` without `--dry-run`; a broken call-site pattern; a renamed
union declaration; off-pin bytes without `--dry-run`; and a missing source. The
last run recorded here reported `14/14` on 2026-08-31.

The detector's demonstrated coverage is exactly those fourteen mutants and
nothing broader. Three of them exist because the corresponding hole was found
by execution, not by review, after this document had already asserted that the
union route rejected an added tag. Treat any further strength claim as
unmade.

Two limits on this evidence are recorded rather than glossed.

**It is reproducible from this checkout.** The exact third-party source file
and its package license are vendored as evidence-only inputs. The generated
Schema assurance gate invokes both source extractors on that fixed path and
refuses a digest mismatch or input override. Effect4 never imports or executes
the vendored TypeScript.

**It is an extraction, not a proof about the runtime.** The assumption is that
the closed type unions are the persisted alphabet. That assumption is named
here because it is the one an extraction cannot verify about itself.

One extraction caveat is recorded. Harvesting `readonly _tag: "X"` instead
yields a 23rd name, `Import`. It is not a persisted representation: it belongs
to `Artifact` in `CodeDocument`, which is code-generation output. The census
is right to exclude it, and the `Schema.tag` / `makeKeywordSchema` route is
the correct one.

`Suspend` is **resolved, at the pin**. rc.112 declares
`readonly thunk: Representation` (`SchemaRepresentation.ts:162`) and its codec
uses `thunk: RepresentationSchema` (`:988`). The persisted field is already
first-order data, not a function, so nothing in this repository's prohibition
on stored host closures is violated by modelling it as a nested
representation. Its `checks` field is `Schema.Tuple([])` (`:987`) — present
and exactly empty, as the census table states.

A related behavior, observed off-pin in `beta.103` and **not** yet verified at
rc.112, is that lowering forces the thunk and cuts recursion by emitting a
`Reference` into the document's references table. That is a lowering claim,
not a representation claim, and it belongs to the `SC-DOC-*` packet.

Two obligations are added to the graph, both owed:

`SC-DOC-06` productivity is not guardedness. A guarded document may still have
no value: `Suspend` is a delay, not a constructor, so a recursive occurrence
under one is deferred rather than broken. Vendored Foldlab evidence exhibits
three documents that pass guardedness and on which Effect's own validator
diverges or overflows (`Cas/Schema/Guarded.lean:29-50`). Consequently
`SC-DEN-07` and `SC-DEN-08` are **not** termination claims and must not be
worded as any. Deciding productivity needs a separate relation over head
positions, tracking what a name reaches through `Suspend` wrappers alone
before any constructor builds anything; `Union` builds nothing either.

rc.112 implements exactly that separation, and its own source names the hazard.
`ReferenceSlot` (`internal/schema/fromRepresentation.ts`, SHA-256
`0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e`, `:19-31`)
returns a `Schema.suspend` wrapper whenever revival re-enters a slot still
marked `resolving` (`:76-77`), so an alias cycle **constructs**. The wrapper's
body then throws `Reference ${key} was evaluated before it was resolved`
(`:27`) if anything reaches it before a body exists. Construction is decided by
guardedness; whether a value ever appears is not decided at all. A bounded
host-local probe agrees: on the resolved-package pin, `A -> A` and
`A -> B -> A` both revive successfully through `fromRepresentation` and then
fail to terminate under `Schema.decodeUnknownSync` within a 25-second bound,
raising no error. That is a finite probe on a timeout, not a proof of
divergence, and it carries the same non-reproducibility caveat as the sealed
pin below: `harness/` has no runner, so nothing in this checkout re-runs it.

`SC-DOC-07` canonical emission order for unions. Union member order is
identity. A generator that does not fix a canonical order makes a generated
document's content address depend on source arrangement.

## Effect4 admission is strictly stricter than the host

This section covers `E4-SCHEMA-CE-024`, `E4-SCHEMA-CE-025`, and the layer split
`E4-SCHEMA-CE-040` forced on the latter.

A first-party executable pin against rc.112 is sealed in the evidence vendor at
`vendor/foldlab/pinned/tree/library/effects/test/SchemaReferencesPin.test.ts`
(SHA-256 `73b28e60505f219903cbdcb5e390e1a201df469a5b91f17269f45a19064106cb`).

**What "accepts" means here has a layer, and the two layers disagree.** The
sealed pin's own predicate is
`readsBack = (json) => { try { SchemaRepresentation.fromJson(json); return true } catch { return false } }`
(`:67-75`), under its own comment "Does Effect's own codec read this document
back?". It exercises the **document codec** — parsing persisted JSON into a
`Representation` — and nothing else. Revival, `fromRepresentation`, is a
different function with different answers. So:

| Shape | `fromJson` | `fromRepresentation` |
| --- | --- | --- |
| a `$ref` naming no table entry | accepts | **refuses**: `Invalid reference <key>` |
| a self alias, `A -> A`, which resolves to no node | accepts | accepts |
| a two-step alias cycle, `A -> B -> A` | accepts | accepts |
| a structural cycle with no `Suspend` anywhere on the path | accepts | accepts |
| a dead table entry nothing points at | accepts | accepts |

The refusal is `resolveReference` in
`internal/schema/fromRepresentation.ts` (SHA-256
`0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e`), which
throws `Invalid reference ${key}` at `:67-68` when the key is absent from the
table. The four cycle and dead-entry rows survive revival for a specific
mechanical reason: `ReferenceSlot` (`:19-31`) holds a `Schema.suspend` wrapper,
and re-entering a slot still marked `resolving` returns that wrapper rather
than recursing (`:76-77`). **Non-termination is deferred to use, not raised at
construction.** The wrapper's own body carries the host's admission of the
hazard — `Reference ${key} was evaluated before it was resolved` (`:27`).

Any sentence in this repository that says rc.112 "accepts" one of these five
must therefore name the layer. Unqualified, the dangling-`$ref` row is false.

The same pin confirms two positive spellings: `Suspend` has exactly the keys
`_tag`, `checks`, `thunk`, its `checks` is always empty and a `Suspend`
carrying a check is refused by Effect itself; and a `Document` has exactly the
keys `representation` and `references`. Recursive documents survive Effect's
own JSON round trip.

**This evidence is not reproducible from this checkout.** The same caveat the
census gate carries above applies here, and for a sharper reason: `harness/`
holds only `README.md` and `AGENTS.md`, so there is no runner, no
`effect@4.0.0-rc.112` install, and no TypeScript toolchain in this repository
that could execute `SchemaReferencesPin.test.ts`. `vendor/foldlab/pinned/` is
read-only evidence and this repository must not depend on Foldlab, so the file
is here as **bytes that assert these results**, verified by digest, executed
elsewhere. The `fromRepresentation` column above was likewise obtained on this
host by running the five shapes through the installed
`effect@4.0.0-rc.112` package — the resolved-package pin of the authority
table, whose `src/SchemaRepresentation.ts` is byte-identical to the semantic
pin — not by any command this checkout can re-run. Reproducing either needs a
local install with the path supplied by hand. Until `harness/` acquires a
runner, no `SC-HOST-*` edge may be closed by citing this section.

The consequence is a standing claim-scope rule. Effect4's reference closure,
guardedness, and dead-entry rules are **narrower than rc.112**. A document
Effect4 refuses may be perfectly acceptable to the host, so:

- no Effect4 refusal may be described as an rc.112 refusal without naming this
  gap; and
- `SC-CAS-*` compatibility must be stated directionally. Effect4-admitted
  implies host-accepted is the claimable direction; the converse is false and
  must never be asserted.

This is a profile decision, not a defect in either system. It needs its own
recorded profile row rather than being absorbed into admission.

The proof-level Getter, Transformation, and Codec laws may proceed over the
existing `Program` after `Data.Row` and schema issue exit are frozen. Their
first-order storage, generation, and reify/elaborate proofs wait for checked
Flow semantics; neither lane may mint a temporary effect type.

## Fired findings

This ruling is frozen design input. A finding against it is recorded here, in
the `BROKE / LAW / WITNESS / CLASS / FIXED-BY` form the contract packets use,
rather than repaired silently in the prose.

### The persisted-field snapshot mis-cited eight of its own twenty-three lines

BROKE: the header of §Verified persisted-field snapshot, which said the field
constraints were "checked line by line against the pinned bytes", and eight
line citations inside the block it introduces.

LAW: every citation in the block was re-derived from the pinned
`SchemaRepresentation.ts` (SHA-256 `a0a7…e69bc`) by locating each named
binding, independently of the block. Fifteen agreed. Eight did not:

| Cited | Subject | Actual | What sat at the cited line |
| --- | --- | ---: | --- |
| `:969` | keyword tags | 970 | blank |
| `:976` | `Declaration` | 977 | blank |
| `:985` | `Suspend` | 984 | `_tag: Schema.tag("Suspend"),` |
| `:1040` | `PropertySignature` | 1039 | `name: Schema.Union([` |
| `:1065` | `Reference` | 1066 | `})` closing `UnionSchema` |
| `:1093` | `References` | 1096 | `UnionSchema` inside `RepresentationUnion` |
| `:1095` | `Document` | 1098 | blank |
| `:1103` | `MultiDocument` | 1105 | `)` closing `DocumentFromJson` |

WITNESS: the offsets are -1, +1, -1, +1, -1, -3, -3, -2. No numbering base,
zero-indexing convention, or uniform shift produces that spread, so these are
independent errors, not one systematic one. Four of the eight point at a blank
line or a closing bracket — text that cannot be mistaken for the cited subject
by a reader who opened the file.

CLASS: claim scope, plus fact. The field content of the block was correct and
has been independently re-verified; the failure was entirely in the navigation
column and in a header that asserted a stronger verification procedure than had
been performed. "Checked line by line" is falsified by its own block: a
line-by-line check is exactly the procedure that would have caught eight wrong
lines, and none were caught.

FIXED-BY: the eight citations corrected to the binding lines above; the block
now states the convention it uses (the `const <Name>Schema = Schema.Struct({`
line, or the `function` line for `makeKeywordSchema`), which is what made the
errors visible; and the header now separates the two claims by strength —
field content re-derived, line numbers a navigation aid re-derived on
2026-08-31 — and records that no script in this repository compares the block
against the pin, so either column can still drift silently. Three citations
outside the block (`:162`, `:987`, `:988` under §`Suspend` is resolved, and
`:1005`, `:999`, `:1020`, `:1042` under the `number` ruling) were re-derived in
the same pass and were already correct.

### "the union route rejects that mutation" was a claim about the detector

BROKE: the §Entry gate sentence describing the census gate's two extraction
routes, which said the closed unions "are single-site and exhaustive" and that
"the union route rejects that mutation" — the mutation being a 23rd tag added
past the call-site-only extractor.

LAW: falsified by execution against a copy of the real pinned bytes.
`scripts/check-schema-census.sh`'s union extractor terminated on the first line
without a leading `|`, so a single `//` comment inside the union truncated the
extraction and a 23rd member hid behind it. The codec route did not catch it
either: its pattern matched double-quoted tag literals only, so
`Schema.tag('Newthing')` went uncounted. On that source the old gate printed
`PASS both lexical source routes agree by family: 24 spellings (22
representation, 2 check)` and exited 0. A third hole in the same family: the
Lean scrape took the first quoted string on a `|` line, so a comment carrying
the pinned spelling with a different value on the next line passed.

WITNESS: the three holes are now regression mutants in
`./scripts/test-schema-census-gate.sh` — "comment-hidden 23rd union member",
"comment-hidden member with single-quoted codec tag", and "Lean spelling hidden
behind a trailing comment". The suite reports `14/14`.

CLASS: claim scope. Two different propositions were fused into one sentence.
*The pinned source declares each union at one site* is true and checkable —
`export type Representation =` at `:406` and `export type Check =` at `:436`,
once each. *The detector reads that union correctly* is a claim about a shell
script, and does not follow from the source's shape. The document asserted the
second on the strength of the first.

FIXED-BY: the passage now states the source-shape fact and the detector's
coverage separately, names the detector's coverage as exactly the fourteen
enumerated mutants and nothing broader, and records that three of those mutants
exist because execution found the hole after this document had already
asserted that the union route rejected an added tag.

### `E4-SCHEMA-CE-025` stated an acceptance without naming its layer

BROKE: §Effect4 admission is strictly stricter than the host, which said the
sealed vendor pin "establishes that rc.112 **accepts**" five shapes, listing a
dangling `$ref` first.

LAW: the sealed test's own predicate is `readsBack` (`:67-75`), which calls
`SchemaRepresentation.fromJson` and nothing else, under the comment "Does
Effect's own codec read this document back?". At revival, `resolveReference`
(`internal/schema/fromRepresentation.ts`, SHA-256 `0b95c360…36d82e`) throws
`Invalid reference ${key}` at `:67-68`. Re-run on this host against the
resolved-package pin, the dangling `$ref` is accepted by `fromJson` and refused
by `fromRepresentation`; the other four are accepted at both.

WITNESS: `E4-SCHEMA-CE-040` in `Test/Counterexamples/REGISTER.md`.

CLASS: claim scope. "rc.112 accepts" named a system where the evidence named a
function. One of the five rows is false at the layer a reader would most likely
assume — the one that turns a persisted document into a usable schema.
Separately, the section asserted an executable result with no note that
`harness/` contains only `README.md` and `AGENTS.md`, so the sealed test cannot
run in this checkout at all; the census gate two sections earlier already
carried exactly that caveat.

FIXED-BY: the five acceptances are now a per-layer table naming `fromJson` and
`fromRepresentation` separately, with the refusal's source line; the mechanism
that saves the four cycle and dead-entry rows at revival — `ReferenceSlot`'s
`Schema.suspend` wrapper on `resolving` re-entry (`:19-31`, `:76-77`) — is
recorded, along with the host's own guard string at `:27`; and the section now
carries the non-reproducibility caveat, stating that both the sealed pin and
the `fromRepresentation` column are host-local and that no `SC-HOST-*` edge may
be closed by citing them. `SC-DOC-06` gained that same mechanism as its
host-side statement of the hazard, with a bounded, non-reproducible probe
attached and reported as a probe.

## Archived host pin: Codec

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


## Archived host pin: Foreign

/-!
# Schema.Foreign.lean

Owner: Fail-closed host reviver boundary.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The boundary where a stable registered identity crosses to host code. The
disposition is `foreignBoundary`: a registered identity crosses, an arbitrary
closure never does. A missing reviver is a refusal, not a default — hence
*fail-closed*.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-HOST-02` reviver bijection and negative tests

and feeds `SC-HOST-01` generated TypeScript registry, `SC-HOST-03` direct
rc.112 typecheck plus diagnostic gate, `SC-HOST-04` runtime differential
vectors, and `SC-HOST-05` source/profile drift gate.

## Retains

- `E4-SCHEMA-CE-008` missing declaration reviver
- `E4-SCHEMA-CE-010` local symbol cannot enter portable wire data
- `E4-SCHEMA-CE-011` non-JSON annotation pruning

`E4-SCHEMA-CE-010` has a necessary condition enforced by the current alphabet:
`PropertyKeyKind` has no `localSymbol` constructor (`E4-SCHEMA-CE-022`). Its
leaf receipt and parent edge remain cutover-open, and the local exclusion would
not discharge `-010` anyway because that attack reaches the payload and
lowering layers.

## Gated by

The registry and the payload carrier. The exact rc.112 bytes are host-local at
`library/effects/node_modules/effect/src/SchemaRepresentation.ts` in the
Foldlab checkout and already support the lexical census gate; they are not
vendored into Effect4. The host reviver, runtime, and language-service gates
remain open, and lexical tag agreement does not close them. See
`SC-REP-CENSUS-PIN` in `docs/SCHEMA-CUTOVER.md`.

## Host evidence at the pin

Read off rc.112 source; not executed here, and host-local for the reason given
just above. Reading source establishes what the host *code says*; it is a
finite reading, not a runtime observation, and it closes no `SC-HOST-*` row.

On the missing-reviver case the fail-closed disposition recorded above
**agrees with the host**: `internal/schema/fromRepresentation.ts:95` throws
`Missing reviver for <id>` instead of substituting a default, and
`SchemaRepresentation.ts:1250` states that none are installed implicitly. So
`E4-SCHEMA-CE-008` names a refusal rc.112 also performs. The row stays open. A
host throw is evidence about rc.112, not an Effect4 refusal classification,
and this repository must still decide whether that refusal is a typed failure,
a defect, or a domain refusal — a decision `PLAN.md` requires be made
explicitly rather than inherited.

Two places where the host boundary is **wider** than this module's
disposition. The boundary design has to survive both rather than assume them
away, and neither may be cited as support for fail-closed:

- **A reviver returns a host object and may raise.** `revive` produces a
  `Schema.Top` (`SchemaRepresentation.ts:509`), and the host contract is that
  reviver "results are used directly, and exceptions raised by a reviver pass
  through unchanged" (`:1212`). rc.112 therefore does not confine reviver
  failure to a value; an arbitrary host exception escapes `fromRepresentation`.
  This is the concrete shape of the `foreignBoundary` disposition: what crosses
  is a registered identity, but what the *host* runs behind that identity is
  unconstrained code with an unconstrained failure mode.
- **For declarations and leaf filters, `representation` is optional only in
  the live interface.** The persisted `DeclarationSchema` and `FilterSchema` require it
  (`SchemaRepresentation.ts:956-960,977-983`), so `fromJson` rejects an
  omission before revival. A hand-constructed live declaration or filter can
  still omit it, and revival then throws `Missing representation annotation`
  (`internal/schema/fromRepresentation.ts:126,142`). That is a layer split
  between live construction, persisted admission, and revival; this module
  must not flatten the three.

## A second door for `E4-SCHEMA-CE-010`

`E4-SCHEMA-CE-022` closes one route by absence: `PropertyKeyKind` has no
`localSymbol` constructor, so a local symbol has no spelling as a *persisted
property key*. That exclusion is real and it is not sufficient, because the
persisted representation is not the only place a key-like value travels.

The rc.112 issue alphabet carries a `Pointer.path` (class `SchemaIssue.ts:316`,
field `:321`,
recursion at `:325`) which admits local symbols, and `Base.input` (`:157`) is
retained **by reference** rather than copied (`SchemaAST.ts:529`) and is
reachable on nine of the eleven issue variants. rc.112 itself writes a live
host `symbol` into `input` (`SchemaAST.ts:4098-4102`). So a local symbol that
the representation alphabet can never spell can still be reached through a
diagnostic produced while decoding that representation.

This does not reopen `E4-SCHEMA-CE-022`, which is about the key alphabet and
remains discharged by absence. It does mean `E4-SCHEMA-CE-010` may not be
treated as approaching closure once the key alphabet and the payload carrier
are settled: whichever module ends up owning `SC-ISSUE-01` inherits a second
door, and that ownership is currently unassigned. See
`docs/SCHEMA-ISSUE-SURVEY.md` for the per-field host-boundary account.

Attribution: read off rc.112 source and finite host probes recorded in that
survey; one build on one host, and not reproducible from this checkout alone.
-/


## Archived host pin: Getter

/-!
# Schema.Getter.lean

Owner: Directional property access over the existing `Program` semantics, plus
the later checked-Flow reification and elaboration bridge.

The proof-level Getter is not serializable content. The later reified face
uses the one common `CheckedFlow`; Schema does not introduce another program
carrier.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

Two faces of one getter, in this order.

1. **Proof semantics.** A getter denotes
   `Option E × ParseOptions → Program (SchemaIssueSig ⊕ₛ S) (Option T)`.
   This higher-order function is a proof carrier and is never serialized as
   canonical program content.
2. **First-order reification.** Once checked Flow has relational semantics,
   the admitted getter language stores blocks as `CheckedFlow`, and
   elaboration interprets that graph back into the proof semantics.

No Schema-specific effect monad and no second free-program carrier.

## Pin citation scope

Every `File.ts:NNN` citation in this module is a line of the installed
`effect@4.0.0-rc.112` sources on the build host, under
`library/effects/node_modules/effect/src/` in the Foldlab checkout. That tree
is third-party read-only evidence. Nothing from it is imported, vendored, or
copied into this repository as code, and reading it creates no Foldlab
dependency.

`docs/SCHEMA-CUTOVER.md` owns the digests; this module does not restate them.
Two limits carried from that table apply to every line number below:

- `SchemaGetter.ts`, `SchemaTransformation.ts`, `SchemaAST.ts`,
  `SchemaIssue.ts`, and `SchemaParser.ts` byte-match the upstream semantic
  revision, so their line numbers are stable across both pins.
- `Schema.ts` does **not** byte-match. Every `Schema.ts:NNN` below is a line of
  the *installed package only* and must be re-derived before it is quoted
  against the upstream revision.

This section is pinned source reading. It is not a Lean theorem, a decoder
result, an executed test, or any claim that a future Effect4 carrier agrees
with rc.112 on a judgment.

## Pin: the exact getter alphabet

`SchemaGetter.ts` exports 52 names: one class, one type alias, two non-getter
helpers, and 48 functions returning a `Getter`.

The carrier and its complete method surface:

```text
class Getter<out T, in E, R = never> extends Pipeable.Class    :64
  run : (Option<E>, SchemaAST.ParseOptions)
          -> Effect<Option<T>, SchemaIssue.Issue, R>           :65-68
  map<T2>(f : T -> T2) : Getter<T2, E, R>                      :79-81
  compose<T2,R2>(other : Getter<T2, T, R2>)
          : Getter<T2, E, R | R2>                              :82-90
```

There is no `flip`, no failure handler, no annotation accessor, and no AST
accessor on the carrier. `map` and `compose` are the whole surface
(`SchemaGetter.ts:79`, `:82`).

Eight sites construct a getter directly; every other exported getter is
defined from these. This is the primitive alphabet:

```text
succeed<T,E>(t)                       :121   new Getter at :122
fail<T,E>(f)                          :157   new Getter at :160
passthrough_  (module-private value)          new Getter at :203
onNone<T,E,R>(f)                      :351   new Getter at :354
onSome<T,E,R>(f)                      :424   new Getter at :427
transformOptional<T,E>(f)             :597   new Getter at :598
omit<T>()                             :629   new Getter at :630
withDefault<T,R>(defaultValue)        :662   new Getter at :665
```

Eight further generic combinators are derived, each by one call:

```text
forbidden<T,E>(message)               :194   via fail            :195
passthrough<T,E> / <T>                :246-248  returns passthrough_ :249
passthroughSupertype<T extends E, E>  :280-283  returns passthrough_ :282
passthroughSubtype<T, E extends T>    :313-316  returns passthrough_ :315
required<T,E>(annotations?)           :387   via onNone          :388
checkEffect<T,R>(f)                   :467   via onSome          :474
transform<T,E>(f)                     :521   via transformOptional :522
transformOrFail<T,E,R>(f)             :561   via onSome          :564
```

The remaining 33 exported getters are a concrete conversion library, not
additional structure. In source order:

```text
String :697   Number :728   Boolean :756   BigInt :785   Date :817
trim :840   capitalize :863   uncapitalize :886
snakeToCamel :911   camelToSnake :936
toLowerCase :961   toUpperCase :986
parseJson :1027   stringifyJson :1087
splitKeyValue :1136   joinKeyValue :1181   split :1219
encodeBase64 :1249   encodeBase64Url :1276   encodeHex :1302
decodeBase64 :1329   decodeBase64String :1365
decodeBase64Url :1404   decodeBase64UrlString :1442
decodeHex :1481   decodeHexString :1519
encodeUriComponent :1558   decodeUriComponent :1583
dateTimeUtcFromInput :1631
decodeFormData :1675   encodeFormData :1714
decodeURLSearchParams :1758   encodeURLSearchParams :1794
```

The three non-getter exports are `type JsonReplacer` (`:1047`),
`makeTreeRecord` (`:1867`), and `collectBracketPathEntries` (`:1962`).

Scope note. This is a name-and-signature census of one file at one digest,
taken by reading `^export` sites. It is not a proof that the 15 generic
combinators generate the 33 concrete ones under any Effect4 relation, and it
assigns no Effect4 declaration.

## Pin: in what sense a getter is effectful

The result type is `Effect<Option<T>, SchemaIssue.Issue, R>`
(`SchemaGetter.ts:68`). Taking the three questions separately:

**Can it fail.** Yes, and the typed error channel is exactly
`SchemaIssue.Issue` (`SchemaGetter.ts:68`), never a wider error type. That
`Issue` alphabet is 11 constructors: six leaves — `InvalidType`,
`InvalidValue`, `MissingKey`, `UnexpectedKey`, `Forbidden`, `OneOf`
(`SchemaIssue.ts:107-113`) — and five composites — `Filter`, `Encoding`,
`Pointer`, `Composite`, `AnyOf` (`SchemaIssue.ts:142-149`). Failing getters at
the pin: `fail` (`:157-161`), `forbidden` (`:194-201`), `required`
(`:387-389`), `decodeBase64` (`:1329-1341`).

**Can it require a service.** Yes; `R` is the third index
(`SchemaGetter.ts:64`, `:68`). Five generic combinators are polymorphic in it:
`onNone` (`:351`), `onSome` (`:424`), `checkEffect` (`:467`),
`transformOrFail` (`:561`), `withDefault` (`:662`). Under `compose` the
requirement index is the union `R | R2` (`SchemaGetter.ts:82`), so getter
composition can only ever **grow** requirements. That monotonicity is the
shape `SC-GET-P-04` has to state, and it is exactly what middleware breaks —
see the next section.

**Can it be async.** Yes in principle, no in the shipped alphabet. `Effect`
admits asynchrony, and the user-supplied argument of `onNone`, `onSome`,
`checkEffect`, `transformOrFail`, and `withDefault` is an arbitrary `Effect`
with no synchrony constraint (`SchemaGetter.ts:352`, `:425`, `:468`, `:562`,
`:663`). But every `Effect` combinator used inside `SchemaGetter.ts` itself is
synchronous — `succeed`, `succeedSome`, `succeedNone`, `fail`, `try`,
`fromResult`, `mapEager`, `flatMapEager`, `mapErrorEager` — so no built-in
getter in that file constructs an asynchronous effect. rc.112 does ship one
first-party asynchronous link, in `Schema.File`'s JSON codec, which encodes
through `Effect.tryPromise` over an `async` thunk
(`Schema.ts:12861-12866`). rc.112's own documentation states the general
permission and its limit: transformations "may be asynchronous, may fail, and
may use optional services" (`Schema.ts:17163-17165`, `:17191-17193`), while
the synchronous adapters throw on an asynchronous transformation
(`Schema.ts:16584-16588`, `:16696`).

**Fourth channel, untyped.** `Issue` is the typed error channel only. A getter
body can still raise a host defect outside it. `SchemaAST.ts:4091` is a pin
example: the symbol decode getter dereferences a regexp match with a non-null
assertion, and it is total only under the assumption that the `isStringSymbol`
check on its `to` node already ran (`SchemaAST.ts:4083`). `ParseOptions`
carries `disableChecks` (`SchemaAST.ts:513`), and the parser honours it by
skipping checks (`SchemaParser.ts:1136`). So the pin's own code makes a
defect-raising path reachable by construction. Not executed here; recorded as
a hazard for `SC-GET-P-01`, which must say whether the Effect4 getter
denotation admits a non-`Issue` exit at all.

## Pin: middleware is a handler, not a value getter (`E4-SCHEMA-CE-016`)

Middleware at the pin is `SchemaTransformation.Middleware<T, E, RDE, RDT,
RET, REE>` (`SchemaTransformation.ts:71`). Three differences from a getter,
each independently load-bearing.

**1. Different input.** A middleware receives the whole inner `Effect`, not a
value: `decode : (Effect<Option<E>, Issue, RDE>, ParseOptions) ->
Effect<Option<T>, Issue, RDT>` (`SchemaTransformation.ts:73-76`), and
symmetrically for `encode` (`:77-80`). A getter receives `Option<E>`
(`SchemaGetter.ts:65-68`). The parser enforces the distinction on `_tag`: on
the failure path a `Transformation` is composed with `flatMapEager`, so its
getter is only ever run on a success (`SchemaParser.ts:1053-1057`), whereas a
`Middleware` is handed the failed effect itself (`SchemaParser.ts:1058-1062`,
and on the success path `:1050-1052`). A getter therefore cannot observe or
recover from an upstream `Issue`; a middleware can.

**2. Different requirement law — this is the sharp one.** `Getter.compose`
unions requirements, `R | R2` (`SchemaGetter.ts:82`). Middleware **discharges**
them: `middlewareDecoding<S, RD>` takes an effect requiring
`S["DecodingServices"]` and returns one requiring `RD`
(`Schema.ts:5318-5323`), and the resulting schema's index is set to `RD`
outright — `readonly "DecodingServices": RD` (`Schema.ts:5282`) — not to a
union with `S["DecodingServices"]`. `middlewareEncoding` is the mirror
(`Schema.ts:5337`, `SchemaAST.ts:3545-3549`). So requirement growth is
monotone under getter composition and non-monotone under middleware. A single
carrier for both makes `SC-GET-P-04` false as stated: row union stops being
the composition law for requirements, and `Data.Row` union stops being the
right lowering for the index.

**3. Different arity, and it is not cosmetic.** A `Transformation` has four
indices, `T, E, RD, RE` (`SchemaTransformation.ts:143`). A `Middleware` has
six, `T, E, RDE, RDT, RET, REE` (`:71`) — an input-side and an output-side
requirement per direction, with no relation imposed between them. Six indices
is the handler shape; four is the value shape.

**What breaks structurally if they share one carrier.** rc.112 itself shows
one concrete failure. Union member selection narrows candidates by walking
encoding links, and it gives up — `return unknown`, meaning "no narrowing" —
as soon as any link is a `Middleware` whose `decode` is not `identity`
(`SchemaAST.ts:2599-2612`, test at `:2608-2609`). The walk is safe for a
`Transformation` because a value getter cannot change the shape the inner
schema produced beyond its own declared `T`; it is not safe for a middleware,
which can replace the pipeline. Erase the `_tag` distinction and that guard
cannot be written, so ordered `anyOf` selection (`E4-SCHEMA-CE-001`) and
exactly-one `oneOf` (`E4-SCHEMA-CE-002`) lose their candidate filter.

The register's stated premise for `E4-SCHEMA-CE-016` is "Middleware and value
getters are one declaration shape". The pin refutes it on all three counts
above. The row's premise is corroborated as false; the row itself stays
RESERVED until Effect4 has an executable or compile-negative witness.

## Pin: what a getter observes

`run` takes exactly two arguments: `Option<E>` and `ParseOptions`
(`SchemaGetter.ts:65-68`). Consequences, each citable:

- **Presence, yes.** The optionality of the encoded slot is observable and
  producible: `onNone` branches on absence (`:354`), `onSome` on presence
  (`:427`), `omit` returns `None` unconditionally (`:630`), `required` turns
  absence into `MissingKey` (`:388`).
- **Parse options, yes, and they are first-order.** `ParseOptions` is exactly
  six optional fields (`SchemaAST.ts:459-550`): `errors` (`:471`),
  `onExcessProperty` (`:484`), `propertyOrder` (`:507`), `disableChecks`
  (`:513`), `concurrency` (`:520`), `reportInput` (`:549`). Each is a string
  literal union, a boolean, or `number | "unbounded"` — no closure, no AST, no
  host object. This corroborates the `ParseOptions` ruling in
  `docs/SCHEMA-CUTOVER.md`, and the six named observables there are exactly
  these six fields.
- **Surrounding structure, no.** The getter never receives its own AST node.
  Two neighbours at the pin do: a check is
  `run : (E, self : AST, ParseOptions) -> Issue | undefined`
  (`SchemaAST.ts:3209`) and a declaration parser is
  `(unknown, self : Declaration, ParseOptions) -> Effect<...>`
  (`SchemaAST.ts:666-668`). Getter is the only one of the three with no `self`.
  Note also that a check is synchronous and total — it returns `Issue |
  undefined`, not an `Effect` — so Check and Getter must not share a carrier
  either. That is a note for `Effect4/Schema/Check.lean`, which this module
  does not own.
- **Issue context, produced but not received.** A getter can build an issue
  and can pass `ParseOptions` into it (`SchemaGetter.ts:195-200`, `:1032-1035`,
  `:1334-1337`). It cannot read an incoming issue. Path and encoding context
  are attached *around* the getter by the parser, which wraps a raised issue in
  `SchemaIssue.Encoding(ast, issue, input, options)` after the fact
  (`SchemaParser.ts:1199-1212`), and by the separate composite issue
  constructors `Pointer` (`SchemaIssue.ts:316`) and `Composite`
  (`SchemaIssue.ts:445`, helper at `:600`).
- **Annotations, only as an authored argument.** `required` takes
  `annotations?: Schema.Annotations.Key<T>` and forwards it into `MissingKey`
  (`SchemaGetter.ts:387-389`); `forbidden` builds its own annotation record
  from a caller-supplied message (`:196`). Both are closed over at
  construction. Nothing reads annotations off a surrounding node.
- **Input retention is policy, not getter behaviour.** An issue keeps its input
  only when `reportInput` is true (`SchemaIssue.ts:151-163`, test at `:159`).

For `SC-GET-P-01` this fixes the denotation's argument list: an Effect4 getter
that takes a representation, a document, or an annotation environment would be
wider than the pin, and any such widening has to be declared as a deliberate
profile difference rather than as faithfulness.

## Pin: composition, and where the reversal is not

`Getter.compose(other)` runs `this` first and `other` second:
`this.run(oe, options)` then `other.run(ot, options)`
(`SchemaGetter.ts:82-90`, the composed body at `:89`). There is **no reversal
at the getter layer**. The reversal named by `E4-SCHEMA-CE-007` is introduced
one level up, by `Transformation.compose` (`SchemaTransformation.ts:159-164`);
`Effect4/Schema/Transformation.lean` owns that row and establishes which
direction is which.

The reason there is nothing to reverse here is that a getter has no direction
of its own. `Getter<out T, in E, R>` always means "from `E` to `T`"
(`SchemaGetter.ts:64`). The encode direction is not a different type — it is
the same type instantiated the other way round, which is why a transformation
pairs `decode : Getter<T, E, RD>` with `encode : Getter<E, T, RE>`
(`SchemaTransformation.ts:146-147`). Effect4 must not give the getter carrier
a direction tag; direction is a position in the pair.

Two facts about identity that `SC-GET-P-02` has to state precisely:

- Composition with the passthrough singleton is dropped, on either side
  (`SchemaGetter.ts:83-88`), so `id ∘ g = g` and `g ∘ id = g` hold at the pin
  by short-circuit rather than by a law about `run`.
- The test is **reference** identity on the `run` field —
  `getter.run === passthrough_.run` (`SchemaGetter.ts:205-207`) — against the
  one module-private singleton (`:203`). A user-written getter that behaves
  identically is not recognised. So the pin's identity behaviour is
  intensional. An Effect4 `SC-GET-P-02` stated extensionally over the
  denotation is a **stronger** claim than the pin's shortcut, not a
  transcription of it, and must be labelled as such.

## Pin: decode-only requirements do not reach encoding (`E4-SCHEMA-CE-006`)

The pin does separate the two directions, in the type indices:

- `Transformation<T, E, RD, RE>` carries `decode : Getter<T, E, RD>` and
  `encode : Getter<E, T, RE>` as independent fields with independent
  requirement indices (`SchemaTransformation.ts:143-147`).
- `Schema.decodeTo` threads them apart:
  `DecodingServices = To | From | RD` (`Schema.ts:5521`) and
  `EncodingServices = To | From | RE` (`Schema.ts:5522`). `RD` never appears in
  the encoding index and `RE` never in the decoding index.

The register's stated premise for `E4-SCHEMA-CE-006` is "Decode-only service
requirements also constrain encoding". The pin refutes it. But the row is a
real risk for Effect4 rather than a settled fact, for two reasons visible in
the same bytes:

1. **The separation is compile-time only.** At the runtime AST the indices are
   erased: a `Link` holds
   `Transformation<any, any, any, any> | Middleware<any, any, any, any, any,
   any>` (`SchemaAST.ts:401-405`), and an `Encoding` is a non-empty list of
   those links (`:432`, field at `:641`). No runtime value at the pin
   distinguishes a decode requirement from an encode requirement. Effect4
   cannot copy a runtime witness here; it has to construct the separation as a
   proof obligation over `Data.Row`.
2. **`flip` swaps the two indices.** `Transformation.flip` exchanges the
   getters and therefore `RD` with `RE` (`SchemaTransformation.ts:156-158`),
   and `Schema.flip` exchanges `DecodingServices` with `EncodingServices`
   (`Schema.ts:2708-2709`). A model that merged the two into one row
   `R = RD ∪ RE` would still satisfy flip-involution, so `SC-TR-02` cannot
   detect the merge. `E4-SCHEMA-CE-006` is the row that has to, and its witness
   must be an asymmetric one — a service used on exactly one side.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

Proof lane: `SC-GET-P-01` declaration and denotation, `SC-GET-P-02` identity,
`SC-GET-P-03` associative composition, `SC-GET-P-04` requirement weakening and
row union.

Flow lane: `SC-GET-F-01` through `SC-GET-F-07`. `SC-GET-F-07` is a
**negative** obligation: reification of an arbitrary `Program` is explicitly
not claimed, and that non-claim must be recorded rather than quietly omitted.

The pin sections above are inputs to these obligations and discharge none of
them. In particular they add three statements each owning packet must answer:

- `SC-GET-P-01` must decide whether the denotation admits a non-`Issue` exit,
  given the reachable-by-construction defect path recorded above.
- `SC-GET-P-02` must record that an extensional identity law is stronger than
  rc.112's reference-identity shortcut.
- `SC-GET-P-04` must state requirement growth as monotone, and must say
  explicitly that middleware is outside that law.

## Pin evidence for the first-order reification lane

One fact bears directly on `SC-GET-F-01` and `SC-GET-F-07`. Getter
constructors at the pin close over arbitrary host functions that are not
values of any schema: `parseJson` accepts a `reviver` callback passed straight
to `JSON.parse` (`SchemaGetter.ts:1027-1035`, use at `:1030`), and
`stringifyJson` accepts a `JsonReplacer` — a union whose first member is a
function (`SchemaGetter.ts:1047-1050`) — passed straight to `JSON.stringify`
(`:1087-1104`, use at `:1091`). These are host closures held inside a getter.
They are exactly the case `SC-GET-F-07` refuses to claim, and they confirm
that the admitted first-order Getter language must be a named subset with a
registry, not a projection of the rc.112 surface.

## Retains

- `E4-SCHEMA-CE-006` decode-only service does not leak into encode requirements
- `E4-SCHEMA-CE-016` middleware is not a value getter

Both rows' stated premises are refuted by the pinned bytes cited above. That
is evidence the rows are aimed at real distinctions; it is not a discharge.
Each still owes an Effect4-side witness against an Effect4 declaration, and
neither exists yet.

## Gated by

Proof lane: `P3-ALGEBRA-CLOSED` (met), `DATA-ROW-01/02/03` (open — see the
canonical row extraction section of `PORT-MANIFEST.md`), and `SC-ISSUE-01`
typed issue exit.

Ownership question, open: `SC-ISSUE-01` has no module. Schema issue, wire
issue, profile issue, Foldlab `IngestRefusal`, general Cause/Exit, cutover
refusal, and live frontier are all separate classifications by the ruling, and
none of them has a declared owner yet. Assign one before this lane opens. The
pin fixes the size of the first of those seven: the typed schema issue exit is
an 11-constructor alphabet (`SchemaIssue.ts:107-113`, `:142-149`), and it is
the only typed error a getter can raise (`SchemaGetter.ts:68`).

Flow lane: additionally `P4-FLOW-SEMANTICS-CLOSED`, which is open.
-/


## Archived host pin: Registry

/-!
# Schema.Registry.lean

Owner: Stable schema declarations and registered foreign meanings.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The open first-order declaration and check registry. Declarations and checks
carry open stable identifiers; closedness is *evidence* from a checked
registry or target profile, not a new constructor family.

This is why `Declaration` and the check nodes need no closed-world assumption
in `Effect4/Schema/Representation.lean`: the alphabet is closed, the registry
is open.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-REG-01` first-order declaration/check registry
- `SC-REG-02` uniqueness, arity, payload admission
- `SC-REG-03` denotation lookup agreement

`SC-REG-01` and `SC-REG-02` are also preconditions of the whole `SC-DEN-*`
family, so this module gates the denotation.

## Retains

- `E4-SCHEMA-CE-009` duplicate reviver identity

## Gated by

The payload carrier, since a registry row admits a payload.

## Host evidence at the pin

The reviver-resolution file cited throughout this section is
`internal/schema/fromRepresentation.ts`, SHA-256
`0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e`. It is
cited here and in `Effect4/Schema/Foreign.lean` but carried no digest in the
repository's pin block, so it is recorded at first use per the convention that
every cited host file gets one.

Read off rc.112 source; not executed here. The pinned bytes are host-local at
`library/effects/node_modules/effect/src/` in the Foldlab checkout and are not
vendored into this repository, so these citations are reproducible only on a
host carrying that package. Reading source establishes what the host *code
says*. It is not a runtime observation and it closes no `SC-REG-*` obligation.

The reviver record is three fields (`SchemaRepresentation.ts:502-510`): a
`string` `id`, a `payloadSchema` of type `Schema.Decoder<P>`, and a `revive`
function returning a host `Schema.Top` (`:509`). `FilterReviver` (`:518`) and
`FilterGroupReviver` (`:534`) repeat that three-field shape and differ only in
what `revive` receives and returns. `Reviver` is their union (`:558`) and
`AnyReviver` erases the payload parameter (`:566`).

The registry is **open in the host's own shape**, which is why the ownership
note above needs no closed-world assumption: revivers are supplied per call as
`fromRepresentation(document, { revivers })` (`:1236`, `:1260`), never as a
global table, and the host installs none implicitly (`:1212`, `:1250`).

Three facts bear directly on `SC-REG-02`:

- **Identifier uniqueness is enforced, eagerly and by position.**
  `internal/schema/fromRepresentation.ts:42` throws `Duplicate reviver for
  <id>` while building the reviver map, at path `["revivers", index, "id"]`.
  The check sits in map construction (`:34-50`), so it fires on a duplicate
  that no document ever mentions. This is a host witness for
  `E4-SCHEMA-CE-009`, not a proof about any Effect4 declaration.
- **Payload admission is decided by the payload schema, not by the row.**
  Each reviver's `payloadSchema` is rewrapped as `Schema.toCodecJson(...)` on
  entry to the map (`:46`), and a payload is admitted by
  `Schema.decodeUnknownResult` (`:105`), failing with `Invalid representation
  payload for <id>` (`:107`). The payload discipline is therefore carried by a
  schema, and a payload's wire form is JSON. The host reviver has no arity
  field; if Effect4 checks type-parameter arity, that is additional registry
  data and remains an open part of `SC-REG-02`.
- **Lookup is by `id` against that local map only.** `resolveReviver`
  (`:89-97`) reads `reviverMap.get(representation.id)` and throws `Missing
  reviver for <id>` (`:95`) on absence.

`SC-REG-03` denotation lookup agreement is untouched by all of the above.
These citations fix what the host does when a lookup fails; they say nothing
about agreement between a lookup and a denotation.
-/


## Archived host pin: Transformation

/-!
# Schema.Transformation.lean

Owner: Bidirectional effectful schema transformations.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

A transformation is a directional pair of getters. Its encoding composition
runs in **reverse** order; that asymmetry is the point of the type and is not
an implementation detail.

## Pin citation scope

Every `File.ts:NNN` citation in this module is a line of the installed
`effect@4.0.0-rc.112` sources on the build host, under
`library/effects/node_modules/effect/src/` in the Foldlab checkout — read-only
third-party evidence, never imported, vendored, or copied into this repository
as code. `docs/SCHEMA-CUTOVER.md` owns the digests. Two limits from that table
apply: `SchemaTransformation.ts`, `SchemaGetter.ts`, `SchemaAST.ts`, and
`SchemaParser.ts` byte-match the upstream semantic revision, so their line
numbers hold at both pins; `Schema.ts` does **not**, so every `Schema.ts:NNN`
below is a line of the installed package only and must be re-derived before
being quoted against the upstream revision.

This is pinned source reading, not a Lean theorem, a decoder result, an
executed test, or a claim that a future Effect4 carrier agrees with rc.112 on
any judgment.

## Pin: the exact transformation alphabet

`SchemaTransformation.ts` exports 46 names: two classes, one guard, seven
generic constructors, and 36 concrete library transformations.

```text
class Middleware<in out T, in out E, RDE, RDT, RET, REE>        :71
class Transformation<in out T, in out E, RD = never, RE = never> :143
isTransformation(u)                                             :195
make({ decode, encode })                                        :232
transformOrFail({ decode, encode })                             :286
transform({ decode, encode })                                   :335
transformOptional({ decode, encode })                           :388
passthrough / passthroughSupertype / passthroughSubtype   :714-716, :749, :783
```

The 36 concrete transformations, in source order: `trim` (`:431`),
`snakeToCamel` (`:470`), `toLowerCase` (`:508`), `toUpperCase` (`:546`),
`capitalize` (`:584`), `uncapitalize` (`:622`), `splitKeyValue` (`:665`),
`numberFromString` (`:821`), `bigintFromString` (`:858`), `dateFromString`
(`:894`), `dateFromMillis` (`:935`), `durationFromString` (`:973`),
`durationFromNanos` (`:1023`), `durationFromMillis` (`:1069`),
`errorFromJsonError` (`:1141`), `defectFromJson` (`:1148`), `optionFromNullOr`
(`:1188`), `optionFromUndefinedOr` (`:1230`), `optionFromNullishOr` (`:1274`),
`optionFromOptionalKey` (`:1324`), `optionFromOptional` (`:1370`),
`urlFromString` (`:1408`), `bigDecimalFromString` (`:1440`),
`uint8ArrayFromBase64String` (`:1490`), `stringFromBase64String` (`:1526`),
`stringFromBase64UrlString` (`:1561`), `stringFromHexString` (`:1596`),
`stringFromUriComponent` (`:1633`), `fromJsonString` (`:1672`), `fromFormData`
(`:1717`), `fromURLSearchParams` (`:1754`), `timeZoneOffsetFromNumber`
(`:1779`), `timeZoneNamedFromString` (`:1806`), `timeZoneFromString`
(`:1847`), `dateTimeUtcFromString` (`:1888`), `dateTimeZonedFromString`
(`:1928`).

**Decode and encode are separate fields, not one invertible object.** The
class body is exactly two independently typed getters:

```text
readonly decode : SchemaGetter.Getter<T, E, RD>      :146
readonly encode : SchemaGetter.Getter<E, T, RE>      :147
```

with no relation imposed between them anywhere in the class
(`SchemaTransformation.ts:143-165`). `make` takes an arbitrary such pair and
wraps it, with no check (`:232-240`). The method surface is exactly `flip`
(`:156-158`) and `compose` (`:159-164`) — there is no `invert`, no `run`, and
no law hook. The four-index shape recorded in `docs/SCHEMA-CUTOVER.md`
(`Transformation decoded encoded decodeRequirements encodeRequirements`) is a
line-for-line match to `:143`.

`Middleware` is in the same file and the same `Link` position
(`SchemaAST.ts:401-405`) but is not a transformation: it has six indices
(`:71`) and takes whole effects rather than values (`:73-80`).
`Effect4/Schema/Getter.lean` owns that distinction and its
`E4-SCHEMA-CE-016` evidence.

## Pin: totality, partiality, and effect status, per direction

Each direction is an independent getter, so each direction independently
carries the whole getter effect surface — typed `Issue` failure, an `R`
requirement index, and the possibility of asynchrony
(`SchemaGetter.ts:64-68`). The three generic constructors fix the pair jointly
at three different points on that scale:

```text
transform         both directions pure and total     :335-338
transformOptional both directions total on Option    :388-391
transformOrFail   both directions effectful, RD and RE separate  :286-289
```

**The two directions can differ, and the pin ships witnesses.** Three kinds:

1. *Partial one way, total the other.* `uint8ArrayFromBase64String` pairs a
   fallible decode with a total encode: `SchemaGetter.decodeBase64()`
   (`SchemaTransformation.ts:1491`), which is a `transformOrFail` mapping a
   failed `Result` to an `InvalidValue` issue (`SchemaGetter.ts:1329-1341`),
   against `SchemaGetter.encodeBase64()` (`:1492`), which is a plain
   `transform` (`SchemaGetter.ts:1249-1251`).
2. *Lossy one way, identity the other.* `trim` pairs `SchemaGetter.trim()`
   with `SchemaGetter.passthrough()` (`SchemaTransformation.ts:431-436`); see
   the `E4-SCHEMA-CE-005` section below.
3. *Total one way, refusing the other, on host-representability grounds.*
   rc.112's symbol link decodes a string into a global symbol with a total
   `transform` calling `Symbol.for` (`SchemaAST.ts:4091`), and encodes a symbol
   back with a `transformOrFail` that raises
   `Forbidden("cannot serialize to string, Symbol is not registered")` whenever
   `Symbol.keyFor` returns `undefined` (`SchemaAST.ts:4092-4103`, test at
   `:4093-4094`, refusal at `:4097-4102`). This is also the pin-side witness
   shape for `E4-SCHEMA-CE-010`, a row this module does not own.

**Requirements do not have to match either.** `RD` and `RE` are separate
indices (`SchemaTransformation.ts:143`, `:146-147`) and `compose` unions them
separately: `RD | RD2` and `RE | RE2` (`:159`). At the schema level
`Schema.decodeTo` keeps them apart — `DecodingServices` takes `RD`
(`Schema.ts:5521`) and `EncodingServices` takes `RE` (`Schema.ts:5522`).

Scope note. No transformation shipped in `SchemaTransformation.ts` at this pin
instantiates `RD` or `RE` to anything but `never`; the separation is exercised
by the type signatures and by `decodeTo`, not by a first-party example in this
file. An Effect4 witness for the asymmetry therefore has to be authored, not
lifted.

## Pin: `SC-CODEC-*` directionality has no runtime round-trip law

**No round-trip law is stated as a law, and none is enforced.** Concretely, at
this pin:

- The `Transformation` class imposes no relation between `decode` and `encode`
  (`SchemaTransformation.ts:143-165`), and `make` accepts any pair without a
  check (`:232-240`).
- Neither `SchemaGetter.ts` nor `SchemaTransformation.ts` contains the word
  "law" anywhere.
- Round-trippability is asserted only in prose, per constructor, and the pin
  contradicts a universal reading of it four times in its own doc comments:
  `trim` "is not round-trippable if the original had whitespace" (`:410-411`),
  `toLowerCase` "is not round-trippable if the original had uppercase
  characters" (`:489`), `toUpperCase` the mirror (`:527`), and `splitKeyValue`
  round-trips only "when keys and values do not contain the separators"
  (`:643`). Positive prose claims are equally informal: `snakeToCamel` (`:451`)
  and `durationFromString` (`:953`).
- The one place rc.112 *names* an isomorphism does not check it. `toIso` builds
  `Optic_.makeIso(encodeSync, decodeSync)` directly from the two directions
  (`Schema.ts:16593-16596`), and its own documentation warns that failing,
  asynchronous, or service-dependent transformations throw there
  (`Schema.ts:16584-16588`).

So directionality at the pin is structural — two typed fields and a fixed
composition order — while round-tripping is a per-transformation convention
documented in prose. That is exactly the shape `docs/SCHEMA-CUTOVER.md` fixes
in its codec law classification: a per-codec proof status rather than a blanket
theorem. The pin corroborates that ruling and supplies no law to port.

## Pin: composition direction (`E4-SCHEMA-CE-007`)

`Transformation.compose` is four lines and settles the direction question:

```text
compose<T2, RD2, RE2>(other : Transformation<T2, T, RD2, RE2>)
    : Transformation<T2, E, RD | RD2, RE | RE2>          :159
  new Transformation(
    this.decode.compose(other.decode),                   :161
    other.encode.compose(this.encode)                    :162
  )
```

Reading off the indices at `:159` fixes which direction is which. With
`this : Transformation<T, E, ...>` and `other : Transformation<T2, T, ...>`:

- the **decode** path runs `E -> T -> T2`, so it composes in argument order,
  `this.decode` then `other.decode` (`:161`);
- the **encode** path runs `T2 -> T -> E`, so it composes in the **reversed**
  order, `other.encode` then `this.encode` (`:162`).

`SchemaGetter.Getter.compose` itself performs no reversal — it is plain
forward composition of `run` (`SchemaGetter.ts:82-90`, body at `:89`). The
reversal is introduced here and nowhere else. Note also that `Middleware` has
no `compose` at all (`SchemaTransformation.ts:71-98`), so this equation is
specific to the value-level pair.

This matches the equations already frozen in `docs/SCHEMA-CUTOVER.md`,

```text
(f then g).decode = f.decode then g.decode
(f then g).encode = g.encode then f.encode
```

with `f = this` and `g = other`. The register's stated premise for
`E4-SCHEMA-CE-007` is "Transformation encodings compose in decoder order"; the
pin refutes it at `:162`. `SC-TR-03` must be stated over an **order-sensitive**
pair, because the two orders agree on any commuting pair and such a witness
would not detect the defect.

## Pin: `E4-SCHEMA-CE-005`, trim refutes a universal round trip

```text
trim() : Transformation<string, string>                :431
  new Transformation(
    SchemaGetter.trim(),                               :433
    SchemaGetter.passthrough()                         :434
  )
```

`SchemaGetter.trim()` is `transform(Str.trim)` (`SchemaGetter.ts:840-842`) —
total, pure, and not injective on `string`. `SchemaGetter.passthrough()` is the
identity singleton (`SchemaGetter.ts:246-250`, `:203`). So decode is
non-injective and encode is the identity, and `encode ∘ decode` is not the
identity on any input with leading or trailing whitespace. rc.112 states the
consequence itself at `SchemaTransformation.ts:410-411`.

Note that the failure is directional. It is `encode ∘ decode` that is not the
identity on inputs carrying whitespace; the opposite composite `decode ∘
encode` restricted to already-trimmed strings is a separate question, and
whether it is the identity depends on idempotence of the host `String.trim`,
which the pinned Effect bytes do not state and which is not established here.
This is why `docs/SCHEMA-CUTOVER.md` splits the classification into left
inverse and right inverse rather than one round-trip row, and why the
`SC-CODEC-07` witness for this row must name **which** inverse fails, on which
domain, and under which host assumption.

The register's stated premise for `E4-SCHEMA-CE-005` is "Every transformation
has an unqualified encode/decode round trip". The pin refutes it, and `trim`
is not the only refutation available — `toLowerCase` (`:508`, doc `:489`) and
`toUpperCase` (`:546`, doc `:527`) refute it the same way, so the Effect4
witness may be chosen for convenience rather than because `trim` is the unique
counterexample.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-TR-01` transformation declaration
- `SC-TR-02` flip involution
- `SC-TR-03` reversed encoding composition
- `SC-TR-04` composition associativity

Three statements the pin sections add to these packets:

- `SC-TR-02` is definitional at the pin: `flip` is
  `new Transformation(this.encode, this.decode)`
  (`SchemaTransformation.ts:156-158`), so double flip restores the field pair
  but allocates a fresh object. The Effect4 statement is therefore an equality
  of the two fields, not of the carrier, until a canonical normalizer exists.
  `Middleware.flip` has the identical shape (`:95-97`), so flip-involution
  alone does not separate the two carriers and cannot serve as an
  `E4-SCHEMA-CE-016` witness.
- `SC-TR-03` needs an order-sensitive witness, per the composition section.
- `SC-TR-04` associativity is not visible at the pin. `compose` is not
  associative by construction there; associativity would follow from
  associativity of `Getter.compose`, which is itself perturbed by the
  passthrough short-circuit (`SchemaGetter.ts:83-88`). Not established at the
  pin; it is an Effect4 obligation over the Effect4 denotation.

## Retains

- `E4-SCHEMA-CE-007` encoding composition is reversed
- `E4-SCHEMA-CE-005` trim refutes universal round trip

Both rows' stated premises are refuted by the pinned bytes cited above. That
is evidence the rows attack real distinctions; it is not a discharge. Each
still owes an Effect4-side witness against an Effect4 declaration, and neither
exists yet.

No universal round-trip law is assigned to all transformations. Lossy
transforms are part of the source surface, so a round-trip claim is a
per-codec classification and never a blanket theorem.

## Gated by

The getter proof lane, hence `DATA-ROW-01/02/03` and `SC-ISSUE-01`.

`DATA-ROW-02` is load-bearing here specifically because `compose` unions the
two requirement rows **separately** (`SchemaTransformation.ts:159`); a single
merged row would satisfy `SC-TR-02` and still be wrong, which is the risk
`E4-SCHEMA-CE-006` guards and `Effect4/Schema/Getter.lean` records.
-/


## Archived host pin: Value

/-!
# Schema.Value.lean

Owner: Decoded and encoded value interpretations.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The document-relative relational denotation. The ruling is explicit that this
is **not** a partial function `Representation -> Type`: overlapping unions,
enum aliases, recursive references, and declarations are not faithfully
modelled by one total function. The judgments are

```text
Gamma |- representation represents T
Gamma |- representation accepts value
```

where `Gamma` owns document references and registry evidence.

## Pin citation scope

Every `File.ts:NNN` citation in this module is a line of the installed
`effect@4.0.0-rc.112` sources on the build host, under
`library/effects/node_modules/effect/src/` in the Foldlab checkout — read-only
third-party evidence, never imported, vendored, or copied into this repository
as code. `docs/SCHEMA-CUTOVER.md` owns the digests. Two limits from that table
apply: `SchemaAST.ts`, `SchemaGetter.ts`, `SchemaTransformation.ts`, and
`SchemaRepresentation.ts` byte-match the upstream semantic revision, so their
line numbers hold at both pins; `Schema.ts` does **not**, so every
`Schema.ts:NNN` below is a line of the installed package only and must be
re-derived before being quoted against the upstream revision.

This is pinned source reading, not a Lean theorem, a decoder result, an
executed test, or a claim that a future Effect4 carrier agrees with rc.112 on
any judgment.

## Pin: what "value" is at this layer, and what it is not

At the pin a schema exposes three **type-level** value positions and one
runtime description, all on the same interface:

```text
readonly "ast"      : SchemaAST.AST          Schema.ts:789
readonly "Type"     : unknown                Schema.ts:791   the decoded value
readonly "Encoded"  : unknown                Schema.ts:792   the encoded value
readonly "Iso"      : unknown                Schema.ts:799   an intermediate form
```

Same four on `Bottom`, the concrete base: `ast` (`:170`), `Type` (`:174`),
`Encoded` (`:175`), `Iso` (`:182`).

Three consequences for `SC-DEN-01`.

**1. Decoded and encoded have no runtime witness at the pin.** `Type` and
`Encoded` are phantom index fields on a TypeScript interface. The only value
that exists at runtime is the `ast`, and at the point where transformation is
actually stored the value indices are erased to `any`: a `Link` holds
`Transformation<any, any, any, any> | Middleware<any, any, any, any, any,
any>` (`SchemaAST.ts:401-405`), chained as a non-empty `Encoding` (`:432`,
node field at `:641`). So rc.112 offers **no** runtime object that
distinguishes a decoded value from an encoded one. Effect4 cannot lift such a
witness; the decoded/encoded distinction has to be carried by the judgment,
which is the reason `Accepts` is relational rather than a lifted host
predicate.

**2. There is a third value index, `Iso`, that the frozen Effect4 model has no
slot for.** `Iso` is described as the schema's intermediate or serialized form,
and `toIso` builds an optic between `Type` and `Iso`
(`Schema.ts:16593-16596`). It is threaded through every derived schema
interface (for example `decodeTo` at `:5525`, `middlewareDecoding` at
`:5286`), and `Optic<T, Iso>` is a fifth erased view alongside `Codec`
(`:1041`), `Decoder` (`:1064`), `Encoder` (`:1087`) and `Schema` (`:941`),
pinning both service indices to `never` (`Schema.ts:1141-1145`). Recorded as an
open scope question for `SC-DEN-01`: either `Iso` is declared out of the
Effect4 profile explicitly, or the four-index model in
`docs/SCHEMA-CUTOVER.md` is short one position. Not resolved here.

**3. The Representation layer is a description of the schema, not of a
value.** `Representation` is the persisted alphabet owned by
`Effect4/Schema/Representation.lean` and censused in
`docs/SCHEMA-CUTOVER.md`. At the pin it reaches a schema only as an annotation
carrying an id and a JSON payload — for example
`Declaration.representation?: SchemaRepresentation.RepresentationAnnotation`
(`Schema.ts:17157-17159`), and `SchemaAST.Json`'s own annotation
`{ id: "effect/schema/Json", payload: null }` (`SchemaAST.ts:4359-4362`). So
the layering at the pin is: `ast` is the live description, `Representation` is
the persisted description, and `Type`/`Encoded`/`Iso` are indices over host
values that no carrier holds. Three descriptions of two different kinds, not
one triple.

The `ast` is emphatically not the persisted description. `SchemaAST.Suspend`
holds `thunk : () => AST`, a host function (`SchemaAST.ts:3144-3146`), while
persisted `Suspend` holds a nested `Representation`
(`SchemaRepresentation.ts:988`). A declaration parser is a function
(`SchemaAST.ts:666-668`) and a check is a function (`SchemaAST.ts:3209`). This
is the direct evidence for the cutover ruling that rc.112's `SchemaAST.AST` is
not persisted Schema content.

## Pin: value carriers that hold non-first-order host values

This is a hard boundary for this repository, so the answer is given by name.
At this pin the following schemas admit a decoded value that is a host
function, promise, class instance, or symbol.

```text
Schema.Any            Bottom<any, any, ...>        :3065 / :3074
Schema.Unknown        Bottom<unknown, unknown, ...> :3082 / :3096
Schema.ObjectKeyword  Bottom<object, object, ...>  :3269 / :3278
Schema.Symbol         Bottom<symbol, symbol, ...>  :3200 / :3209
Schema.UniqueSymbol   Bottom<sym, sym, ...>        :3286 / :3307
Schema.instanceOf(C)  decoded value is `u instanceof C`  :6571-6576
```

Notes that make each precise:

- `Any` and `Unknown` set **both** `Type` and `Encoded` to a top type, so a
  function, a promise, or a class instance is admissible on the encoded side
  too, not only the decoded side.
- `ObjectKeyword` explicitly includes functions. Its documented predicate is
  `typeof value === "object" && value !== null || typeof value === "function"`
  (`Schema.ts:3273`), and rc.112's union-candidate table lists its types as
  `["object", "array", "function"]` (`SchemaAST.ts:2634-2635`). An `Objects`
  node with no property signatures and no index signatures spans `"function"`
  as well (`SchemaAST.ts:2636-2639`).
- `Symbol` and `UniqueSymbol` put a raw host `symbol` in **both** the decoded
  and the encoded position (`Schema.ts:3200`, `:3286-3288`). That is a
  non-first-order host value on the persisted-facing side.
- `instanceOf` closes over a host constructor and reduces to `declare` with an
  `instanceof` predicate (`Schema.ts:6571-6576`). Its first-party uses at this
  pin are `URL` (`:12090`), `File` (`:12824`), `FormData` (`:12920`),
  `URLSearchParams` (`:13097`), and `Uint8Array` (`:13605`); `Date` (`:12218`)
  and `Duration` (`:12369`) use `declare` directly.
- **Promises.** There is no promise-valued schema at this pin. A promise
  reaches a value position only through `Any`, `Unknown`, `ObjectKeyword`, or
  a user-written `instanceOf(Promise)`. Recorded as a negative finding, from
  reading the exported schema constructors of `Schema.ts`; it is not a proof
  that no such schema can be written.

Two neighbouring host-closure facts that are **not** values but bound the same
boundary: a getter can close over a host function without any schema holding
one, since `parseJson` takes a `reviver` (`SchemaGetter.ts:1027-1035`) and
`stringifyJson` takes a `JsonReplacer` whose first member is a function
(`SchemaGetter.ts:1047-1050`); and the persisted `UniqueSymbol` codec field is
typed `Schema.Symbol` (`SchemaRepresentation.ts:1013`), so even the persisted
representation carrier is not itself JSON until a further codec step runs.
`Effect4/Schema/Getter.lean` owns the first; `Effect4/Schema/Representation.lean`
owns the second.

Consequence for this module. `SC-DEN-01` cannot state
`Gamma |- representation accepts value` over a host-value universe. The Effect4
value universe has to be declared as a named first-order subset with these
carriers excluded, and every exclusion above is a deliberate profile narrowing
against rc.112 — the same directional claim-scope rule the cutover ruling
already fixes: Effect4-admitted implies host-accepted, never the converse.

## Pin: what `Schema.Json` constrains

`Schema.Json` is a `Codec<Json>` (`Schema.ts:16807-16812`) over the type
`null | number | boolean | string | JsonArray | JsonObject`
(`Schema.ts:16773`, `:16781`, `:16789-16791`). Its AST is a `Declaration`
whose parser is `isJson` (`SchemaAST.ts:4352-4366`), and `isJson` is
`isTree(u, isJsonLeaf)` (`:4347-4349`).

The leaf predicate is four lines and decides most of the question:

```text
isJsonLeaf(u) =
  u === null || typeof u === "string" || typeof u === "boolean" ||
  (typeof u === "number" && Number.isFinite(u))     SchemaAST.ts:4271-4274
```

The tree walk adds the rest (`SchemaAST.ts:4280-4337`): a non-array object
passes only when its prototype is `null`, is `Object.prototype`, or is itself
a null-prototype object — the cross-realm plain-object case (`:4297-4308`);
a node already on the current path fails, so a cycle is refused (`:4310`, with
the doc statement at `:4343`); a node already fully validated is reused, so
DAG sharing is **accepted** (`:4291-4292`); and array slots are read by index
against the array's length snapshot (`:4313`, `:4322-4326`).

Taking the named cases one at a time:

```text
NaN         refused    Number.isFinite fails            :4273
Infinity    refused    same                             :4273
-Infinity   refused    same                             :4273
-0          ACCEPTED   Number.isFinite(-0) is true      :4273
undefined   refused    no `undefined` disjunct          :4271-4274
sparse array refused   a hole reads as `undefined`,
                       and `undefined` is not a Json leaf :4324-4325 + :4271
duplicate keys  not representable at this layer at all
```

Three of these need their scope named rather than asserted flatly.

**`-0`.** The predicate accepts it; that is all the pinned Effect bytes decide.
Whether `-0` survives a JSON string round trip is host `JSON` behaviour, not an
Effect fact, and it is not established here. What the pin does show is that the
serializing step is a getter over host `JSON`: `stringifyJson` calls
`JSON.stringify` (`SchemaGetter.ts:1087-1104`, call at `:1091`) and `parseJson`
calls `JSON.parse` (`:1027-1035`, call at `:1030`). Any Effect4 claim about
`-0` therefore belongs to the wire packet with a host-behaviour assumption
named, not to `SC-DEN-01`.

**Sparse arrays.** rc.112 comments the decision itself: "A sparse slot is read
as `undefined`; the leaf predicate determines whether that is valid for the
current tree" (`SchemaAST.ts:4324-4325`). Since `undefined` is not a JSON leaf,
a sparse array fails `Schema.Json`. The same walk with a different leaf
predicate reaches the opposite verdict: `isStringTreeLeaf` accepts `undefined`
(`SchemaAST.ts:4276-4278`), so `Schema.StringTree` (`Schema.ts:15986`,
`SchemaAST.ts:4400-4402`) accepts sparse arrays. The two tree carriers differ
on exactly one leaf case, and Effect4 must not conflate them.

**Duplicate keys.** They are not refused at this layer; they are already gone.
`Schema.Json` is a predicate over an already-constructed host object, and the
walk enumerates with `Object.keys` (`SchemaAST.ts:4313`), which cannot report a
repeat. The construction happens earlier, in `JSON.parse`
(`SchemaGetter.ts:1030`). This corroborates the raw-JSON ruling in
`docs/SCHEMA-CUTOVER.md` and is the pin-side statement of
`E4-SCHEMA-CE-012`'s premise: by the time any Schema value exists, duplicate
evidence has been discarded. That row belongs to the document/wire packet, not
to this module.

Also refused by the same predicate, with no separate rule needed: `bigint`,
`symbol`, functions, promises, and class instances — none satisfies
`isJsonLeaf` and none survives the prototype gate at `:4297-4308`. `Schema.Json`
is therefore the pin's own narrowing of the previous section's host-value
carriers, and it accepts sharing while refusing cycles — a distinction Effect4's
value denotation must decide explicitly, because a shared subtree and its tree
unfolding are different host graphs that `Schema.Json` cannot tell apart.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-DEN-01` representation/type/value judgments
- `SC-DEN-02` primitive/product/array/object semantics
- `SC-DEN-03` ordered anyOf theorem
- `SC-DEN-04` exactly-one oneOf theorem
- `SC-DEN-05` enum-alias relation
- `SC-DEN-06` document-relative references
- `SC-DEN-07` recursive evaluator soundness
- `SC-DEN-08` evaluator completeness for the named guarded profile

Three statements the pin sections add to `SC-DEN-01` before it can be frozen:

- the value universe must be a declared first-order subset, because the pin's
  own carriers admit functions, symbols, and class instances by name;
- the `Iso` index must be either adopted or explicitly excluded from the
  profile; and
- sharing versus cyclicity must be decided, since `Schema.Json` separates them
  (`SchemaAST.ts:4291-4292` against `:4310`) while a first-order Lean value
  cannot express sharing at all.

## Retains

- `E4-SCHEMA-CE-001` overlapping anyOf chooses first success
- `E4-SCHEMA-CE-002` overlapping oneOf rejects multiple successes
- `E4-SCHEMA-CE-003` enum aliases defeat encode injectivity

## Not a termination claim

`SC-DEN-07` and `SC-DEN-08` must not be worded as termination results. Vendored
commentary reports documents that pass guardedness while Effect's validator
diverges, but the executable witness remains an open `SC-DOC-06` obligation.
An evaluator soundness result here is about agreement with the judgment, not
about the evaluator halting.

The pin sharpens why. `SchemaAST.Suspend.thunk` is `() => AST`
(`SchemaAST.ts:3144-3146`) — a delay, not a constructor — and `Suspend`
refuses to carry checks at all, throwing on construction
(`SchemaAST.ts:3156`, and again at `:3475`). A guarded document can therefore
still fail to produce a value, which is exactly the productivity-versus-
guardedness gap `SC-DOC-06` owns.

## Why a relation and not a function

`vendor/foldlab/pinned/tree/library/cas/Cas/Schema/El.lean:187-192` is useful
prior-art pressure against simply porting Foldlab's closed type function.
Five of its fourteen constructors map to `Empty` unconditionally: `.decl`
(`:187`), `.enum` (`:189`), `.tuple` (`:190`), `.reference` (`:191`), and
`.susp` (`:192`). A sixth, `.union` (`:188`), is *conditional* —
`cond (discriminatedB ms) (ElMembers ms) Empty` — so a discriminated union is
interpreted and only an undiscriminated one is not. That shows those cases are
uninterpreted by Foldlab's particular `El`; it does not prove that every
faithful rc.112 model must be relational, nor that the cases transfer
exhaustively. The conditional row is the sharper piece of prior art: it is a
type function that already needs a decidable side condition to stay total,
which is itself pressure toward a relation.

The native contract must justify the relational judgment directly from the
source phenomena it intends to preserve, including registry dependence,
ordered overlapping unions, enum aliases, variable-length tuples, and
document-relative references. The Foldlab mapping is a warning against an
unexamined port, not an impossibility theorem.

The pin adds one independent pressure, from rc.112 rather than from Foldlab.
Union member selection is not a type function: `toCandidate` walks the encoding
chain and answers `unknown` — "cannot narrow" — for a `Suspend` node
(`SchemaAST.ts:2601`) and for any middleware link with a non-identity decode
(`:2607-2609`). A carrier that computed a single type per representation would
have to invent an answer at exactly the two places rc.112 declines to give one.

## Gated by

`SC-REP-CLOSED` and `SC-DOC-CLOSED` plus `SC-REG-01` and `SC-REG-02`. All four
are open.

`SC-WIRE-06` `normalization_preserves_denotation` waits on `SC-DEN-01` and is
not a well-formed statement until the judgment above is frozen. Proving
normalization idempotent licenses no preservation claim.
-/

