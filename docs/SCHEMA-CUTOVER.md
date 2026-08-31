# Schema cutover ruling

Status: frozen design input; the six tag declarations and their local proof
receipts are implemented, but their generated assurance join and the payload
carrier remain cutover-open, 2026-08-31.

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
- `SCHEMA-PG-DOCUMENT` owns reference interpretation, reachability,
  guardedness, and productivity. The plain `Document` and `MultiDocument`
  record declarations are leaves until those meanings are attached.
- `SCHEMA-PG-WIRE` owns duplicate-preserving raw data, decoding,
  canonicalization, and encoding. Finite host fixtures attach as receipts;
  they do not receive graphs.
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

- **Tag declarations — implemented with local receipts; cutover closure
  open.** The six exact type rows, their one-parent-graph/five-leaf allocation,
  and their native contract origins are recorded in `PORT-MANIFEST.md`.
  `test/contracts/schema-representation.contract.md` and
  `test/contracts/schema-subalphabets.contract.md` are the frozen breaker
  packets, preserved separately in commit `f487774`, with counterexamples
  `E4-SCHEMA-CE-017` through `E4-SCHEMA-CE-022`. The implementation, axiom
  report, lexical source evidence, and bounded mutation receipt are present.
  The six rows and required parent-graph edges remain open until those inputs
  are joined mechanically by the generated assurance check; this document
  does not discharge `SC-REP-02` or `SC-REP-03`.
- **Payload and field admission — Pass-B frozen; implementation
  required-blocked.** The frozen
  D0-D6 structural slice and D7 recursive-admission slice are intentionally
  the only two graph-bearing families in this packet. The module DAG is
  `Data.Json` (D0-D1) -> `Schema.Payload` (D2-D3) ->
  `Schema.Representation` (D4-D5) -> `Schema.Document` (D6) ->
  `Schema.Check` (D7); `Schema.Value` owns later denotation only. The clean-red
  diagnostic receipt and the mechanical reaction gate are present. The latter
  kills an ordinary extra constructor, an uninhabited extra constructor, a
  constructor permutation, a field-type drift, and a declaration-free upward
  `Schema.Value` import. Its fixed production half also materializes
  the packet's `payloadBoundaryImportProbe` from an isolated module whose only
  library import is `Effect4.Schema.Payload`: D0-D3 must resolve, D4-D7 must
  remain unreachable, ownership inspection must assign D0-D1 to
  `Effect4.Data.Json` and D2-D3 to `Effect4.Schema.Payload`, and an upward
  Payload import must be rejected. That production half remains intentionally
  red until the builder creates `Schema.Payload` and moves D2-D3 into it; it is
  the exact implementation-admission blocker. This is a finite
  surface/ownership receipt, not a third proof graph. Cutover and semantic
  closure remain open. Reserved
  `E4-SCHEMA-CE-*` rows remain reservations until the owning packet supplies
  the exact executable or immutable witness; a reservation is not a
  discharged obligation.

The pinned bytes needed by `SC-REP-CENSUS-PIN` are on the build host at
`library/effects/node_modules/effect/src/SchemaRepresentation.ts` in the
Foldlab checkout, verified at SHA-256
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

**It is host-local.** The pinned file is not vendored into this repository and
`lake build` does not invoke the gate. Re-verifying needs a local
`effect@4.0.0-rc.112` install with the path passed by hand. This is not a
Foldlab dependency — the evidence is a third-party npm package identified by
digest that happens to sit under a Foldlab checkout on this host — but it is
not reproducible from this checkout alone.

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

WITNESS: `E4-SCHEMA-CE-040` in `test/counterexamples/REGISTER.md`.

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
