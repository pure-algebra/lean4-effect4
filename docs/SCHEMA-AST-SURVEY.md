# Live SchemaAST survey and its map to the persisted representation

Status: pinned source-reading evidence, 2026-08-31. No Lean declaration, no
theorem, no cutover status, and no executed runtime probe is created by this
document. It is a survey of the **live** side of the Schema boundary, which the
repository record had described only negatively.

The frozen persisted side is owned by the census table in
`docs/SCHEMA-CUTOVER.md` and by `Effect4/Schema/Representation.lean`. This
document does not restate, amend, or discharge any row there. It establishes
what sits on the other side of the arrow, and what the arrow loses.

## What this document is, and is not

It is a **lexical and type-level reading of fixed bytes**. Every claim carries
a `SchemaAST.ts:NNN`, `toRepresentation.ts:NNN`, or `SchemaRepresentation.ts:NNN`
citation into the files hashed below. Where a claim cannot be cited it is marked
"not established at the pin".

Nine shell extractions were run over one byte-state on one host (darwin
25.2.0): four census routes, one case-label extraction, three set differences,
and one digest sweep. **Zero programs were executed against the Effect
runtime.** Every behavioural statement below is read off source, not observed.
Executable host evidence remains owed by `SC-HOST-03` and `SC-HOST-04`.

The words "sound", "equivalent", "preserves", "fully reified", and "complete"
do not appear as verdicts anywhere below.

## Bytes read

All paths are relative to `library/effects/node_modules/effect/src/` in the
Foldlab checkout on the build host. Foldlab is not a dependency of this
repository; this is a third-party npm package identified by digest that happens
to live under that checkout. `vendor/foldlab/` is read-only evidence and was
not modified.

```text
SchemaAST.ts
  7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8  [PIN MATCH]
SchemaRepresentation.ts
  a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc  [PIN MATCH]
Schema.ts
  9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784  [INSTALLED, OFF UPSTREAM]
SchemaGetter.ts
  a2f2c85c41eceb1e8092ca15fd6ded1ac90c23a4c44be610200d3feefe1d6682  [PIN MATCH]
SchemaTransformation.ts
  4050859c4d340b3580c5e58aceeb9984339eed1dfadb1a2e86f18a9c0ac110f5  [PIN MATCH]
internal/schema/toRepresentation.ts
  677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2  [NOT IN ANY AUTHORITY PIN TABLE]
internal/schema/annotations.ts
  4b3bedcae279fcb3a1dff4e8eb718d42f450d59c8b45912070a586adcdcb077c  [NOT IN ANY AUTHORITY PIN TABLE]
```

Digest reconciliation:

- `SchemaAST.ts`, `SchemaRepresentation.ts`, `SchemaGetter.ts`, and
  `SchemaTransformation.ts` each match a digest already carried in the
  `docs/SCHEMA-CUTOVER.md` authority table, whose rows for those four files
  read `same` in the installed column and are ruled `byte match`.
- `Schema.ts` matches the *installed* digest that `PORT-MANIFEST.md` records
  with the note that "an upstream tag does not prove what a package manager
  placed on disk". Every `Schema.ts:NNN` citation below is a citation of the
  installed bytes only.
- `internal/schema/toRepresentation.ts` and
  `internal/schema/annotations.ts` now have explicit installed-byte rows in
  `PORT-MANIFEST.md`. This survey identified the gap while it was being
  drafted; the retained authority table is the current owner. The hashes here
  independently agree with those rows. Neither installed-byte row establishes
  upstream equality until a resolved upstream comparison is recorded.

## 1. The live AST census

### 1.1 The count

**Twenty-one.** The live `SchemaAST.AST` alphabet has 21 node variants at the
pin.

### 1.2 Four independent lexical routes, and their agreement

| Route | Site | Members |
| --- | --- | ---: |
| A — closed type union | `SchemaAST.ts:53-74`, `export type AST =` | 21 |
| B — class declarations | 21 sites matching `class X extends Base` | 21 |
| C — narrowing guards | 21 sites matching `makeGuard("X")`, factory at `SchemaAST.ts:76-78` | 21 |
| D — tag literals | 23 sites matching `readonly _tag = "X"`, minus 2 | 21 |

Routes A, B, and C are **set-identical**. The extraction of route A was
diffed against route C and produced no output; the extraction of route A was
diffed against route B's class-name list and produced no output.

Route D is the one that needs a stated restriction, and the restriction is
what makes it independent rather than circular. There are 23 `readonly _tag =`
literals in the file. Two of them — `Filter` (`SchemaAST.ts:3208`) and
`FilterGroup` (`SchemaAST.ts:3256`) — belong to classes that extend
`Pipeable.Class`, not `Base` (`SchemaAST.ts:3207`, `:3255`). They are the
`Check` family, `export type Check<T> = Filter<T> | FilterGroup<T>`
(`SchemaAST.ts:3290`), which is a *separate* alphabet carried on
`Base.checks` (`SchemaAST.ts:640`). Restricting route D to subclasses of
`Base` (`SchemaAST.ts:636`) yields exactly route A's 21.

**The routes agree.** The disagreement that route D exposes before restriction
is the same class of trap the repository already recorded on the persisted
side, where harvesting `readonly _tag: "X"` yielded a spurious 23rd name
`Import` from `Artifact`. Here the spurious names are `Filter` and
`FilterGroup`, and the discriminator is the superclass, not the annotation.

This is a **membership census**. Route A's source order is preserved in the
table below for citation convenience; no claim about parser precedence,
decode order, or union member preference follows from it, and no observation
below reads a variant's position.

The assumption a lexical extraction cannot check about itself is named here:
that `export type AST` at `SchemaAST.ts:53` is the live alphabet. It is
corroborated by `isAST` (`SchemaAST.ts:92-93`), which admits any value
carrying the module-private `TypeId` brand (`SchemaAST.ts:614`, installed on
`Base` at `:637`) — a *wider* test than the union, so a subclass of `Base`
declared outside this file would pass `isAST` and not appear in any route.
No such subclass exists in the pinned file. Whether one exists elsewhere in
the package is **not established at the pin**.

### 1.3 The shared base

Every variant extends `Base` (`SchemaAST.ts:636-656`) and inherits four
fields plus the brand:

| Field | Type | Line |
| --- | --- | --- |
| `[TypeId]` | `"~effect/Schema"` | `:637` (constant at `:614`) |
| `_tag` | `string`, abstract | `:638` |
| `annotations` | `Schema.Annotations.Annotations \| undefined` | `:639` |
| `checks` | `Checks \| undefined` | `:640` (type at `:612`) |
| `encoding` | `Encoding \| undefined` | `:641` (type at `:432`) |
| `context` | `Context \| undefined` | `:642` (class at `:576`) |

`Checks` is a non-empty array of `Check` (`SchemaAST.ts:612`). `Encoding` is a
non-empty array of `Link` (`SchemaAST.ts:432`).

### 1.4 Field census, own fields only

| # | `_tag` | Class | Own fields beyond `_tag` |
| ---: | --- | --- | --- |
| 1 | `Declaration` | `:689` | `typeParameters : ReadonlyArray<AST>` `:691`; `run : DeclarationRun` `:692`; `encodingChecks : Checks?` `:693`; `encodingRun : DeclarationRun?` `:698` |
| 2 | `Null` | `:765` | none |
| 3 | `Undefined` | `:805` | none |
| 4 | `Void` | `:865` | none |
| 5 | `Never` | `:920` | none |
| 6 | `Any` | `:957` | none |
| 7 | `Unknown` | `:997` | none |
| 8 | `ObjectKeyword` | `:1034` | none |
| 9 | `Enum` | `:1074` | `enums : ReadonlyArray<readonly [string, string \| number]>` `:1076` |
| 10 | `TemplateLiteral` | `:1155` | `parts : ReadonlyArray<AST>` `:1157`; `encodedParts` `:1159`; `literals` `:1161`; `suffixLengths` `:1163` (last three `@internal`) |
| 11 | `UniqueSymbol` | `:1253` | `symbol : symbol` `:1255` |
| 12 | `Literal` | `:1315` | `literal : LiteralValue` `:1317` (type at `:1289`) |
| 13 | `String` | `:1376` | none |
| 14 | `Number` | `:1427` | none |
| 15 | `Boolean` | `:1502` | none |
| 16 | `Symbol` | `:1548` | none |
| 17 | `BigInt` | `:1602` | none |
| 18 | `Arrays` | `:1683` | `isMutable : boolean` `:1685`; `elements : ReadonlyArray<AST>` `:1686`; `rest : ReadonlyArray<AST>` `:1687`; `encodingChecks : Checks?` `:1688` |
| 19 | `Objects` | `:2097` | `propertySignatures : ReadonlyArray<PropertySignature>` `:2099`; `indexSignatures : ReadonlyArray<IndexSignature>` `:2100`; `encodingChecks : Checks?` `:2101` |
| 20 | `Union` | `:2913` | `types : ReadonlyArray<A>` `:2915`; `mode : "anyOf" \| "oneOf"` `:2916`; `encodingChecks : Checks?` `:2917` |
| 21 | `Suspend` | `:3144` | `thunk : () => AST` `:3146` |

Twelve variants — rows 2 through 8 and 13 through 17, i.e. the eleven keyword
tags plus `ObjectKeyword` — have **no** own fields. They are distinguished
only by `_tag`. This is the live-side counterpart of the persisted-side fact
`Effect4/Schema/Representation.lean` already records, that "Twelve of them
share one persisted field shape in rc.112".

Auxiliary classes referenced by the table:

| Class | Line | Fields |
| --- | --- | --- |
| `Link` | `:401` | `to : AST` `:402`; `transformation : SchemaTransformation.Transformation \| SchemaTransformation.Middleware` `:403-405` |
| `Context` | `:576` | `isOptional : boolean` `:577`; `isMutable : boolean` `:578`; `constructorDefault : Link?` `:580`; `annotations : Schema.Annotations.Key<unknown>?` `:581` |
| `PropertySignature` | `:1974` | `name : PropertyKey` `:1975`; `type : AST` `:1976` |
| `IndexSignature` | `:2036` | `parameter : IndexSignatureParameter` `:2037`; `type : AST` `:2038` |
| `Filter<E>` | `:3207` | `run : (input, self, options) => Issue \| undefined` `:3209`; `annotations : Annotations.Filter?` `:3210`; `aborted : boolean` `:3214` |
| `FilterGroup<E>` | `:3255` | `checks : [Check<E>, ...]` `:3257`; `annotations : Annotations.Filter?` `:3258` |

Two live/persisted *shape* differences are worth stating here because they are
not tag-level and a tag census cannot see them:

- Live `PropertySignature` carries only `name` and `type`
  (`SchemaAST.ts:1975-1976`). Optionality and mutability live on the **child
  AST's `Context`** (`SchemaAST.ts:577-578`), read back through `isOptional`
  (`:3731-3733`) and `isMutable` (`:3736-3738`). The persisted
  `PropertySignatureSchema` puts `isOptional` and `isMutable` on the
  **property record** (`SchemaRepresentation.ts:1039-1048`). The information
  moves node.
- Live `Arrays.elements` is a bare `ReadonlyArray<AST>`
  (`SchemaAST.ts:1686`); the persisted `ElementSchema` is a record with
  `isOptional`, `type`, `annotations` (`SchemaRepresentation.ts:1028-1032`).
  Same movement.

## 2. The map to the persisted 22

### 2.1 Where the map lives

Public entry points are `SchemaRepresentation.toRepresentation`
(`SchemaRepresentation.ts:784-786`) and `toRepresentations`
(`:805-811`); both delegate straight to
`internal/schema/toRepresentation.ts:28` and `:37`. The whole map is the one
closure body spanning `toRepresentation.ts:37-361`.

The node-level dispatch is `on` (`toRepresentation.ts:190-298`).

### 2.2 The tag correspondence

`on`'s `switch` has 21 case labels (`toRepresentation.ts:193`, `:200-211`,
`:217`, `:224`, `:231`, `:238`, `:245`, `:261`, `:282`, `:290`). That label
set was extracted and diffed against the route-A union set: **no difference**.
`on` has no `default` clause and no `throw` anywhere in `:190-298`.

| Live `_tag` | Persisted `_tag` | Emission site |
| --- | --- | --- |
| `Declaration` | `Declaration` | `toRepresentation.ts:194-199` |
| `Null` `Undefined` `Void` `Never` `Unknown` `Any` `String` `Boolean` `Number` `BigInt` `Symbol` `ObjectKeyword` | same name, 12 tags | `:200-216`, tag copied dynamically at `:213` |
| `Literal` | `Literal` | `:218-223` |
| `UniqueSymbol` | `UniqueSymbol` | `:225-230` |
| `Enum` | `Enum` | `:232-237` |
| `TemplateLiteral` | `TemplateLiteral` | `:239-244` |
| `Arrays` | `Arrays` | `:246-260` |
| `Objects` | `Objects` | `:262-281` |
| `Union` | `Union` | `:283-289` |
| `Suspend` | `Suspend` | `:291-296` |
| *(none)* | `Reference` | `:109`, from `makeReference` `:102-110` |

The `Check` alphabet maps alongside: `Filter -> Filter`
(`toRepresentation.ts:311-315`) and `FilterGroup -> FilterGroup` (`:317-321`),
via `fromChecks` (`:300-304`) and `fromCheck` (`:306-323`).

### 2.3 The map is not injective

**It is not injective, and it is worse than non-injective: it is not a
function of the live AST's first-order structure at all.**

Two facts establish the second, stronger statement, and they should be read
before the edge list.

**(i) The map reads the encoded side only.** `recur` (`toRepresentation.ts:179`)
does not dispatch on its argument. It calls `getCandidate(input)`
(`:180`), which sets `ast = SchemaAST.getContextOwner(SchemaAST.getLastEncoding(input))`
(`toRepresentation.ts:113-114`), and then `on(ast)` (`:187`).
`getLastEncoding` (`SchemaAST.ts:3457-3459`) walks the `encoding` chain to the
final `Link.to`. So the node that gets a persisted image is never the node you
handed in unless that node has no encoding. Upstream says this in its own
words: `toRepresentation` "Lowers the encoded side of an AST to a live
representation document" (`SchemaRepresentation.ts:768`), and "Apply
`SchemaAST.toType` to the AST first to lower its type side instead" (`:775`).
The decoded side and every transformation between the two sides have no
persisted image whatsoever.

**(ii) Candidate identity is host object identity, not structure.** The
candidate table is `Map<SchemaAST.AST, Map<string | undefined, ReferenceCandidate>>`
(`toRepresentation.ts:44`), keyed by AST object identity at `:121`.
`getContextOwner` reads a module-level `WeakMap` (`SchemaAST.ts:3424`,
`:3426-3428`). Upstream states the consequence:
"Structurally equal ASTs remain distinct candidates"
(`SchemaRepresentation.ts:710`). Two live ASTs that are structurally identical
therefore need not receive the same persisted image — they can be allocated
distinct reference names, or one inline and one referenced. **A Lean model of
this arrow as a function `LiveAST -> Representation` would be modelling
something rc.112 does not implement.** For a repository whose standing rule is
that canonical program content is first-order data, this is the sharpest
finding in the survey: the generator's own control flow is keyed on a
non-first-order notion of identity.

### 2.4 The information-losing edges

Each row names a pair of distinct live inputs whose persisted images coincide,
or a live field with no persisted image. All are source-reading; none has been
exhibited by an executed probe.

| # | Lost | Live site | Where it is dropped |
| ---: | --- | --- | --- |
| L1 | the entire `encoding` chain — every `Link` and its `Transformation`/`Middleware` | `SchemaAST.ts:641`, `:401-405` | never read by `on`; projected away at `toRepresentation.ts:113` via `SchemaAST.ts:3457` |
| L2 | `Declaration.run` — the whole parser of a declaration | `SchemaAST.ts:692` | `toRepresentation.ts:194-199` emits only `typeParameters`, `checks`, and annotations |
| L3 | `Declaration.encodingRun` | `SchemaAST.ts:698` | same site |
| L4 | `Filter.run` — the whole predicate of a check | `SchemaAST.ts:3209` | `toRepresentation.ts:311-315` emits only `_tag`, `aborted`, annotations |
| L5 | `encodingChecks` on `Declaration`, `Arrays`, `Objects`, `Union` | `:693`, `:1688`, `:2101`, `:2917` | no case in `on` reads the field |
| L6 | `Arrays.isMutable` | `SchemaAST.ts:1685` | `toRepresentation.ts:246-260`; `ArraysSchema` has no such field (`SchemaRepresentation.ts:1033-1038`) |
| L7 | `Context.constructorDefault` | `SchemaAST.ts:580` | `on` reads only `isOptional`, `isMutable`, `context.annotations` (`toRepresentation.ts:250-252`, `:265-272`) |
| L8 | `Context` in any position other than an `Arrays` element or an `Objects` property — e.g. on a `rest` member or on the document root | `SchemaAST.ts:642` | `rest` is mapped by bare `recur` at `toRepresentation.ts:257` |
| L9 | `Suspend.thunk` closure identity | `SchemaAST.ts:3146` | forced at `toRepresentation.ts:294` |
| L10 | `TemplateLiteral.encodedParts`, `literals`, `suffixLengths` | `:1159`, `:1161`, `:1163` | `toRepresentation.ts:239-244` emits only `parts` |
| L11 | `Base.[TypeId]` brand | `SchemaAST.ts:637` | not emitted by any case |
| L12 | a node's own tag and payload, when a reference is allocated for it | all 21 | `toRepresentation.ts:183-186`; the node becomes `{_tag:"Reference", $ref}` |

Notes that change how these should be read:

- **L1 is the largest edge.** It collapses every codec whose decoded and
  encoded sides differ onto its encoded side alone. A schema decoding to a
  `Date` from a string and a schema that is simply a string have the same
  persisted image up to annotations. Nothing in the persisted alphabet can
  distinguish them. This is the mechanical reason `docs/SCHEMA-CUTOVER.md` is
  right that "Effect's runtime `SchemaAST.AST` is not persisted Schema content
  because its declarations and checks contain executable functions" — but the
  ruling states it for `Declaration` and `Check`, and the encoding chain is a
  third and larger source of the same loss that the ruling does not name.
- **L2 and L4 are total semantic erasure, not partial.** After L2, two
  `Declaration` nodes with the same `typeParameters`, `checks`, and annotations
  are indistinguishable regardless of what they parse. After L4, a `Filter`
  carrying no `representation` annotation persists as `{_tag:"Filter",
  aborted}` and *every* such filter is one value. This is exactly why the
  reviver registry (`SC-REG-*`) is load-bearing rather than decorative: the
  registry identity is the only thing standing between two different programs.
- **L10 is derived data.** `encodedParts`, `literals`, and `suffixLengths` are
  computed in the constructor from `parts` (`SchemaAST.ts:1173-1192`).
  Re-derivation from the persisted `parts` is *not* established, because the
  derivation calls `toEncoded(part)` (`:1176`) and the encoding chain is gone
  by L1.
- **L12 is recoverable at document level, not at node level.** `Representation`
  alone is not injective; `Document` (`SchemaRepresentation.ts:480-483`) with
  its `references` table is what carries the payload back. Any Lean statement
  about recovery must be document-relative, which matches the ruling's
  "References are interpreted relative to the enclosing `Document`."
- One channel runs the *other* way and should not be mistaken for loss.
  `getCandidate` reads the identifier of the **unprojected** input when the
  projected node has none (`toRepresentation.ts:116-120`), appending an
  `Encoded` suffix at `:120`, and `annotateReference` (`:84-100`) can write
  `identifier: reference` into the stored node at `:99`. So the decoded side's
  identifier annotation can leak into the persisted document through the
  reference name, even though the decoded side itself does not survive.

## 3. Live variants with no persisted image

**None, at the node level.** All 21 live variants have a case in `on`, and the
case-label set is set-identical to the union (section 2.2). There is no
`default`, no `throw`, and no `undefined` return in `toRepresentation.ts:190-298`.
`toRepresentation` refuses nothing.

The refusals are all one layer further out, at `toJson`
(`SchemaRepresentation.ts:1134-1136`), and this two-boundary structure is the
part of the picture the repository record does not currently distinguish:

```text
live AST  --toRepresentation-->  live Document  --toJson-->  Json
          (drops closures per §2.4)            (prunes and refuses per §3)
```

Upstream itself calls the middle object a "live representation document"
(`SchemaRepresentation.ts:768`). It is **not** first-order. Three things
survive `toRepresentation` and die only at `toJson`:

1. **Local symbols.** `UniqueSymbol.symbol` is copied verbatim at
   `toRepresentation.ts:227`, and a symbol property name at `:268`. The
   persisted codecs are `Schema.Symbol` (`SchemaRepresentation.ts:1013`,
   `:1043`), whose encoder fails with
   `SchemaIssue.Forbidden` "cannot serialize to string, Symbol is not
   registered" when `Symbol.keyFor` returns `undefined`
   (`SchemaAST.ts:4093-4103`). So `E4-SCHEMA-CE-010` ("local symbol cannot
   enter portable wire data") bites at `toJson`, **not** at `toRepresentation`.
2. **Non-JSON annotations.** `annotationsField` (`toRepresentation.ts:23-25`)
   wraps the live annotations object by reference and does no filtering. The
   in-memory `Document` therefore shares annotation objects — and any host
   closures in them — with the live AST. Pruning happens only in
   `pruneAnnotations` (`SchemaRepresentation.ts:927-937`), gated by
   `SchemaAST.isJson`, reached through `AnnotationsSchema`'s encode leg
   (`:939-948`). `E4-SCHEMA-CE-011` likewise bites at `toJson`.
3. **Non-finite literal numbers.** Live `LiteralValue` is
   `string | number | boolean | bigint` with no finiteness restriction
   (`SchemaAST.ts:1289`); `literal` is copied verbatim at
   `toRepresentation.ts:220`. The persisted leg is `Schema.Finite`
   (`SchemaRepresentation.ts:1005`). This is the live-side half of
   `E4-SCHEMA-CE-023`.

There is a fourth case which is not a refusal but a **shape the persisted
codec rejects**, and it is worth its own line because `toRepresentation`
produces it silently:

4. `DeclarationSchema.representation` is required (`SchemaRepresentation.ts:979`),
   but `fromDeclarationAnnotations` emits the key only when the annotation is
   present, and returns `undefined` outright for a node with no annotations at
   all (`toRepresentation.ts:333`, `:336`). A live `Declaration` carrying no
   `representation` annotation therefore yields a live `Document` that `toJson`
   rejects. `docs/SCHEMA-CUTOVER.md` already records the required-vs-optional
   trap — "`Declaration.representation` and `Filter.representation` are
   **required in the codec** while the live TypeScript interfaces mark them
   optional" — and `test/contracts/schema-payload.contract.md` records the
   `Filter` half at `internal/schema/toRepresentation.ts:351-357`. The
   `Declaration` half at `:333-338` is the same trap and is recorded here.

Two live-side constructor refusals exist and belong to the live layer, not to
the map: `new Suspend(...)` throws `"Cannot add checks to Suspend"`
(`SchemaAST.ts:3155-3157`), and `replaceChecks` throws the same for a
`Suspend` (`SchemaAST.ts:3473-3476`). `TemplateLiteral`'s constructor throws
`Invalid TemplateLiteral part ${tag}` for a part outside
`TemplateLiteralPart` (`SchemaAST.ts:1181`). These bound what live ASTs can
exist at all.

## 4. Persisted tags with no live source

**None. All 22 persisted tags are emitted by `toRepresentation`.**

How this was established, in three steps that do not rely on reading the
control flow correctly:

1. Every `_tag: "..."` literal in `toRepresentation.ts` was extracted. There
   are 12: `Reference` `:109`, `Declaration` `:195`, `Literal` `:219`,
   `UniqueSymbol` `:226`, `Enum` `:233`, `TemplateLiteral` `:240`, `Arrays`
   `:247`, `Objects` `:263`, `Union` `:284`, `Suspend` `:292`, and the two
   `Check` tags `Filter` `:312` and `FilterGroup` `:318`.
2. Every non-literal `_tag:` was extracted. There is exactly one:
   `_tag: ast._tag` at `:213`, inside the 12-way fall-through whose labels are
   `Null` `Undefined` `Void` `Never` `Unknown` `Any` `String` `Boolean`
   `Number` `BigInt` `Symbol` `ObjectKeyword` (`:200-211`). Its image is
   therefore exactly those 12 names.
3. 10 representation literals + 12 fall-through names = 22, and the resulting
   set was diffed against the persisted union `export type Representation`
   (`SchemaRepresentation.ts:406-428`): no difference.

`Reference` is the only tag with **no live AST variant behind it**. It is
produced by `makeReference` (`:102-110`) from the reference-allocation policy,
not by any node. In that precise sense it is the persisted alphabet's only
synthetic member — but it is *not* hand-write-only, which is what the question
asked, and the distinction matters for admission: a decoder may not treat a
`Reference` as evidence that a document was hand-written.

## 5. Where the live AST holds host closures

"Host value" below means a function, an `Effect`, a `symbol`, a class instance,
or an entry in an open `unknown`-typed index signature. No field in the live
AST is typed as a `Promise` at the pin; `Effect` appears only as a *return*
type of the function-valued fields.

| Live field | Line | Host content | Survives `toRepresentation`? | Survives `toJson`? |
| --- | --- | --- | --- | --- |
| `Base.annotations` | `:639` | open index signature `{ [x: string]: unknown }` (`Schema.ts:17004-17006`); declaration hooks `toCodec` `Schema.ts:17166`, `toCodecJson` `:17175`, `toCodecStringTree` `:17184`, `toCodecIso` `:17195`, `toArbitrary` `:17198`, `toEquivalence` `:17199`, `toFormatter` `:17200`, `toCode` `:17201` are all function-valued | **yes, by reference** (`toRepresentation.ts:24`) | **no** — pruned by `SchemaAST.isJson` (`SchemaRepresentation.ts:927-937`) |
| `Base.checks -> Filter.run` | `:3209` | `(input, self, options) => Issue \| undefined` | **no** (`toRepresentation.ts:311-315`) | n/a |
| `Base.checks -> Filter.annotations` | `:3210` | `Annotations.Filter`, may hold `toJsonSchema`, `toCode` | yes, by reference (`:314`) | no, pruned |
| `Base.checks -> FilterGroup.checks` | `:3257` | recursive, each leaf a `Filter` | structure yes (`:319`), `run` no | structure yes |
| `Base.encoding` | `:641` | `[Link, ...]`; `Link.transformation` `:403-405` is a `Transformation` (whose `decode`/`encode` are `Getter`s with `run : (...) => Effect` — `SchemaGetter.ts:65-68`) or a `Middleware` (whose `decode`/`encode` are functions over `Effect` — `SchemaTransformation.ts:73-80`) | **no** — never read; the chain is only walked by `getLastEncoding` (`SchemaAST.ts:3457`) | n/a |
| `Base.context` | `:642` | `Context` class instance (`:576`) | only `isOptional`, `isMutable`, `annotations`, and only in element/property position (`toRepresentation.ts:250-252`, `:265-272`) | those three yes |
| `Context.constructorDefault` | `:580` | `Link`, i.e. functions | **no** | n/a |
| `Declaration.run` | `:692` | `DeclarationRun = (typeParameters) => (input, self, options) => Effect` (`:667-669`) | **no** | n/a |
| `Declaration.encodingRun` | `:698` | same | **no** | n/a |
| `Declaration.encodingChecks` | `:693` | `Checks`, i.e. `Filter.run` closures | **no** | n/a |
| `Arrays.encodingChecks` | `:1688` | same | **no** | n/a |
| `Objects.encodingChecks` | `:2101` | same | **no** | n/a |
| `Union.encodingChecks` | `:2917` | same | **no** | n/a |
| `Suspend.thunk` | `:3146` | `() => AST`, wrapped in `memoizeThunk` (`:3159`, factory at `:3100`) so it carries mutable cache state | **forced, then dropped** — `recur(ast.thunk())` (`toRepresentation.ts:294`); the persisted field is a nested `Representation` (`SchemaRepresentation.ts:162`) | yes, as data |
| `UniqueSymbol.symbol` | `:1255` | host `symbol` | **yes, verbatim** (`toRepresentation.ts:227`) | only if `Symbol.for`-registered (`SchemaAST.ts:4093-4103`) |
| `PropertySignature.name` | `:1975` | `PropertyKey = string \| number \| symbol` | **yes, verbatim** (`toRepresentation.ts:268`) | symbol leg: only if registered |
| `Literal.literal` | `:1317` | includes `bigint` (`:1289`) | yes (`:220`) | via a tagged `Schema.BigInt` codec (`SchemaRepresentation.ts:1007`) |
| `Objects.propertySignatures` | `:2099` | array of `PropertySignature` class instances (`:1974`) | flattened to plain records (`toRepresentation.ts:264-274`) | yes |
| `Objects.indexSignatures` | `:2100` | array of `IndexSignature` class instances (`:2036`) | flattened to `{parameter, type}` (`:275-278`) | yes |
| `Base.[TypeId]` | `:637` | module-private brand | **no** | n/a |

Ambient host state that is not a field but conditions the map, and therefore
has no first-order counterpart:

- `contextOwners : WeakMap<AST, AST>` (`SchemaAST.ts:3424`), read by
  `getContextOwner` (`:3426-3428`) and written by `replaceContext` (`:3452`).
- `memoizeThunk` (`:3100`), installed on every `Suspend` at `:3159`.
- `toType = memoizeIdempotent(...)` (`:3779`), used by the map at
  `toRepresentation.ts:174` and `:355`.
- The five per-call mutable tables inside `toRepresentations`:
  `references` `:41`, `referenceOwners` `:42`, `buildingReferences` `:43`,
  `candidates` `:44`, `visitingCandidates` `:45`.

**The difference that makes the persisted layer portable, stated exactly:**
every function-valued field is dropped at `toRepresentation` (rows `Filter.run`,
`Base.encoding`, `Context.constructorDefault`, `Declaration.run`,
`Declaration.encodingRun`, the four `encodingChecks`, and `Suspend.thunk`),
and the only host values that get past it are `symbol` and the open
`annotations` bag — both of which are then filtered or refused at `toJson`.
That is a **two-stage** boundary, and only the second stage yields first-order
data. A model that treats `toRepresentation`'s output as the portable artefact
would be one stage short.

## 6. Reference and recursion

### 6.1 How recursion is expressed on each side

**Live.** There is no `Reference` node and no references table. Recursion is
expressed only by `Suspend.thunk : () => AST` (`SchemaAST.ts:3146`) — a
closure over the schema being defined. The live AST is a host object graph
that may be cyclic *through thunks*; the cycle is cut lazily at parse time by
`Suspend.getParser`, which compiles `this.thunk()` on first use and caches the
parser (`SchemaAST.ts:3162-3165`).

**Persisted.** `Suspend` survives as a tag, but its `thunk` is a nested
`Representation` (`SchemaRepresentation.ts:157-163`, codec at `:984-989`), a
finite value. Recursion is carried instead by `Reference`
(`SchemaRepresentation.ts:171-174`) resolved against the `references` table on
`Document` (`:480-483`) or `MultiDocument` (`:491-494`), typed
`Record(String, Representation)` (`:1096`).

### 6.2 Where the reference table is allocated

In `toRepresentations` (`toRepresentation.ts:37`), at `:41`:
`const references: Record<string, Representation> = {}` — one table per call,
alongside `referenceOwners` `:42`, `buildingReferences` `:43`, `candidates`
`:44`, and `visitingCandidates` `:45`. Entries are written by
`makeReference` at `:107`, guarded against re-entry at `:103-106`.

`toRepresentation` (`:28-34`) is a thin wrapper: it calls
`toRepresentations([ast], options)` and returns
`{ representation: representations[0], references }` (`:33`). **A single-root
`Document` therefore shares the identical table object a `MultiDocument`
would have had.** Upstream describes `toRepresentations` as lowering roots
"in a shared reference environment" (`SchemaRepresentation.ts:806`).

Allocation is a **three-phase** pass, which matters because it means reference
naming cannot be decided locally:

1. `for (const ast of asts) visit(ast)` (`:47`) — count occurrences, detect
   recursion.
2. the policy loop over every candidate (`:50-67`) — assign names.
3. `Arr.map(asts, (ast) => recur(ast))` (`:69`) — build, emitting `Reference`
   wherever a name was assigned.

### 6.3 Direction A — recursion implies a reference entry: **verified**

Two independent supports at the pin.

*Generator.* `visit` sets `candidate.isRecursive = true` exactly when a
candidate is re-entered while still on the traversal stack
(`toRepresentation.ts:145-148`). The policy loop then reaches
`else if (candidate.isRecursive) { candidate.reference = getReference(...) }`
(`:63-65`), assigning the synthetic name `${ast._tag}_`. Since the `if` branch
at `:57-62` also assigns, **every recursive candidate leaves the loop with
`reference !== undefined`.** `recur` (`:183-186`) then routes it through
`makeReference`, which writes the table entry at `:107` and returns a
`Reference` node at `:109`. Upstream states the same rule in prose:
"Recursive candidates always require a reference. When the policy returns
`undefined` for one, the generator assigns a synthetic name."
(`SchemaRepresentation.ts:733-734`).

*Structural.* Independently of the generator, a persisted document is a finite
JSON value: `Suspend.thunk` is a nested `Representation`
(`SchemaRepresentation.ts:162`), not a delay, so no persisted construct can
close a loop except `$ref`. Recursion in a persisted document therefore
*must* appear as a `Reference`, whoever wrote it.

*Scope of the verification.* "Recursion" here means "a candidate re-entered
during `visit`'s traversal". `visit`'s descent is the switch at `:152-168`:
`Declaration`/`Arrays`/`Objects`/`Union` via `ast.recur`, `TemplateLiteral`
via `parts` (`:163`), `Suspend` via `thunk()` (`:166`), plus check
representation schemas via `visitChecks` (`:172-177`). Those `recur` methods
cover exactly the child positions `on` later descends into —
`Declaration.typeParameters` (`SchemaAST.ts:731`), `Arrays.elements`+`rest`
(`:1808-1809`), `Objects` property types, index parameters and index types
(`:2417-2428`), `Union.types` (`:2978`) — so no cycle reachable by `on` is
invisible to `visit`. A cycle reachable only through a dropped field
(`Context.constructorDefault`, `Link.to`) is not traversed by either, and is
therefore outside both.

*Bonus: an open item in the record is now closed by source reading.*
`docs/SCHEMA-CUTOVER.md` currently says of the recursion-cutting behaviour that
it was "observed off-pin in `beta.103` and **not** yet verified at rc.112",
and that "lowering forces the thunk and cuts recursion by emitting a
`Reference` into the document's references table." **That behaviour is now
verified at rc.112 by source reading**, at `toRepresentation.ts:166` (forcing
during `visit`), `:294` (forcing during `on`), `:145-148` (recursion mark),
`:63-64` (synthetic name), and `:102-110` (`Reference` emission plus table
write). It remains a lowering claim belonging to the `SC-DOC-*` packet, and it
remains unexecuted.

### 6.4 Direction B — a reference entry implies recursion: **refuted**

`defaultReferencePolicy` is `({ identifier }) => identifier`
(`toRepresentation.ts:8`). The policy loop consults it for **every** candidate
(`:50-56`), before and independently of any `isRecursive` test, and assigns a
reference whenever it returns a name (`:57-62`). `resolveIdentifier` reads the
ordinary `identifier` annotation (`internal/schema/annotations.ts:42`).

So any node carrying an `identifier` annotation is extracted into the table
whether or not it recurs. Upstream states the contrapositive:
"The default policy returns the resolved `identifier`, so anonymous
non-recursive candidates remain inline even when they occur more than once."
(`SchemaRepresentation.ts:755-756`). A caller-supplied `referencePolicy`
(`SchemaRepresentation.ts:740`, option at `:764`) can extract anything at all.

**The repository's claim is verified and can be strengthened.**
`docs/SCHEMA-CUTOVER.md` states: "A non-empty references table does **not**
mean the document is recursive. A shared non-recursive name allocates a table
entry with no `Suspend` node anywhere. No admission rule may infer recursion
from table non-emptiness." The word *shared* understates the case. Sharing is
not required: the policy is consulted per candidate regardless of
`occurrences`, so a **single, once-occurring, identified** node is enough. By
source reading, a schema that is one annotated string should yield a root that
is a `Reference` and a one-entry table containing the `String` node — a
non-empty references table, one occurrence, no `Suspend`, no recursion.

That last sentence is **an unexecuted prediction**, not an observation. It is
the natural next vector for the first-party pin already sealed at
`vendor/foldlab/pinned/tree/library/effects/test/SchemaReferencesPin.test.ts`,
which today establishes what rc.112 *accepts* but does not exercise what the
generator *emits*.

### 6.5 A third non-implication, not previously recorded

`Suspend` in a persisted document does not imply recursion either. A
non-recursive `Suspend` — a lazy wrapper around a finite schema — is forced at
`toRepresentation.ts:294` and its `thunk` becomes the forced node inline, with
no `Reference` and no table entry, because `isRecursive` was never set at
`:146`. So of the three signals an admission rule might read off a persisted
document — a non-empty table, a `Reference` node, a `Suspend` node — **none
implies recursion**, and only `Reference` can express it.

## 7. Drift notes against the existing record

Neither note changes a ruling; both record how the retained authority table
and citations were repaired during the survey.

1. **The internal-file pin gap is closed at the installed-byte layer.**
   `PORT-MANIFEST.md` now records both `toRepresentation.ts` and
   `annotations.ts`; the digests agree with this survey. Upstream comparison
   remains a separate provenance edge.

2. **A citation-drift note that resolved itself mid-survey, recorded because
   the convergence is evidence.** While this survey was being written, seven
   line pointers in the persisted-field snapshot of `docs/SCHEMA-CUTOVER.md`
   — the block introduced by the claim that its field constraints were
   "checked line by line against the pinned bytes" — pointed at blank lines or
   at the wrong construct in `SchemaRepresentation.ts`. A concurrent process
   corrected all seven while this file was being drafted.

   The corrected values are `Declaration :977`, `Suspend :984`,
   `Reference :1066`, `PropertySig :1039`, `keyword tags :970`,
   `References :1096`, `Document :1098`, and `MultiDocument :1105`. **Those are
   exactly the values this survey derived independently**, by grepping the
   `const`/`function` declaration sites at digest
   `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`, before
   the correction landed and without reading it. Two unrelated readings of the
   same bytes converged on the same 22-row field map.

   That convergence is a cross-check on the snapshot, not a discharge of
   `SC-REP-01` or `SC-REP-04`. Both readings are lexical; neither decodes
   anything. The numeric-domain citations the ruling leans on hardest —
   `Schema.Finite` at `:1005`, `Schema.Number` at `:999` used at `:1020` and
   `:1042` — were exact in both readings throughout.

## 8. What is not established at the pin

- **Nothing here was executed.** No Effect runtime was started, no schema was
  built, no document was emitted. Every behavioural sentence is a reading of
  control flow in fixed bytes. The finite probes performed were nine shell
  extractions on one host over one byte-state, and they establish *lexical
  set* facts only.
- Whether a subclass of `SchemaAST.Base` is declared outside `SchemaAST.ts`
  anywhere in the package. If one is, `isAST` (`SchemaAST.ts:92-93`) would
  admit it and all four census routes would miss it.
- Whether `toRepresentation` terminates on every live AST. `recur` terminates
  on cycles because `visit` marked them, but a live AST that is *infinite
  without being cyclic* — each `thunk()` returning a fresh object — would
  defeat the identity-keyed candidate table (`toRepresentation.ts:44`,
  `:121`) and is not excluded by anything read here. This is the generator-side
  face of the obligation `docs/SCHEMA-CUTOVER.md` opened as `SC-DOC-06`,
  "productivity is not guardedness".
- The §6.4 prediction that a single annotated non-recursive node yields a
  one-entry table. Predicted from `toRepresentation.ts:8`, `:50-62`, and
  `SchemaRepresentation.ts:755-756`; not observed.
- Any statement about `fromRepresentation`
  (`internal/schema/fromRepresentation.ts`, digest recorded in
  `test/contracts/schema-payload.contract.md`). The inverse direction was not
  surveyed. Whether the persisted alphabet maps back into a live AST at all,
  and what it must invent to do so, is open work.
- Anything about `SchemaAST.ts` outside the AST alphabet, its `Check` family,
  and the helpers cited: the parser compilers, the `flip` machinery, the
  JSON-Schema lowering, and `toCodeDocument` were not surveyed.
