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
