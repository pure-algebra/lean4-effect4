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
