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
