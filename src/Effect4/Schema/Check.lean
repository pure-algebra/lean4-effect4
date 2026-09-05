import Effect4.Schema.Document

/-!
# Schema.Check.lean

Owner: Schema persisted/decode-side structural field admission.

This module declares `SC-REP-04`'s persisted/decode-side field-admission
judgment from `Test/contracts/schema-payload.contract.md` D7, its Boolean
companion, their agreement, exact constructor equations, and retained positive
and negative witnesses.

Nothing below is a refusal carrier, a classifier over `RepresentationTag`, or a
profile identity. `SC-PROFILE-01` through `SC-PROFILE-03` remain unopened, and
the rest of this file's original navigation notes still apply to them.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/research/SCHEMA-CUTOVER.md`; counterexample rows
are those of `Test/Counterexamples/REGISTER.md`.

## Ownership

This module owns Effect4's **Schema-specific structural admission checker**
over the persisted representation. It does not own a generic target-profile
classifier, refusal, issue, diagnostic, or checked-value carrier. A failed
judgment here is only a false proposition.

Naming hazard, recorded rather than silently resolved: rc.112 also has a
persisted node family called `Check` (`Filter | FilterGroup`). That is a
representation node, and its tag alphabet already lives in
`src/Effect4/Schema/Representation.lean` as `CheckTag`. The mutually recursive
`Representation`/`Check` payload family must be declared together in
`Schema.Representation`; this module consumes that family and must not add a
second `Check` or `CheckTag` carrier.

A second naming hazard, newly recorded. rc.112 also ships a module called
`Filter.ts` whose `Filter<Input, Pass, Fail>` is a function returning a
`Result` (`Filter.ts:44`), with combinators such as `or` (`Filter.ts:714`) and
`zipWith` (`Filter.ts:755`). That module is **unrelated** to the schema check
family: no schema module imports it. `SchemaRepresentation.ts`, `SchemaAST.ts`,
and `Schema.ts` contain no `from "./Filter.ts"` import at the pinned bytes.
Nothing in `Filter.ts` may be cited as evidence about a schema `Filter`.

## Assigned obligation

- `SC-REP-04` recursive field admission matches the frozen rc.112 constraints.
  Its proposition, Boolean reflection, constructor equations, and witnesses
  are implemented below; denotation, wire form, and host agreement remain
  separate graph edges.

The directory boundary is settled as follows. `Effect4.Protocol.Profile` owns
versioned target-profile identity, `Effect4.Protocol.Admission` owns generic
profile membership, unknown-profile behavior, and refusal policy, and this
module owns only the Schema-specific structural judgment. It may later
implement a separately contracted adapter to the Protocol admission boundary,
but it must not mint a second profile or admission carrier.

## Gated by

The payload carrier and frozen D7 admission breaker, both now supplied. The tag
layer itself needs no checker: `mem_census` is proved by case analysis.
-/

/-!
## Pin, method, and the exact scope of what follows

Everything in the remaining sections is **pinned source reading plus finite
executable probes** against one installed package. It is not a Lean theorem,
not a decoder result of this repository, and not a statement that any future
Effect4 carrier agrees with rc.112. No admission rule below is discharged.

Evidence files, on the build host under
`library/effects/node_modules/effect/src/` in the Foldlab checkout. Foldlab is
not a dependency of this repository; this is a third-party npm package
identified by digest that happens to live under that checkout. Re-verifying
needs a local `effect@4.0.0-rc.112` install and the path passed by hand.

```text
SchemaRepresentation.ts  a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc
SchemaAST.ts             7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8
Schema.ts                9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784
Filter.ts                38214f48f02c8e80b0d8f615d8baa60b1881bc54bd0d6b07587faeb22d84d093
internal/schema/toRepresentation.ts
                         677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2
```

The first three digests are the `installed` column of the authority table in
`docs/research/SCHEMA-CUTOVER.md`. `SchemaRepresentation.ts` and `SchemaAST.ts` are byte
matches with the pinned upstream revision; `Schema.ts` is **not** a byte match
upstream, so every `Schema.ts:NNN` citation below is a citation of the
*installed* bytes only. `Filter.ts` and `internal/schema/toRepresentation.ts`
carry no prior repository pin; their digests are recorded here for the first
time and are unverified against upstream.

Two distinct kinds of claim appear below and are never merged.

- **Declared.** A field, type, or codec spelling read off the pinned source at
  a cited line.
- **Observed.** A behaviour reproduced by running the installed package. Each
  observation is a finite probe over the cases it names, and generalises to
  nothing else. Probes were run out of tree and are not retained in this
  repository, so an observation is reproducible-in-principle evidence, not a
  standing gate. Where a future gate is wanted, its obligation is named.

A word about `representation`. The identifier is overloaded three ways in the
pinned file and the overload is a live source of error: the persisted node
family `Representation` (`SchemaRepresentation.ts:406`), the *field* named
`representation` on a check or declaration, and the `Document` root field also
named `representation` (`SchemaRepresentation.ts:481`). Below, "the
representation annotation" always means the field.
-/

/-!
## 1. The persisted field set of `Filter` and `FilterGroup`

### `Filter`

Interface, `SchemaRepresentation.ts:444-449`:

```text
_tag           : "Filter"                                        :445  required
representation : CheckRepresentationAnnotation<Representation>?  :446  OPTIONAL
annotations    : Schema.Annotations.Annotations?                 :447  optional
aborted        : boolean                                         :448  required
```

Codec, `SchemaRepresentation.ts:956-961`:

```text
_tag           : Schema.tag("Filter")                    :957  required
representation : CheckRepresentationAnnotationSchema     :958  REQUIRED
annotations    : AnnotationsSchema                       :959  optional key
aborted        : Schema.Boolean                          :960  required
```

The interface and the codec **differ**, on exactly one field. `representation`
is `?`-optional at `:446` and is a bare, non-`Schema.optional` struct field at
`:958`. `aborted` agrees (required at `:448` and `:960`); `annotations` agrees
(optional both sides; the codec optionality is inside `AnnotationsSchema`,
`:939`); `_tag` agrees.

`Filter` has **no** `checks` field on either side. Compare `:444-449` with
`FilterGroup` at `:461`, and `:956-961` with `:966`.

### `FilterGroup`

Interface, `SchemaRepresentation.ts:457-462`:

```text
_tag           : "FilterGroup"                                   :458  required
representation : CheckRepresentationAnnotation<Representation>?  :459  optional
annotations    : Schema.Annotations.Annotations?                 :460  optional
checks         : readonly [Check, ...Array<Check>]               :461  required, non-empty
```

Codec, `SchemaRepresentation.ts:962-967`:

```text
_tag           : Schema.tag("FilterGroup")                        :963  required
representation : Schema.optional(CheckRepresentationAnnotation…)  :964  optional
annotations    : AnnotationsSchema                                :965  optional key
checks         : Schema.NonEmptyArray(CheckSchema)                :966  required, non-empty
```

The interface and the codec **agree** for `FilterGroup`. The divergence is
specific to `Filter.representation`.

`FilterGroup` has **no** `aborted` field on either side. Aborting is a
leaf-only property in the persisted data; a group can only abort through a
member that carries `aborted = true`. See section 4 for what that does.

### The representation annotation itself

`RepresentationAnnotation` interface, `SchemaRepresentation.ts:25-28`:
`id : string` (`:26`), `payload : Schema.Json` (`:27`).

`CheckRepresentationAnnotation<S>` extends it, `:36-38`, adding
`schemas?: ReadonlyArray<S> | undefined` (`:37`). A check's annotation is
instantiated at `S = Representation` (`:446`, `:459`).

Codec, `SchemaRepresentation.ts:917-925`:

```text
RepresentationAnnotationSchema       :917  { id : Schema.NonEmptyString  :918
                                             payload : Schema.Json       :919 }
CheckRepresentationAnnotationSchema  :922  …fields + schemas : Schema.optional(
                                             RepresentationsSchema)      :924
```

**A third interface/codec divergence, not previously recorded in this
repository.** The interface types `id` as plain `string` (`:26`); the codec
requires `Schema.NonEmptyString` (`:918`). Observed: a check whose
`representation.id` is `""` is refused by the pinned decoder, reported as
`Expected a value with a length of at least 1` at path
`["representation"]["checks"][0]["representation"]["id"]`. This is the same
class of hazard as `Filter.representation` presence: a model that reads the
interface admits documents rc.112 rejects. `docs/research/SCHEMA-CUTOVER.md` records
the codec spelling `id : NonEmptyString` but lists only the presence
divergence, so the non-emptiness divergence is added here.

Observed field emission order under `encode ∘ decode`, from a probe that fed
the keys in scrambled order: a `Filter` re-emits as `_tag`, `representation`,
`annotations`, `aborted`, and a `FilterGroup` as `_tag`, `representation`
(when present), `annotations`, `checks` — the struct declaration order at
`:957-960` and `:963-966`, not the input order. This is an ordering
observation on two finite inputs. It is not a canonicalisation theorem and
does not discharge `SC-WIRE-04` or `SC-WIRE-05`.
-/

/-!
## 2. Nesting: does a check contain a check?

**Yes, and the recursion is unbounded in the persisted data.**

`Check = Filter | FilterGroup` (`SchemaRepresentation.ts:436`).
`FilterGroup.checks : readonly [Check, ...Array<Check>]` (`:461`), so a member
may itself be a `FilterGroup`. The codec closes the same loop lazily:
`CheckSchema = Schema.suspend((): Schema.Codec<Check, unknown> => CheckUnion)`
(`:950`), `CheckUnion = Schema.Union([FilterSchema, FilterGroupSchema])`
(`:968`), and `FilterGroup.checks = Schema.NonEmptyArray(CheckSchema)` (`:966`).

**No depth bound appears anywhere in the pinned check codec.** There is no
fuel, no maximum-depth option, and no cycle guard on this path — `:950`,
`:966`, and `:968` are the whole recursion. Observed: a document carrying 200
nested `FilterGroup` wrappers around one `Filter` decodes without complaint.
That probe establishes that at least depth 200 is accepted; it does not
establish that every depth is, and the host's own stack is the only limit
anyone has measured.

### The persisted recursion shape is a tree, and it is left-leaning in practice

The shape produced by rc.112's own authoring API is not flat. `Filter.and`
returns `new FilterGroup([this, other], annotations)` (`SchemaAST.ts:3235-3238`)
and `FilterGroup.and` returns the same (`SchemaAST.ts:3271-3274`), so chaining
`.and()` re-wraps the accumulated group as the *first* member of a new group.
Observed: `a.and(b).and(c).and(d)` lowers to

```text
FilterGroup[ FilterGroup[ FilterGroup[ Filter a, Filter b ], Filter c ], Filter d ]
```

— depth three for four leaves, growing linearly with the number of `.and()`
calls. A model that assumes groups arrive flat, or that group depth is bounded
by anything an author would write deliberately, is wrong about rc.112 output.

`Schema.check(...)` (`Schema.ts:5135-5139`) is the other route and attaches
several checks as *siblings* on the node rather than as a group;
`Schema.makeFilterGroup` (`Schema.ts:6725-6730`) builds a group directly.

### `Filter` is a `checks`-leaf but **not** a representation-leaf

`docs/research/SCHEMA-CUTOVER.md` states, as pinned fact 2 of its six, that "`Filter`
has **no** `checks` field; it is a leaf. Only `FilterGroup` recurses". The
first clause is exact. **The word "leaf" and the word "only" are too strong**,
and this annotation narrows them.

`Filter.representation.schemas` is `ReadonlyArray<Representation>` (`:37` at
`S = Representation`, codec `:924`). So a `Filter` carries arbitrarily deep
`Representation` subtrees, and those subtrees carry `checks` of their own. The
mutual recursion `Representation ↔ Check` therefore runs through **both**
`FilterGroup.checks` and `Filter.representation.schemas`.

Observed, decoded intact by the pinned decoder:

```text
String
  checks[0] = Filter  id "outer"
    representation.schemas[0] = Objects
      checks[0] = FilterGroup
        checks[0] = Filter  id "inner"
          representation.schemas[0] = Reference $ref "R"
```

Consequences this module must carry into `SC-REP-04` and `SC-PROFILE-01`:

- a recursive Effect4 admission function over `Representation` must descend
  into `Filter.representation.schemas`, or it will accept representations it
  never looked at;
- reference-occurrence collection for `SC-DOC-01` must do the same. rc.112's
  own lowering already does: `toRepresentation.ts:174` visits
  `check.annotations?.representation?.schemas` before `:175` recurses into
  `FilterGroup.checks`;
- any termination argument for a check walk is over two mutually recursive
  positions, not one.
-/

/-!
## 3. Does a check carry a `representation` field?

Both do, and the interface/codec answer differs between them. Restating
section 1 as the direct answer:

| | interface | codec | verdict |
| --- | --- | --- | --- |
| `Filter.representation` | optional `:446` | required `:958` | **differs** |
| `FilterGroup.representation` | optional `:459` | optional `:964` | agrees |

For comparison, the same divergence exists one family over:
`Declaration.representation` is optional at `:146` and required at `:979`.
`Reference` has no such field at all (`:171-174`, `:1066-1069`).

### The divergence is reachable from inside rc.112, not only from a bad model

This is the sharpening worth recording. `docs/research/SCHEMA-CUTOVER.md` frames the
divergence as a modelling hazard — "a model that reads optionality off the
interfaces admits two document shapes rc.112 rejects". True, and there is more
to it: **rc.112's own lowering path produces one of those shapes.**

`toRepresentation.ts:306-323` builds a persisted `Filter` from a live
`SchemaAST.Filter` as `{ _tag, aborted, ...fromCheckAnnotations(…) }`, and
`fromCheckAnnotations` (`:341-360`) omits the `representation` key entirely
when the live filter carries no representation annotation (`:351-352`, `:357`).
Nothing on that path supplies a default.

Observed, on a filter built with `SchemaAST.makeFilter(pred, { expected: "…" })`
and no representation annotation:

```text
toRepresentation(ast)  =>  { _tag: "Filter", aborted: false,
                             annotations: { expected: "long" } }      -- no key
toJson(that document)  =>  throws SchemaError(Missing key)
                           at ["representation"]["checks"][0]["representation"]
```

So the in-memory `Representation` type is inhabited by values the persisted
codec refuses to encode. The refusal happens at `toJson`
(`SchemaRepresentation.ts:1134-1136`, `encodeDocument` at `:1112`), not at
lowering. Decoding refuses symmetrically: a JSON `Filter` without
`representation` is rejected with the same missing-key path, while a
`FilterGroup` without `representation` decodes.

For this module that means: **`Filter.representation` presence is an admission
condition on the persisted form, and the live `Representation` type is not a
subset of the encodable ones.** Any Effect4 statement of the form "an rc.112
`Representation` value is encodable" is false as written. The claimable
direction is the one `docs/research/SCHEMA-CUTOVER.md` already fixes for `SC-CAS-*`:
Effect4-admitted implies host-accepted, never the converse.

`SchemaRepresentation.ts:1126` records the encode-side refusal in prose:
invalid persistence identities and unsupported structural values throw an
`Error` containing their representation path.
-/

/-!
## 4. How a `FilterGroup` combines its members

Cited from the runtime, not from the type. The whole combinator is
`SchemaAST.collectIssues`, `SchemaAST.ts:4125-4155`.

```text
4132  for (let i = 0; i < checks.length; i++) {
4134    if (check._tag === "FilterGroup") {
4135      issues = collectIssues(check.checks, value, issues, ast, options)
4136-4141  if (issues && (options.errors !== "all" || lastIssue.filter.aborted)) return issues
4142    } else {
4143      const issue = check.run(value, ast, options)
4144-4147  if (issue) { push a SchemaIssue.Filter onto issues
4148        if (options.errors !== "all" || check.aborted) return issues } } }
```

Four separate facts, kept separate.

**Combination is conjunction.** Every member must pass. There is no
disjunction anywhere on this path: a group succeeds exactly when it adds no
issue, and one failing member is enough to fail the group. Observed: a group
of two whose first member passes and whose second fails, fails.

**The group contributes no wrapper and no operator of its own.** The recursive
call at `:4135` is passed the *same* `issues` accumulator, so a group's member
issues land flat in the enclosing list; no group-level issue node is created.
Observed, on one finite pair of inputs: `a.and(b).and(c)` and the sibling list
`check(a, b, c)` produce the same three issues in the same order. The group is
therefore a carrier for shared annotations (`:3258`, `:3268-3270`) and for
persisted structure, not a distinct combining rule. This is an observation on
one pair of inputs, not a normalisation theorem, and no Effect4 rewriting of
groups into sibling lists is licensed by it.

**Short-circuiting is conditional on `ParseOptions.errors`, which defaults to
stopping.** `options.errors !== "all"` at `:4138` and `:4148` returns after the
first failure. `ParseOptions.errors` is `"first" | "all" | undefined`
(`SchemaAST.ts:471`) and defaults to `"first"` (`SchemaAST.ts:465-469`). So the
default is short-circuiting and `errors: "all"` is exhaustive. Observed: three
failing members report one issue by default and three under `errors: "all"`.

**`aborted` overrides exhaustiveness.** Under `errors: "all"`, a failing member
with `aborted = true` still returns immediately (`:4148`), and after a nested
group the same test is applied to the last accumulated issue (`:4138`).
Observed: a group whose first member is aborting and whose next two also fail
reports only the first issue even under `errors: "all"`. The class doc states
the same at `SchemaAST.ts:3247-3248`.

`aborted` defaults to `false` (`SchemaAST.ts:3222`), `.abort()` sets it
(`:3232-3234`), and a guard-derived filter is aborting by construction
(`:3306-3314`, comment at `:3313`).

`runChecks` (`SchemaAST.ts:4158-4168`) is the constructor-side entry point and
hard-codes `{ errors: "all" }` at `:4162`, so that path is exhaustive-unless-
aborted regardless of caller options.

Note for the eventual Effect4 semantics: this is *live* check evaluation over
`SchemaAST.Filter.run` (`SchemaAST.ts:3209`), a host function. It is not
something the persisted `Filter` node can express — the persisted node keeps
`aborted` and a representation identity, and the predicate itself is recovered
only through a registered reviver (`SchemaRepresentation.ts:518-526`,
`:534-542`). The combinator semantics above therefore belong to the registry
and host-conformance packet (`SC-REG-*`, `SC-HOST-*`), not to structural
admission. This module may cite them; it may not claim to implement them.
-/

/-!
## 5. Which of the 22 tags carry checks

Mechanically, from the codec. `KeywordFields = { annotations, checks }`
(`SchemaRepresentation.ts:952-955`) with `checks: ChecksSchema` at `:954`, and
`ChecksSchema = Schema.Array(CheckSchema)` at `:951`.

**20 tags carry an ordered, possibly empty `checks`.**

- 12 through `makeKeywordSchema` (`:970-975`, spreading `KeywordFields` at
  `:973`), called at `:1075-1086`: `Null`, `Undefined`, `Void`, `Never`,
  `Unknown`, `Any`, `String`, `Number`, `Boolean`, `BigInt`, `Symbol`,
  `ObjectKeyword`.
- 7 through an explicit `...KeywordFields` spread: `Literal` `:1002`,
  `UniqueSymbol` `:1012`, `Enum` `:1017`, `TemplateLiteral` `:1025`,
  `Arrays` `:1035`, `Objects` `:1056`, `Union` `:1062`.
- 1 with its own field: `Declaration`, `checks: ChecksSchema` at `:982`.

**1 tag carries a present-but-exactly-empty `checks`:** `Suspend`,
`checks: Schema.Tuple([])` at `:987`.

**1 tag carries no `checks` field at all:** `Reference`, `:1066-1069`.

The same split holds on the interface side: `Keyword<Tag>.checks` at `:179`,
`Declaration.checks` at `:149`, `Suspend.checks : readonly []` at `:161`, and
`Reference` at `:171-174` with only `_tag` and `$ref`.

`checks` is a **required key with a possibly empty value**, not an optional
key. Observed: `{ _tag: "String" }` is refused with `Missing key` at
`["representation"]["checks"]`, while `{ _tag: "String", checks: [] }` decodes.
The same holds for `Suspend`.

### Verifying the two claims `docs/research/SCHEMA-CUTOVER.md` marks special

**`Suspend`: the claim is correct.** `checks: Schema.Tuple([])` (`:987`) is
present and exactly empty, and the interface says `readonly []` (`:161`).
Observed: a `Suspend` whose `checks` holds one otherwise-valid `Filter` is
refused, reported as `Expected no excess property` at
`["representation"]["checks"][0]` — the empty-tuple arity, not a check error.
A `Suspend` with `checks: []` decodes; a `Suspend` with the key missing is
refused. This agrees with the sealed rc.112 pin already cited in
`docs/research/SCHEMA-CUTOVER.md`.

**`Reference`: the claim is correct as stated about fields, and needs one
qualification about admission.** `Reference` is exactly `_tag` and `$ref`
(`:171-174`, `:1066-1069`) and is the only representation with neither
`annotations` nor `checks`. What the phrasing "it is exactly `_tag` and
`$ref`" does not say is that this describes the **decoded value, not the
accepted input**. Observed: a JSON `Reference` carrying extra `annotations`
and `checks` keys is **accepted**, and the two keys are silently dropped from
the decoded value. The cause is `ParseOptions.onExcessProperty`, which
defaults to `"ignore"` and strips undeclared properties
(`SchemaAST.ts:474-480`). The same silent drop was observed for a spurious
`checks` key on a `Filter` and a spurious `aborted` key on a `FilterGroup`.

Neither claim in `docs/research/SCHEMA-CUTOVER.md` is wrong. The qualification matters
anyway, because it is exactly the standing claim-scope rule that document
already fixes: rc.112 accepts more than Effect4 will. If this module refuses a
`Reference` bearing an `annotations` key, that refusal is an **Effect4 profile
refusal and must never be described as an rc.112 refusal.**

A note on a neighbouring `docs/research/SCHEMA-CUTOVER.md` row, recorded because it was
observed while verifying `Suspend`. That document says the beta.103 behaviour
where lowering forces the thunk and cuts recursion by emitting a `Reference`
into the references table is "**not** yet verified at rc.112". Observed at
rc.112: lowering a self-recursive `Schema.Struct` produces a document whose
root is `Reference $ref "Objects_"`, whose table entry is the `Objects` node,
and whose recursive position is
`Suspend{ checks: [], thunk: Reference $ref "Objects_" }`. That is the
described behaviour, at the pin. It remains a lowering claim owned by the
`SC-DOC-*` packet, not a representation claim, and this note does not move
that row — the owning document does.
-/

/-!
## 6. What an `annotations` payload is, and what encoding does to it

This section is the direct input to reserved row `E4-SCHEMA-CE-011`, "all host
annotations survive portable serialization".

### The live type

A persisted node's `annotations` field is typed
`Schema.Annotations.Annotations | undefined` (`SchemaRepresentation.ts:147`,
`:160`, `:178`; on checks, `:447` and `:460`). That interface is an open index
signature: `readonly [x: string]: unknown` (`Schema.ts:17004-17006`). It is
user-extensible by declaration merging (`Schema.ts:16979-16987`), and a missing
key and an `undefined` value both mean absent (`Schema.ts:16968-16971`).

So the live annotation bag is **arbitrary host values under arbitrary string
keys**, with no JSON restriction in the type at all.

The check-specific bag `Schema.Annotations.Filter` (`Schema.ts:17218-17277`)
makes the stakes concrete. Its declared members include `toJsonSchema` and
`toCode`, both **functions** (`Schema.ts:17231`, `:17232`), an `arbitrary`
hint carrying further callbacks (`:17262-17264`), and a `representation` whose
`schemas` are live `SchemaAST.AST` values (`:17219-17221`). None of that is
JSON. It is precisely the executable content that
`docs/research/SCHEMA-CUTOVER.md` names when it rules that Effect's runtime
`SchemaAST.AST` is not persisted Schema content.

### The codec, and what it does in each direction

`AnnotationsSchema`, `SchemaRepresentation.ts:939-948`:

```text
939  Schema.optional(Schema.Record(Schema.String, Schema.Unknown))
940    .pipe(Schema.encodeTo(Schema.optionalKey(Schema.JsonObject), {
941      decode: SchemaGetter.passthroughSubtype(),
942-946   encode: transformOptional(a => none if absent/undefined
                                        else pruneAnnotations(a.value)) }))
```

`pruneAnnotations`, `:927-937`: iterate `Object.entries`, keep an entry only
when `SchemaAST.isJson(value)` (`:932`), and return `Option.none()` when the
survivors are zero (`:936`).

The two directions are **not** mirror images, and this is the asymmetry
`E4-SCHEMA-CE-011` has to state.

**Encode prunes, silently.** Non-JSON entries are dropped with no issue and no
diagnostic. When nothing survives, the encoded key is *omitted* rather than
emitted as `{}` — `Option.none()` at `:936` into `optionalKey` at `:940`.
Observed: annotating a schema with
`{ ok: 1, bad: fn, nan: NaN, undef: undefined, sym: Symbol(), big: 1n }`
encodes to `annotations: { ok: 1 }`, and annotating with `{ bad: fn }` alone
encodes to a node with **no** `annotations` key.

**Decode refuses.** The encoded side is `Schema.JsonObject` (`:940`) and the
decode getter is `passthroughSubtype()` (`:941`) — no pruning step exists in
that direction. Observed: decoding a node whose `annotations` holds a function
value, or an `undefined` value, is refused with `Expected JSON value` at the
offending key path.

So `docs/research/SCHEMA-CUTOVER.md`'s ruling — "unsupported entries are pruned and an
empty result is omitted" — is **correct for encode and does not describe
decode**, where the same entry is a refusal. `E4-SCHEMA-CE-011` must fix a
direction before it can be discharged; the two directions have different
answers.

### The pruning predicate, exactly

`SchemaAST.isJson` (`SchemaAST.ts:4347-4349`) is a stack-based tree walk
(`isTree`, `:4280-4338`) over the leaf predicate `isJsonLeaf`
(`:4271-4274`), which admits only `null`, `string`, `boolean`, and **finite**
numbers. Therefore an annotation value is pruned on encode when it is, or
transitively contains, any of:

- `undefined`, a `symbol`, a `bigint`, or a function — none is an `isJsonLeaf`;
- `NaN` or an infinity — excluded by the `Number.isFinite` conjunct at `:4273`;
- an object whose prototype is neither `null` nor `Object.prototype` nor
  itself null-prototyped, i.e. a class instance (`:4298-4308`);
- anything cyclic — a node already on the current path returns `false`
  (`:4293-4295`, documented at `:4343`).

Note the third domain split this creates, alongside the `Finite`-versus-
`Number` split already registered as `E4-SCHEMA-CE-023`: an annotation payload
may not hold a non-finite number, whereas an `Enum` value or a property-name
number may (`SchemaRepresentation.ts:999`, used at `:1020` and `:1042`). The
`Filter.representation.payload` field is `Schema.Json` (`:919`) and is bound
by the same finiteness restriction as an annotation value.

### One canonicalisation fact this yields for free

`annotations: {}` **decodes** (nothing in `JsonObject` forbids it) but is never
**produced** by encode (`:936` omits instead). Observed: a document carrying
`annotations: {}` survives `fromJson` unchanged and re-encodes with the key
absent. So `encode ∘ decode` is a canonicalising map on this field and not the
identity — which is the shape `docs/research/SCHEMA-CUTOVER.md` already requires of
`SC-WIRE-03`, stated there as `encode (decode acceptedBytes) =
canonicalize acceptedBytes`. This observation is one witness consistent with
that requirement on one input. It is not a proof of it, and it discharges
neither `SC-WIRE-03` nor `SC-WIRE-04`.
-/

/-!
## Retains

Rows this module's future admission checker must answer, with the part of the
answer that is now pinned rather than assumed:

- `E4-SCHEMA-CE-011` non-JSON annotation pruning — the policy is
  direction-dependent: silent pruning with key omission on encode
  (`SchemaRepresentation.ts:927-948`), refusal on decode (`:940-941`). The
  witness must name a direction. The pruning predicate is
  `SchemaAST.isJson` (`SchemaAST.ts:4271-4274`, `:4347-4349`) and excludes
  non-finite numbers, so the witness family overlaps `E4-SCHEMA-CE-023`.
- `E4-SCHEMA-CE-010` local symbol cannot enter portable wire data — a check's
  `representation.schemas` (`SchemaRepresentation.ts:37`, `:924`) is a further
  entry point for representations carrying symbol-keyed properties, so the
  lowering argument must cover the check position too, not only the object
  position.

Two admission conditions this module owns that are visible only from the
codec, never from the interfaces:

- `Filter.representation` must be present (`:958`), though rc.112's own
  lowering can build a `Filter` without it (`toRepresentation.ts:351-357`);
- a check's `representation.id` must be non-empty (`:918`), though the
  interface types it as plain `string` (`:26`).

Both are field-admission facts and belong to `SC-REP-04`.

## Implemented boundary, restated for the check layer

The payload and recursive `Check` carriers are imported below. The judgment is
total over their frozen constructor surface, including the
`Filter.representation.schemas` position rather than only
`FilterGroup.checks`. It does not classify target profiles.
-/

namespace Effect4

/-!
## Annotation-bag admission

An ordinary annotation bag that is already present in persisted input is
decoded through `Schema.JsonObject` (`SchemaRepresentation.ts:940-941`), which
refuses a non-finite number. Encode-side pruning
(`pruneAnnotations`, `:927-937`) drops such an entry silently instead, so the
policy is direction-dependent and this judgment is the **decode** direction
only. `E4-SCHEMA-CE-011` must name its direction; this packet asserts nothing
about the encode side.

Annotation *keys* carry no non-emptiness constraint. Only `$ref` and the two
representation-annotation `id` fields do.
-/

/-- Every entry of a present annotation bag carries finite JSON. -/
def Annotations.FieldAdmissible : Annotations → Prop
  | none => True
  | some entries => ∀ entry ∈ entries, Json.NumbersFinite entry.payload

/-- The decidable companion of `Annotations.FieldAdmissible`. -/
def Annotations.fieldAdmissible : Annotations → Bool
  | none => true
  | some entries => entries.all fun entry => Json.numbersFinite entry.payload

/-- Boolean and propositional annotation admission agree. -/
theorem Annotations.fieldAdmissible_iff (annotations : Annotations) :
    Annotations.fieldAdmissible annotations = true ↔
      Annotations.FieldAdmissible annotations := by
  cases annotations with
  | none => simp [Annotations.fieldAdmissible, Annotations.FieldAdmissible]
  | some entries =>
      simp [Annotations.fieldAdmissible, Annotations.FieldAdmissible,
        Json.numbersFinite_iff]

/-- An absent bag is admissible; absent and empty remain distinct carrier states. -/
theorem Annotations.fieldAdmissible_none : Annotations.FieldAdmissible none := True.intro

/-- A present bag is admissible exactly when every entry payload is finite JSON. -/
theorem Annotations.fieldAdmissible_some_iff (entries : List AnnotationEntry) :
    Annotations.FieldAdmissible (some entries) ↔
      ∀ entry ∈ entries, Json.NumbersFinite entry.payload := Iff.rfl

/-!
## Field admission, `SC-REP-04`

`FieldAdmissible` is exactly the pinned rc.112 constraints on a persisted value
being decoded into the carrier. It is a proposition with a Boolean decision
procedure, not a refusal or issue value: there is no `Diagnostic`, no site, no
scan order, no first-condemning clause, and no private checked-value
constructor. Any later diagnostic API needs its own contract and evidence; it
is not predesigned by this judgment.

The judgment visits every representation child route and all three
check-constructor routes: `Filter.representation.schemas`,
`FilterGroup.representation.schemas`, and `FilterGroup.checks`. That is two
recursive field forms but three constructor routes, and the first is the one a
`FilterGroup.checks`-only traversal silently skips (`E4-SCHEMA-CE-033`).

Deliberately **not** clauses, each with its reason:

- *enum value or name uniqueness* — `enums` is a plain `Schema.Array`
  (`SchemaRepresentation.ts:1018-1021`) and aliases are permitted. A uniqueness
  clause makes the reserved `E4-SCHEMA-CE-003` witness unspellable.
- *optional-before-required tuple elements* — `elements` is a plain
  `Schema.Array` with per-element `isOptional` (`:1036`). The reserved
  `E4-SCHEMA-CE-004` needs the malformed value to remain expressible. This is a
  field-shape result only; a later denotation may still reject the sequence.
- *non-finite enum values and numeric property keys* — those legs are
  `Schema.Number`, not `Schema.Finite` (`:999` used at `:1020` and `:1042`).
- *annotation keys and string property keys* — no non-emptiness constraint at
  the pin.
- *reference resolution, reachability, guardedness, dead entries* — `SC-DOC-*`.
- *duplicate raw-JSON or references-table keys* — `SC-WIRE-01`.
- *property-key uniqueness* — deferred: it cannot freeze before the key
  equivalence relation does, because structural `Float64` equality separates
  `+0` from `-0` and every NaN payload while host or wire key equivalence may
  not. `E4-SCHEMA-CE-037` remains owed.

`E4-SCHEMA-CE-035` is the row that keeps this list honest: an admission that
normalized any of them away would pass its own refusal tests and silently make
four reserved counterexample rows unprovable.
-/

mutual

/-- Every rc.112 field clause holds at this node and everywhere below it. -/
def Representation.FieldAdmissible : Representation → Prop
  | .declaration rep ann tps cs =>
      rep.id ≠ "" ∧ Json.NumbersFinite rep.payload ∧
        Annotations.FieldAdmissible ann ∧ Representation.FieldAdmissibleList tps ∧
        Check.FieldAdmissibleList cs
  | .reference key =>
      key.value ≠ ""
  | .suspend ann cs th =>
      Annotations.FieldAdmissible ann ∧ cs = [] ∧
        Representation.FieldAdmissible th
  | .null ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .undefined ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .void ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .never ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .unknown ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .any ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .string ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .number ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .boolean ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .bigint ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .symbol ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .literal ann cs (.number value) =>
      Annotations.FieldAdmissible ann ∧ Float64.isFinite value = true ∧
        Check.FieldAdmissibleList cs
  | .literal ann cs _ =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .uniqueSymbol ann cs _ =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .objectKeyword ann cs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .enum ann cs _ =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs
  | .templateLiteral ann cs ps =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs ∧
        Representation.FieldAdmissibleList ps
  | .arrays ann cs els rs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs ∧
        Representation.FieldAdmissibleElements els ∧
        Representation.FieldAdmissibleList rs
  | .objects ann cs props idxs =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs ∧
        Representation.FieldAdmissibleProperties props ∧
        Representation.FieldAdmissibleIndexes idxs
  | .union ann cs ts _ =>
      Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs ∧
        Representation.FieldAdmissibleList ts

/-- Field admission over an ordered list of representations. -/
private def Representation.FieldAdmissibleList : List Representation → Prop
  | [] => True
  | head :: tail =>
      Representation.FieldAdmissible head ∧ Representation.FieldAdmissibleList tail

/-- Field admission over an ordered list of tuple elements. -/
private def Representation.FieldAdmissibleElements :
    List (ElementOf Representation) → Prop
  | [] => True
  | ⟨_, ty, ann⟩ :: tail =>
      (Annotations.FieldAdmissible ann ∧ Representation.FieldAdmissible ty) ∧
        Representation.FieldAdmissibleElements tail

/-- Field admission over an ordered list of property signatures. -/
private def Representation.FieldAdmissibleProperties :
    List (PropertySignatureOf Representation) → Prop
  | [] => True
  | ⟨_, ty, _, _, ann⟩ :: tail =>
      (Annotations.FieldAdmissible ann ∧ Representation.FieldAdmissible ty) ∧
        Representation.FieldAdmissibleProperties tail

/-- Field admission over an ordered list of index signatures. -/
private def Representation.FieldAdmissibleIndexes :
    List (IndexSignatureOf Representation) → Prop
  | [] => True
  | ⟨par, ty⟩ :: tail =>
      (Representation.FieldAdmissible par ∧ Representation.FieldAdmissible ty) ∧
        Representation.FieldAdmissibleIndexes tail

/-- Field admission over the representations a check references. -/
private def Representation.FieldAdmissibleSchemas : Option (List Representation) → Prop
  | none => True
  | some schemas => Representation.FieldAdmissibleList schemas

/-- Every rc.112 field clause holds at this check and everywhere below it. -/
def Check.FieldAdmissible : Check → Prop
  | .filter ⟨id, payload, schemas⟩ ann _ =>
      id ≠ "" ∧ Json.NumbersFinite payload ∧ Annotations.FieldAdmissible ann ∧
        Representation.FieldAdmissibleSchemas schemas
  | .filterGroup rep ann cs =>
      cs ≠ [] ∧ Annotations.FieldAdmissible ann ∧ Check.FieldAdmissibleList cs ∧
        Check.AnnotationFieldAdmissible rep

/-- Field admission over an ordered list of checks. -/
private def Check.FieldAdmissibleList : List Check → Prop
  | [] => True
  | head :: tail => Check.FieldAdmissible head ∧ Check.FieldAdmissibleList tail

/-- Field admission over a `FilterGroup`'s optional representation annotation. -/
private def Check.AnnotationFieldAdmissible :
    Option (CheckRepresentationAnnotationOf Representation) → Prop
  | none => True
  | some ⟨id, payload, schemas⟩ =>
      id ≠ "" ∧ Json.NumbersFinite payload ∧
        Representation.FieldAdmissibleSchemas schemas

end

mutual

/-- The decidable companion of `Representation.FieldAdmissible`. -/
def Representation.fieldAdmissible : Representation → Bool
  | .declaration rep ann tps cs =>
      rep.id != "" && Json.numbersFinite rep.payload &&
        Annotations.fieldAdmissible ann && Representation.fieldAdmissibleList tps &&
        Check.fieldAdmissibleList cs
  | .reference key =>
      key.value != ""
  | .suspend ann cs th =>
      Annotations.fieldAdmissible ann && cs.isEmpty &&
        Representation.fieldAdmissible th
  | .null ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .undefined ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .void ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .never ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .unknown ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .any ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .string ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .number ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .boolean ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .bigint ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .symbol ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .literal ann cs (.number value) =>
      Annotations.fieldAdmissible ann && Float64.isFinite value &&
        Check.fieldAdmissibleList cs
  | .literal ann cs _ =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .uniqueSymbol ann cs _ =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .objectKeyword ann cs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .enum ann cs _ =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs
  | .templateLiteral ann cs ps =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs &&
        Representation.fieldAdmissibleList ps
  | .arrays ann cs els rs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs &&
        Representation.fieldAdmissibleElements els &&
        Representation.fieldAdmissibleList rs
  | .objects ann cs props idxs =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs &&
        Representation.fieldAdmissibleProperties props &&
        Representation.fieldAdmissibleIndexes idxs
  | .union ann cs ts _ =>
      Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs &&
        Representation.fieldAdmissibleList ts

/-- The decidable companion of `Representation.FieldAdmissibleList`. -/
private def Representation.fieldAdmissibleList : List Representation → Bool
  | [] => true
  | head :: tail =>
      Representation.fieldAdmissible head && Representation.fieldAdmissibleList tail

/-- The decidable companion of `Representation.FieldAdmissibleElements`. -/
private def Representation.fieldAdmissibleElements :
    List (ElementOf Representation) → Bool
  | [] => true
  | ⟨_, ty, ann⟩ :: tail =>
      (Annotations.fieldAdmissible ann && Representation.fieldAdmissible ty) &&
        Representation.fieldAdmissibleElements tail

/-- The decidable companion of `Representation.FieldAdmissibleProperties`. -/
private def Representation.fieldAdmissibleProperties :
    List (PropertySignatureOf Representation) → Bool
  | [] => true
  | ⟨_, ty, _, _, ann⟩ :: tail =>
      (Annotations.fieldAdmissible ann && Representation.fieldAdmissible ty) &&
        Representation.fieldAdmissibleProperties tail

/-- The decidable companion of `Representation.FieldAdmissibleIndexes`. -/
private def Representation.fieldAdmissibleIndexes :
    List (IndexSignatureOf Representation) → Bool
  | [] => true
  | ⟨par, ty⟩ :: tail =>
      (Representation.fieldAdmissible par && Representation.fieldAdmissible ty) &&
        Representation.fieldAdmissibleIndexes tail

/-- The decidable companion of `Representation.FieldAdmissibleSchemas`. -/
private def Representation.fieldAdmissibleSchemas : Option (List Representation) → Bool
  | none => true
  | some schemas => Representation.fieldAdmissibleList schemas

/-- The decidable companion of `Check.FieldAdmissible`. -/
def Check.fieldAdmissible : Check → Bool
  | .filter ⟨id, payload, schemas⟩ ann _ =>
      (id != "") && Json.numbersFinite payload && Annotations.fieldAdmissible ann &&
        Representation.fieldAdmissibleSchemas schemas
  | .filterGroup rep ann cs =>
      !cs.isEmpty && Annotations.fieldAdmissible ann && Check.fieldAdmissibleList cs &&
        Check.annotationFieldAdmissible rep

/-- The decidable companion of `Check.FieldAdmissibleList`. -/
private def Check.fieldAdmissibleList : List Check → Bool
  | [] => true
  | head :: tail => Check.fieldAdmissible head && Check.fieldAdmissibleList tail

/-- The decidable companion of `Check.AnnotationFieldAdmissible`. -/
private def Check.annotationFieldAdmissible :
    Option (CheckRepresentationAnnotationOf Representation) → Bool
  | none => true
  | some ⟨id, payload, schemas⟩ =>
      (id != "") && Json.numbersFinite payload &&
        Representation.fieldAdmissibleSchemas schemas

end

/-!
## Membership forms of the list clauses

The recursive list predicates above are what the structural recursion needs;
the membership forms are what the contract states. These bridges keep the two
readings from drifting apart.
-/

/-- List admission is admission of every member. -/
private theorem Representation.fieldAdmissibleList_forall (representations : List Representation) :
    Representation.FieldAdmissibleList representations ↔
      ∀ child ∈ representations, Representation.FieldAdmissible child := by
  induction representations with
  | nil => simp [Representation.FieldAdmissibleList]
  | cons _ _ ih => simp [Representation.FieldAdmissibleList, ih]

/-- Element admission is admission of every element's annotations and type. -/
private theorem Representation.fieldAdmissibleElements_forall
    (elements : List (ElementOf Representation)) :
    Representation.FieldAdmissibleElements elements ↔
      ∀ element ∈ elements,
        Annotations.FieldAdmissible element.annotations ∧
          Representation.FieldAdmissible element.type := by
  induction elements with
  | nil => simp [Representation.FieldAdmissibleElements]
  | cons _ _ ih => simp [Representation.FieldAdmissibleElements, ih]

/-- Property admission is admission of every signature's annotations and type. -/
private theorem Representation.fieldAdmissibleProperties_forall
    (properties : List (PropertySignatureOf Representation)) :
    Representation.FieldAdmissibleProperties properties ↔
      ∀ property ∈ properties,
        Annotations.FieldAdmissible property.annotations ∧
          Representation.FieldAdmissible property.type := by
  induction properties with
  | nil => simp [Representation.FieldAdmissibleProperties]
  | cons _ _ ih => simp [Representation.FieldAdmissibleProperties, ih]

/-- Index admission is admission of every signature's parameter and type. -/
private theorem Representation.fieldAdmissibleIndexes_forall
    (indexes : List (IndexSignatureOf Representation)) :
    Representation.FieldAdmissibleIndexes indexes ↔
      ∀ index ∈ indexes,
        Representation.FieldAdmissible index.parameter ∧
          Representation.FieldAdmissible index.type := by
  induction indexes with
  | nil => simp [Representation.FieldAdmissibleIndexes]
  | cons _ _ ih => simp [Representation.FieldAdmissibleIndexes, ih]

/-- Referenced-schema admission, in the form the contract states it. -/
private theorem Representation.fieldAdmissibleSchemas_forall
    (schemas : Option (List Representation)) :
    Representation.FieldAdmissibleSchemas schemas ↔
      ∀ list : List Representation, schemas = some list →
        ∀ child ∈ list, Representation.FieldAdmissible child := by
  cases schemas with
  | none => simp [Representation.FieldAdmissibleSchemas]
  | some list =>
      simp [Representation.FieldAdmissibleSchemas,
        Representation.fieldAdmissibleList_forall]

/-- Check-list admission is admission of every member. -/
private theorem Check.fieldAdmissibleList_forall (checks : List Check) :
    Check.FieldAdmissibleList checks ↔
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  induction checks with
  | nil => simp [Check.FieldAdmissibleList]
  | cons _ _ ih => simp [Check.FieldAdmissibleList, ih]

/-- The optional check annotation clause, in the form the contract states it. -/
private theorem Check.annotationFieldAdmissible_forall
    (annotation : Option (CheckRepresentationAnnotationOf Representation)) :
    Check.AnnotationFieldAdmissible annotation ↔
      ∀ value : CheckRepresentationAnnotationOf Representation,
        annotation = some value →
          value.id ≠ "" ∧ Json.NumbersFinite value.payload ∧
            ∀ list : List Representation, value.schemas = some list →
              ∀ child ∈ list, Representation.FieldAdmissible child := by
  cases annotation with
  | none => simp [Check.AnnotationFieldAdmissible]
  | some value =>
      obtain ⟨_, _, _⟩ := value
      simp [Check.AnnotationFieldAdmissible,
        Representation.fieldAdmissibleSchemas_forall]

/-!
## Boolean and propositional agreement

The Boolean decision procedure and the proposition are written separately and
proved to agree, so neither is the other's definition. Agreement alone is not a
specification — both sides could be constant — which is why the per-constructor
equations below are separate obligations.
-/

mutual

/-- Boolean and propositional field admission agree on representations. -/
theorem Representation.fieldAdmissible_iff (representation : Representation) :
    Representation.fieldAdmissible representation = true ↔
      Representation.FieldAdmissible representation := by
  cases representation
  case suspend ann cs th =>
    simp [Representation.fieldAdmissible, Representation.FieldAdmissible,
      Annotations.fieldAdmissible_iff, Representation.fieldAdmissible_iff th,
      List.isEmpty_iff, and_assoc]
  case literal ann cs value =>
    cases value <;>
      simp [Representation.fieldAdmissible, Representation.FieldAdmissible,
        Annotations.fieldAdmissible_iff, Check.fieldAdmissibleList_iff cs, and_assoc]
  all_goals
    simp [Representation.fieldAdmissible, Representation.FieldAdmissible,
      Annotations.fieldAdmissible_iff, Json.numbersFinite_iff,
      Representation.fieldAdmissibleList_iff, Check.fieldAdmissibleList_iff,
      Representation.fieldAdmissibleElements_iff,
      Representation.fieldAdmissibleProperties_iff,
      Representation.fieldAdmissibleIndexes_iff, and_assoc]
termination_by structural representation

/-- Agreement for an ordered list of representations. -/
private theorem Representation.fieldAdmissibleList_iff (representations : List Representation) :
    Representation.fieldAdmissibleList representations = true ↔
      Representation.FieldAdmissibleList representations := by
  match representations with
  | [] =>
      simp [Representation.fieldAdmissibleList, Representation.FieldAdmissibleList]
  | head :: tail =>
      simp [Representation.fieldAdmissibleList, Representation.FieldAdmissibleList,
        Representation.fieldAdmissible_iff head,
        Representation.fieldAdmissibleList_iff tail]
termination_by structural representations

/-- Agreement for an ordered list of tuple elements. -/
private theorem Representation.fieldAdmissibleElements_iff
    (elements : List (ElementOf Representation)) :
    Representation.fieldAdmissibleElements elements = true ↔
      Representation.FieldAdmissibleElements elements := by
  match elements with
  | [] =>
      simp [Representation.fieldAdmissibleElements,
        Representation.FieldAdmissibleElements]
  | ⟨_, ty, _⟩ :: tail =>
      simp [Representation.fieldAdmissibleElements,
        Representation.FieldAdmissibleElements, Annotations.fieldAdmissible_iff,
        Representation.fieldAdmissible_iff ty,
        Representation.fieldAdmissibleElements_iff tail, and_assoc]
termination_by structural elements

/-- Agreement for an ordered list of property signatures. -/
private theorem Representation.fieldAdmissibleProperties_iff
    (properties : List (PropertySignatureOf Representation)) :
    Representation.fieldAdmissibleProperties properties = true ↔
      Representation.FieldAdmissibleProperties properties := by
  match properties with
  | [] =>
      simp [Representation.fieldAdmissibleProperties,
        Representation.FieldAdmissibleProperties]
  | ⟨_, ty, _, _, _⟩ :: tail =>
      simp [Representation.fieldAdmissibleProperties,
        Representation.FieldAdmissibleProperties, Annotations.fieldAdmissible_iff,
        Representation.fieldAdmissible_iff ty,
        Representation.fieldAdmissibleProperties_iff tail, and_assoc]
termination_by structural properties

/-- Agreement for an ordered list of index signatures. -/
private theorem Representation.fieldAdmissibleIndexes_iff
    (indexes : List (IndexSignatureOf Representation)) :
    Representation.fieldAdmissibleIndexes indexes = true ↔
      Representation.FieldAdmissibleIndexes indexes := by
  match indexes with
  | [] =>
      simp [Representation.fieldAdmissibleIndexes,
        Representation.FieldAdmissibleIndexes]
  | ⟨par, ty⟩ :: tail =>
      simp [Representation.fieldAdmissibleIndexes,
        Representation.FieldAdmissibleIndexes,
        Representation.fieldAdmissible_iff par, Representation.fieldAdmissible_iff ty,
        Representation.fieldAdmissibleIndexes_iff tail, and_assoc]
termination_by structural indexes

/-- Agreement for the representations a check references. -/
private theorem Representation.fieldAdmissibleSchemas_iff
    (schemas : Option (List Representation)) :
    Representation.fieldAdmissibleSchemas schemas = true ↔
      Representation.FieldAdmissibleSchemas schemas := by
  match schemas with
  | none =>
      simp [Representation.fieldAdmissibleSchemas,
        Representation.FieldAdmissibleSchemas]
  | some list =>
      simp [Representation.fieldAdmissibleSchemas,
        Representation.FieldAdmissibleSchemas,
        Representation.fieldAdmissibleList_iff list]
termination_by structural schemas

/-- Boolean and propositional field admission agree on checks. -/
theorem Check.fieldAdmissible_iff (check : Check) :
    Check.fieldAdmissible check = true ↔ Check.FieldAdmissible check := by
  match check with
  | .filter ⟨_, _, schemas⟩ ann _ =>
      simp [Check.fieldAdmissible, Check.FieldAdmissible,
        Annotations.fieldAdmissible_iff, Json.numbersFinite_iff,
        Representation.fieldAdmissibleSchemas_iff schemas, and_assoc]
  | .filterGroup rep ann cs =>
      simp [Check.fieldAdmissible, Check.FieldAdmissible,
        Annotations.fieldAdmissible_iff, Check.fieldAdmissibleList_iff cs,
        Check.annotationFieldAdmissible_iff rep, and_assoc]
termination_by structural check

/-- Agreement for an ordered list of checks. -/
private theorem Check.fieldAdmissibleList_iff (checks : List Check) :
    Check.fieldAdmissibleList checks = true ↔ Check.FieldAdmissibleList checks := by
  match checks with
  | [] => simp [Check.fieldAdmissibleList, Check.FieldAdmissibleList]
  | head :: tail =>
      simp [Check.fieldAdmissibleList, Check.FieldAdmissibleList,
        Check.fieldAdmissible_iff head, Check.fieldAdmissibleList_iff tail]
termination_by structural checks

/-- Agreement for a `FilterGroup`'s optional representation annotation. -/
private theorem Check.annotationFieldAdmissible_iff
    (annotation : Option (CheckRepresentationAnnotationOf Representation)) :
    Check.annotationFieldAdmissible annotation = true ↔
      Check.AnnotationFieldAdmissible annotation := by
  match annotation with
  | none =>
      simp [Check.annotationFieldAdmissible, Check.AnnotationFieldAdmissible]
  | some ⟨_, _, schemas⟩ =>
      simp [Check.annotationFieldAdmissible, Check.AnnotationFieldAdmissible,
        Json.numbersFinite_iff, Representation.fieldAdmissibleSchemas_iff schemas,
        and_assoc]
termination_by structural annotation

end

/-!
## The compositional specification

Boolean and propositional agreement is not a specification by itself: both
sides could be constant. These equations fix the proposition on every
constructor and every recursive route, including all three check-constructor
routes.
-/

/-- `Declaration`: annotation clauses, type parameters, and checks. -/
theorem Representation.fieldAdmissible_declaration_iff
    (annotation : RepresentationAnnotation) (annotations : Annotations)
    (types : List Representation) (checks : List Check) :
    Representation.FieldAdmissible
        (Representation.declaration annotation annotations types checks) ↔
      annotation.id ≠ "" ∧
      Json.NumbersFinite annotation.payload ∧
      Annotations.FieldAdmissible annotations ∧
      (∀ child ∈ types, Representation.FieldAdmissible child) ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) := by
  simp [Representation.FieldAdmissible, Representation.fieldAdmissibleList_forall,
    Check.fieldAdmissibleList_forall]

/-- `Reference`: exactly the non-empty `$ref` clause. -/
theorem Representation.fieldAdmissible_reference_iff (key : ReferenceKey) :
    Representation.FieldAdmissible (Representation.reference key) ↔
      key.value ≠ "" := by
  simp [Representation.FieldAdmissible]

/-- `Suspend`: its `checks` are present and exactly empty. -/
theorem Representation.fieldAdmissible_suspend_iff (annotations : Annotations)
    (checks : List Check) (thunk : Representation) :
    Representation.FieldAdmissible
        (Representation.suspend annotations checks thunk) ↔
      Annotations.FieldAdmissible annotations ∧
      checks = [] ∧ Representation.FieldAdmissible thunk := by
  simp [Representation.FieldAdmissible]

/-- The `null` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_null_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.null annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `undefined` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_undefined_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.undefined annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `void` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_void_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.void annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `never` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_never_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.never annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `unknown` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_unknown_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.unknown annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `any` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_any_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.any annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `string` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_string_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.string annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `number` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_number_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.number annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `boolean` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_boolean_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.boolean annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `bigint` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_bigint_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.bigint annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `symbol` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_symbol_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible (Representation.symbol annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- A string literal carries no value clause. -/
theorem Representation.fieldAdmissible_literal_string_iff
    (annotations : Annotations) (checks : List Check) (value : String) :
    Representation.FieldAdmissible
        (Representation.literal annotations checks (LiteralValue.string value)) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `Literal` number leg is `Schema.Finite`; the other three legs are not
constrained. -/
theorem Representation.fieldAdmissible_literal_number_iff
    (annotations : Annotations) (checks : List Check) (value : Float64) :
    Representation.FieldAdmissible
        (Representation.literal annotations checks (LiteralValue.number value)) ↔
      Annotations.FieldAdmissible annotations ∧
      Float64.isFinite value = true ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/--
Finiteness enters at admission, not at the embedding.

`EnumValue.toLiteralValue` is total and copies the datum unchanged. This is
the theorem that says where the `Literal` leg's `Schema.Finite` constraint
actually bites: a string enum value is admitted unconditionally, and a number
enum value is admitted exactly when it is finite. Together with the totality
of the embedding it prevents a builder from hiding admission inside the
embedding, which would put the refusal a layer too early and discard the datum
before admission could speak about it. `E4-SCHEMA-CE-028`.
-/
theorem Representation.fieldAdmissible_toLiteralValue_iff (value : EnumValue) :
    Representation.FieldAdmissible
        (Representation.literal none [] (EnumValue.toLiteralValue value)) ↔
      match value with
      | .string _ => True
      | .number datum => Float64.isFinite datum = true := by
  cases value with
  | string text =>
      simp [EnumValue.toLiteralValue,
        Representation.fieldAdmissible_literal_string_iff,
        Annotations.FieldAdmissible]
  | number datum =>
      simp [EnumValue.toLiteralValue,
        Representation.fieldAdmissible_literal_number_iff,
        Annotations.FieldAdmissible]

/-- The forward corollary of `fieldAdmissible_toLiteralValue_iff`, in the
direction a caller uses: a finite enum datum yields an admissible literal. -/
theorem Representation.fieldAdmissible_toLiteralValue_of_finite (value : EnumValue)
    (finite : match value with
      | .string _ => True
      | .number datum => Float64.isFinite datum = true) :
    Representation.FieldAdmissible
      (Representation.literal none [] (EnumValue.toLiteralValue value)) :=
  (Representation.fieldAdmissible_toLiteralValue_iff value).mpr finite

/-- A bigint literal carries no value clause. -/
theorem Representation.fieldAdmissible_literal_bigint_iff
    (annotations : Annotations) (checks : List Check) (value : Int) :
    Representation.FieldAdmissible
        (Representation.literal annotations checks (LiteralValue.bigint value)) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- A boolean literal carries no value clause. -/
theorem Representation.fieldAdmissible_literal_boolean_iff
    (annotations : Annotations) (checks : List Check) (value : Bool) :
    Representation.FieldAdmissible
        (Representation.literal annotations checks (LiteralValue.boolean value)) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- `UniqueSymbol`: the symbol key carries no clause. -/
theorem Representation.fieldAdmissible_uniqueSymbol_iff (annotations : Annotations)
    (checks : List Check) (key : GlobalSymbolKey) :
    Representation.FieldAdmissible
        (Representation.uniqueSymbol annotations checks key) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- The `object` keyword: annotations and checks only. -/
theorem Representation.fieldAdmissible_objectKeyword_iff (annotations : Annotations)
    (checks : List Check) :
    Representation.FieldAdmissible
        (Representation.objectKeyword annotations checks) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- `Enum`: entries carry no clause at all, so aliases and non-finite values
survive. -/
theorem Representation.fieldAdmissible_enum_iff (annotations : Annotations)
    (checks : List Check) (entries : List EnumEntry) :
    Representation.FieldAdmissible
        (Representation.enum annotations checks entries) ↔
      Annotations.FieldAdmissible annotations ∧
      ∀ check ∈ checks, Check.FieldAdmissible check := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall]

/-- `TemplateLiteral`: every part is visited. -/
theorem Representation.fieldAdmissible_templateLiteral_iff
    (annotations : Annotations) (checks : List Check)
    (parts : List Representation) :
    Representation.FieldAdmissible
        (Representation.templateLiteral annotations checks parts) ↔
      Annotations.FieldAdmissible annotations ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ part ∈ parts, Representation.FieldAdmissible part) := by
  simp [Representation.FieldAdmissible, Representation.fieldAdmissibleList_forall,
    Check.fieldAdmissibleList_forall]

/-- `Arrays`: element annotations and element types are both visited. -/
theorem Representation.fieldAdmissible_arrays_iff (annotations : Annotations)
    (checks : List Check) (elements : List (ElementOf Representation))
    (rest : List Representation) :
    Representation.FieldAdmissible
        (Representation.arrays annotations checks elements rest) ↔
      Annotations.FieldAdmissible annotations ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ element ∈ elements,
        Annotations.FieldAdmissible element.annotations ∧
        Representation.FieldAdmissible element.type) ∧
      (∀ child ∈ rest, Representation.FieldAdmissible child) := by
  simp [Representation.FieldAdmissible, Representation.fieldAdmissibleList_forall,
    Check.fieldAdmissibleList_forall,
    Representation.fieldAdmissibleElements_forall]

/-- `Objects`: property annotations, property types, and both index positions. -/
theorem Representation.fieldAdmissible_objects_iff (annotations : Annotations)
    (checks : List Check)
    (properties : List (PropertySignatureOf Representation))
    (indexes : List (IndexSignatureOf Representation)) :
    Representation.FieldAdmissible
        (Representation.objects annotations checks properties indexes) ↔
      Annotations.FieldAdmissible annotations ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ property ∈ properties,
        Annotations.FieldAdmissible property.annotations ∧
        Representation.FieldAdmissible property.type) ∧
      (∀ index ∈ indexes,
        Representation.FieldAdmissible index.parameter ∧
        Representation.FieldAdmissible index.type) := by
  simp [Representation.FieldAdmissible, Check.fieldAdmissibleList_forall,
    Representation.fieldAdmissibleProperties_forall,
    Representation.fieldAdmissibleIndexes_forall]

/-- `Union`: every member is visited; the mode carries no clause. -/
theorem Representation.fieldAdmissible_union_iff (annotations : Annotations)
    (checks : List Check) (types : List Representation) (mode : UnionMode) :
    Representation.FieldAdmissible
        (Representation.union annotations checks types mode) ↔
      Annotations.FieldAdmissible annotations ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ child ∈ types, Representation.FieldAdmissible child) := by
  simp [Representation.FieldAdmissible, Representation.fieldAdmissibleList_forall,
    Check.fieldAdmissibleList_forall]

/-- `Filter`: route 1, the referenced schemas of a required annotation. -/
theorem Check.fieldAdmissible_filter_iff
    (annotation : CheckRepresentationAnnotationOf Representation)
    (annotations : Annotations) (aborted : Bool) :
    Check.FieldAdmissible (Check.filter annotation annotations aborted) ↔
      annotation.id ≠ "" ∧
      Json.NumbersFinite annotation.payload ∧
      Annotations.FieldAdmissible annotations ∧
      (∀ schemas : List Representation, annotation.schemas = some schemas →
        ∀ child ∈ schemas, Representation.FieldAdmissible child) := by
  obtain ⟨_, _, _⟩ := annotation
  simp [Check.FieldAdmissible, Representation.fieldAdmissibleSchemas_forall]

/-- `FilterGroup`: routes 2 and 3, the optional annotation and the check list. -/
theorem Check.fieldAdmissible_filterGroup_iff
    (annotation : Option (CheckRepresentationAnnotationOf Representation))
    (annotations : Annotations) (checks : List Check) :
    Check.FieldAdmissible (Check.filterGroup annotation annotations checks) ↔
      checks ≠ [] ∧
      Annotations.FieldAdmissible annotations ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ value : CheckRepresentationAnnotationOf Representation,
        annotation = some value →
          value.id ≠ "" ∧
          Json.NumbersFinite value.payload ∧
          (∀ schemas : List Representation, value.schemas = some schemas →
            ∀ child ∈ schemas, Representation.FieldAdmissible child)) := by
  simp [Check.FieldAdmissible, Check.fieldAdmissibleList_forall,
    Check.annotationFieldAdmissible_forall]

/-!
## Documents

No reference edge is interpreted. At the pin a dangling `$ref` is accepted by
the document codec `fromJson` and refused by the revival layer
`fromRepresentation`; neither is a field constraint (`E4-SCHEMA-CE-040`).
Reference-key uniqueness for both document shapes belongs to
`Effect4.Protocol.Bytes` under `SCHEMA-PG-WIRE`, before either ordered list is
collapsed to a map, and no such declaration appears here.
-/

/-- A document is field-admissible when its root and every table entry are. -/
def Document.FieldAdmissible (document : Document) : Prop :=
  Representation.FieldAdmissible document.representation ∧
    ∀ entry ∈ document.references,
      Representation.FieldAdmissible entry.representation

/-- The decidable companion of `Document.FieldAdmissible`. -/
def Document.fieldAdmissible (document : Document) : Bool :=
  Representation.fieldAdmissible document.representation &&
    document.references.all fun entry =>
      Representation.fieldAdmissible entry.representation

/-- Boolean and propositional field admission agree on documents. -/
theorem Document.fieldAdmissible_iff (document : Document) :
    Document.fieldAdmissible document = true ↔ Document.FieldAdmissible document := by
  simp [Document.fieldAdmissible, Document.FieldAdmissible,
    Representation.fieldAdmissible_iff]

/-- The document clause, per constructor. The table key carries no clause. -/
theorem Document.fieldAdmissible_mk_iff (root : Representation)
    (references : List ReferenceEntry) :
    Document.FieldAdmissible (Document.mk root references) ↔
      Representation.FieldAdmissible root ∧
      (∀ entry ∈ references,
        Representation.FieldAdmissible entry.representation) := Iff.rfl

/--
A multi-root document is field-admissible when its roots are non-empty and
every root and table entry is.

`representations: Schema.NonEmptyArray` (`SchemaRepresentation.ts:1107`).
-/
def MultiDocument.FieldAdmissible (multi : MultiDocument) : Prop :=
  multi.representations ≠ [] ∧
    (∀ root ∈ multi.representations, Representation.FieldAdmissible root) ∧
    ∀ entry ∈ multi.references, Representation.FieldAdmissible entry.representation

/-- The decidable companion of `MultiDocument.FieldAdmissible`. -/
def MultiDocument.fieldAdmissible (multi : MultiDocument) : Bool :=
  !multi.representations.isEmpty &&
    multi.representations.all Representation.fieldAdmissible &&
    multi.references.all fun entry =>
      Representation.fieldAdmissible entry.representation

/-- Boolean and propositional field admission agree on multi-root documents. -/
theorem MultiDocument.fieldAdmissible_iff (multi : MultiDocument) :
    MultiDocument.fieldAdmissible multi = true ↔
      MultiDocument.FieldAdmissible multi := by
  simp [MultiDocument.fieldAdmissible, MultiDocument.FieldAdmissible,
    Representation.fieldAdmissible_iff, and_assoc]

/-- The multi-root document clause, per constructor. -/
theorem MultiDocument.fieldAdmissible_mk_iff (roots : List Representation)
    (references : List ReferenceEntry) :
    MultiDocument.FieldAdmissible (MultiDocument.mk roots references) ↔
      roots ≠ [] ∧
      (∀ root ∈ roots, Representation.FieldAdmissible root) ∧
      (∀ entry ∈ references,
        Representation.FieldAdmissible entry.representation) := Iff.rfl

/--
The `D6` embedding lands inside field admission, in both directions.

`MultiDocument.fieldAdmissible_two_roots` records that admission does not
account for non-surjectivity; this records the complementary half, that the
embedding does not change the judgment. A single-root image is never rejected
by the non-empty-roots clause, and no other clause distinguishes the shapes.
-/
theorem Document.fieldAdmissible_toMulti (document : Document) :
    MultiDocument.FieldAdmissible document.toMulti ↔
      Document.FieldAdmissible document := by
  cases document with
  | mk root references =>
      simp [Document.toMulti, MultiDocument.FieldAdmissible,
        Document.FieldAdmissible]

/-!
## Witnesses

Refusals and acceptances are separate obligations on purpose. The refusals
alone are satisfied by an admission that rejects everything; the acceptances
alone by one that accepts everything. The acceptances are where over-strict
admission — the failure mode that would silently make four reserved
counterexample rows unprovable — is caught.

None of these constructs a refusal or issue value, and none precommits a later
diagnostic vocabulary or scan order.
-/

section Witnesses

attribute [local simp]
  Annotations.FieldAdmissible Representation.FieldAdmissible
  Representation.FieldAdmissibleList Representation.FieldAdmissibleElements
  Representation.FieldAdmissibleProperties Representation.FieldAdmissibleIndexes
  Representation.FieldAdmissibleSchemas Check.FieldAdmissible
  Check.FieldAdmissibleList Check.AnnotationFieldAdmissible
  Document.FieldAdmissible MultiDocument.FieldAdmissible

/--
A retained annotation bag is decoded as JSON, so a non-finite payload is
refused here. Encode-side pruning drops the same entry silently instead; the
two directions are different judgments and only the decode direction is
asserted. `E4-SCHEMA-CE-011`.
-/
theorem Annotations.not_fieldAdmissible_nonFinite :
    ¬ Annotations.FieldAdmissible (some [⟨"bad", Json.number Float64.nan⟩]) := by
  simp [Json.not_numbersFinite_nan]

/-- The same clause reached through a representation's own annotation bag. -/
theorem Representation.not_fieldAdmissible_nonFiniteAnnotations :
    ¬ Representation.FieldAdmissible
      (Representation.never (some [⟨"bad", Json.number Float64.nan⟩]) []) := by
  simp [Json.not_numbersFinite_nan]

/-- Array elements carry annotation bags, and they are visited. -/
theorem Representation.not_fieldAdmissible_nonFiniteElementAnnotations :
    ¬ Representation.FieldAdmissible
      (Representation.arrays none []
        [⟨false, Representation.never none [],
          some [⟨"bad", Json.number Float64.nan⟩]⟩] []) := by
  simp [Json.not_numbersFinite_nan]

/-- Property signatures carry annotation bags, and they are visited. -/
theorem Representation.not_fieldAdmissible_nonFinitePropertyAnnotations :
    ¬ Representation.FieldAdmissible
      (Representation.objects none []
        [⟨PropertyKey.string "x", Representation.never none [], false, false,
          some [⟨"bad", Json.number Float64.nan⟩]⟩] []) := by
  simp [Json.not_numbersFinite_nan]

/-- Check nodes carry annotation bags too. -/
theorem Check.not_fieldAdmissible_nonFiniteAnnotations :
    ¬ Check.FieldAdmissible
      (Check.filter ⟨"effect/test", Json.null, none⟩
        (some [⟨"bad", Json.number Float64.nan⟩]) false) := by
  intro admissible
  have bag := ((Check.fieldAdmissible_filter_iff _ _ _).mp admissible).2.2.1
  exact Json.not_numbersFinite_nan (bag _ (List.mem_cons_self))

/-- `$ref: Schema.NonEmptyString` (`SchemaRepresentation.ts:1068`). -/
theorem Representation.not_fieldAdmissible_emptyReferenceKey :
    ¬ Representation.FieldAdmissible (Representation.reference ⟨""⟩) := by simp

/-- `id: Schema.NonEmptyString` on the declaration annotation (`:918`). -/
theorem Representation.not_fieldAdmissible_emptyAnnotationId :
    ¬ Representation.FieldAdmissible
      (Representation.declaration ⟨"", Json.null⟩ none [] []) := by simp

/--
`payload: Schema.Json` (`:919`) and `isJsonLeaf` requires `Number.isFinite`
(`SchemaAST.ts:4271-4274`).

This is the third numeric domain: a non-finite number is a legal enum value and
a legal property key, and is not a legal annotation payload
(`E4-SCHEMA-CE-028`).
-/
theorem Representation.not_fieldAdmissible_nonFiniteAnnotationPayload :
    ¬ Representation.FieldAdmissible
      (Representation.declaration ⟨"effect/test", Json.number Float64.nan⟩
        none [] []) := by
  intro admissible
  exact Json.not_numbersFinite_nan
    ((Representation.fieldAdmissible_declaration_iff _ _ _ _).mp admissible).2.1

/-- The `Literal` number leg is `Schema.Finite` (`:1005`). -/
theorem Representation.not_fieldAdmissible_nonFiniteLiteral :
    ¬ Representation.FieldAdmissible
      (Representation.literal none [] (LiteralValue.number Float64.nan)) := by
  simp [Float64.isFinite_nan]

/-- `Suspend.checks: Schema.Tuple([])` (`:987`). `E4-SCHEMA-CE-031`. -/
theorem Representation.not_fieldAdmissible_suspendChecks :
    ¬ Representation.FieldAdmissible
      (Representation.suspend none
        [Check.filter ⟨"effect/test", Json.null, none⟩ none false]
        (Representation.never none [])) := by simp

/-- `FilterGroup.checks: Schema.NonEmptyArray` (`:966`). -/
theorem Check.not_fieldAdmissible_emptyFilterGroup :
    ¬ Check.FieldAdmissible (Check.filterGroup none none []) := by simp

/-- `MultiDocument.representations: Schema.NonEmptyArray` (`:1107`). -/
theorem MultiDocument.not_fieldAdmissible_emptyRoots :
    ¬ MultiDocument.FieldAdmissible (MultiDocument.mk [] []) := by simp

/--
A defect buried under `Filter.representation.schemas` is found.

This is the row an admission that follows only `FilterGroup.checks` fails while
still passing every other row. `E4-SCHEMA-CE-033`.
-/
theorem Representation.not_fieldAdmissible_throughFilterSchemas :
    ¬ Representation.FieldAdmissible
      (Representation.objects none
        [Check.filter
          ⟨"effect/test", Json.null, some [Representation.reference ⟨""⟩]⟩
          none false]
        [] []) := by
  intro admissible
  have checks := ((Representation.fieldAdmissible_objects_iff _ _ _ _).mp admissible).2.1
  have filter := checks _ (List.mem_cons_self)
  have schemas := ((Check.fieldAdmissible_filter_iff _ _ _).mp filter).2.2.2
  have child := schemas _ rfl _ (List.mem_cons_self)
  exact (Representation.fieldAdmissible_reference_iff _).mp child rfl

/-- A non-empty `$ref` is admissible. -/
theorem Representation.fieldAdmissible_nonEmptyReferenceKey :
    Representation.FieldAdmissible (Representation.reference ⟨"Node"⟩) :=
  (Representation.fieldAdmissible_reference_iff _).mpr (by decide)

/-- A finite number literal is admissible. -/
theorem Representation.fieldAdmissible_finiteLiteral :
    Representation.FieldAdmissible
      (Representation.literal none [] (LiteralValue.number Float64.zero)) := by
  simp [Float64.isFinite_zero]

/-- A `Suspend` whose `checks` are empty is admissible. -/
theorem Representation.fieldAdmissible_suspendEmptyChecks :
    Representation.FieldAdmissible
      (Representation.suspend none [] (Representation.never none [])) := by simp

/-- Enum values are `Schema.Number`, not `Schema.Finite`. -/
theorem Representation.fieldAdmissible_nonFiniteEnumValue :
    Representation.FieldAdmissible
      (Representation.enum none [] [⟨"NotANumber", EnumValue.number Float64.nan⟩]) := by
  simp

/-- Property-name keys are `Schema.Number` too. -/
theorem Representation.fieldAdmissible_nonFinitePropertyKey :
    Representation.FieldAdmissible
      (Representation.objects none []
        [⟨PropertyKey.number Float64.nan, Representation.never none [], false, false,
          none⟩]
        []) := by simp

/--
Enum aliases are permitted.

A value-uniqueness clause here makes the reserved `E4-SCHEMA-CE-003` witness
unspellable. `E4-SCHEMA-CE-035`.
-/
theorem Representation.fieldAdmissible_aliasedEnum :
    Representation.FieldAdmissible
      (Representation.enum none []
        [⟨"A", EnumValue.string "x"⟩, ⟨"B", EnumValue.string "x"⟩]) := by simp

/--
An optional tuple element before a required one is field-admissible.

This is a field-shape result only. A later Schema denotation may reject the
sequence, so the two judgments do not contradict each other, and the reserved
`E4-SCHEMA-CE-004` needs the raw value to remain expressible.
-/
theorem Representation.fieldAdmissible_optionalBeforeRequiredElement :
    Representation.FieldAdmissible
      (Representation.arrays none []
        [⟨true, Representation.string none [], none⟩,
         ⟨false, Representation.string none [], none⟩] []) := by simp

/--
Duplicate property keys are field-admissible.

rc.112 persists `propertySignatures` as a plain array with no uniqueness check.
The Effect4 narrowing that would reject this is deferred until the key
equivalence relation is frozen; `E4-SCHEMA-CE-037` remains owed.
-/
theorem Representation.fieldAdmissible_duplicatePropertyKeys :
    Representation.FieldAdmissible
      (Representation.objects none []
        [⟨PropertyKey.string "a", Representation.string none [], false, false, none⟩,
         ⟨PropertyKey.string "a", Representation.number none [], false, false, none⟩]
        []) := by simp

/-- Field admission resolves no reference. `E4-SCHEMA-CE-040`. -/
theorem Document.fieldAdmissible_danglingReference :
    Document.FieldAdmissible
      (Document.mk (Representation.reference ⟨"Missing"⟩) []) := by
  refine (Document.fieldAdmissible_mk_iff _ _).mpr ⟨?_, ?_⟩
  · exact (Representation.fieldAdmissible_reference_iff _).mpr (by decide)
  · simp

/-- A table entry nothing points at is field-admissible. -/
theorem Document.fieldAdmissible_deadReferenceEntry :
    Document.FieldAdmissible
      (Document.mk (Representation.never none [])
        [⟨"Dead", Representation.never none []⟩]) := by simp

/--
An entry under the empty table key is admissible and unreachable by
construction: a table key is plain `Schema.String` while `$ref` is
`Schema.NonEmptyString`. `E4-SCHEMA-CE-030`.
-/
theorem Document.fieldAdmissible_emptyTableKey :
    Document.FieldAdmissible
      (Document.mk (Representation.never none [])
        [⟨"", Representation.never none []⟩]) := by simp

/-- The same table-key rule holds for a multi-root document. -/
theorem MultiDocument.fieldAdmissible_emptyTableKey :
    MultiDocument.FieldAdmissible
      (MultiDocument.mk
        [Representation.never none [], Representation.string none []]
        [⟨"", Representation.never none []⟩]) := by simp

/--
The two-root value used by the D6 non-image theorem is itself admissible.

Non-surjectivity of `Document.toMulti` is therefore not an artifact of an
empty, admission-rejected root list.
-/
theorem MultiDocument.fieldAdmissible_two_roots :
    MultiDocument.FieldAdmissible
      (MultiDocument.mk
        [Representation.never none [], Representation.string none []] []) := by simp

end Witnesses

end Effect4
