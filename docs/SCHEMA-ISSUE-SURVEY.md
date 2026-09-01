# rc.112 schema issue survey

Status: research input for the open `SC-ISSUE-01` ownership question,
2026-08-31. This file is a **survey of pinned third-party source**, not a
ruling and not a contract packet. It closes no obligation, allocates no
declaration, and assigns no cutover status. `docs/SCHEMA-CUTOVER.md` remains
the Schema ruling; `PORT-MANIFEST.md` remains the declaration record.

Every source claim below cites a line in the pinned bytes. The runtime
observations in §6 are explicitly finite and unretained; anything neither
citable nor observed there is marked **not established at the pin**.

## What is pinned, and what is only observed

The evidence is the Effect `4.0.0-rc.112` sources already named by
`docs/SCHEMA-CUTOVER.md`. They live on the build host under a Foldlab checkout
at `library/effects/node_modules/effect/src/`. That is a third-party npm
package identified by digest that happens to sit under a Foldlab checkout; it
is not a Foldlab dependency, and this repository still does not depend on
Foldlab. As with `SC-REP-CENSUS-PIN`, the evidence is **host-local**: it is not
vendored here, `lake build` does not reach it, and re-deriving it needs a local
`effect@4.0.0-rc.112` install.

| File | SHA-256 observed now | Pin status |
| --- | --- | --- |
| `SchemaIssue.ts` | `b4cb0ada18aef01083f9179dd827fb46aea4c625c2c63308d43cae5d3a86328e` | matches the `SchemaIssue.ts` row of `docs/SCHEMA-CUTOVER.md` §Exact authority state |
| `SchemaParser.ts` | `492dfbb294e24b2f3ebd949abbb9ba73cc19a71b4c35f290fd0137d52f8aaaaa` | matches the `SchemaParser.ts` row of `docs/SCHEMA-CUTOVER.md` §Exact authority state |
| `SchemaAST.ts` | `7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8` | matches the `SchemaAST.ts` row of `docs/SCHEMA-CUTOVER.md` §Exact authority state |
| `Formatter.ts` | `a772a439461546421ac6eb13380cacc120e66781474b3a53bcba180dd07b4bcf` | **not previously pinned**; recorded here as a new observation |
| `Schema.ts` | not re-hashed for this survey | the cutover ruling already records upstream/installed divergence in its own `Schema.ts` row |

Citations are written `SchemaIssue.ts:NNN` and refer to these bytes. Where a
claim rests on `Schema.ts`, the ruling's own caveat applies: installed
`Schema.ts` differs from the upstream revision (`docs/SCHEMA-CUTOVER.md`
§Exact authority state, `Schema.ts` row), so `Schema.ts` line numbers here are
**installed-bytes** citations only.

Line citations are used only for targets that cannot move under this
repository's edits: the pinned host sources above, the read-only evidence under
`vendor/foldlab/`, and `.lean` sources. This repository's own authored rulings
are edited continuously, so every citation into one names a section heading, an
obligation ID, a proof-graph node, or a quoted phrase instead of a line.
`./scripts/check-internal-citations.sh` enforces that. A passing run means no
`<doc>:NNN` citation into `docs/SCHEMA-CUTOVER.md`, `PLAN.md`, `AGENTS.md`,
`docs/ARCHITECTURE.md`, or `PORT-MANIFEST.md` remains under the scanned trees.
It does not mean the named anchors exist, that they still say what the citing
sentence claims, or anything at all about the host-source line citations, which
it deliberately ignores.

## 1. The issue census

**Count: 11.**

The count is a membership census over the pinned bytes, taken by two
independent lexical routes that agree with each other — the same two-route
discipline `./scripts/check-schema-census.sh` uses for the representation
alphabet:

1. **The closed source unions.** `Leaf` lists six members
   (`SchemaIssue.ts:107-113`) and `Issue` is `Leaf` plus five composite
   members (`:142-149`). Six plus five is eleven.
2. **The class declarations.** Eleven `export class X extends Base` blocks
   carry a `readonly _tag` initialiser, at `:205/:206`, `:260/:261`,
   `:316/:317`, `:360/:361`, `:400/:401`, `:445/:446`, `:511/:512`,
   `:572/:573`, `:646/:647`, `:698/:699`, `:757/:758`. `Base` itself
   (`:151`) is unexported and carries no `_tag`.

The assumption neither extraction can verify about itself is that these two
surfaces are the whole persisted-or-otherwise alphabet. That assumption is
recorded, not proved. Nothing here rules out a variant constructed by other
packages. An unretained lexical search over the surveyed installed rc.112
source tree found only `Schema.ts:1250`/`:1254` (a doc example) and
`unstable/ai/AiError.ts:533` (an unrelated `Schema.Literals` alphabet whose
`"MissingKey"` is an AI key-error kind, not a schema issue). That bounded
search is not evidence about unsurveyed packages or future producers.

Every variant additionally carries the brand `[TypeId] = TypeId` where
`TypeId = "~effect/SchemaIssue/Issue"` (`SchemaIssue.ts:21`, `:152`), and the
optional `input` field declared on `Base` (`:157`). `isIssue` narrows on that
brand alone (`:51-53`).

`Base`'s constructor is the gate on `input`:

```ts
constructor(input?: unknown, options?: SchemaAST.ParseOptions) {
  if (options?.reportInput === true && input !== InternalParser.missing) {
    this.input = input
  }
}
```

(`SchemaIssue.ts:158-162`.) `InternalParser.missing` is a module-private
`Symbol()` (`internal/schema/parser.ts:5`).

### 1.1 Field census

`_tag` is the exact class-declaration string in every row. `input?: unknown`
is inherited from `Base` and is present only where the constructor forwards it
to `super`; the `super(...)` call sites are `:235`, `:290`, `:337`, `:373`,
`:421`, `:475`, `:532`, `:594`, `:668`, `:728`, `:787`.

| # | `_tag` | Class | Fields beyond `_tag` and the brand | Carries `input`? |
| ---: | --- | --- | --- | --- |
| 1 | `"Filter"` | `Filter` (`:205`) | `filter : SchemaAST.Filter<unknown>` (`:210`); `issue : Issue` (`:214`) | yes — `super(input, options)` (`:235`) |
| 2 | `"Encoding"` | `Encoding` (`:260`) | `ast : SchemaAST.AST` (`:265`); `issue : Issue` (`:269`) | yes (`:290`) |
| 3 | `"Pointer"` | `Pointer` (`:316`) | `path : ReadonlyArray<PropertyKey>` (`:321`); `issue : Issue` (`:325`) | **no** — `super()` (`:337`) |
| 4 | `"MissingKey"` | `MissingKey` (`:360`) | `annotations : Schema.Annotations.Key<unknown> \| undefined` (`:365`) | **no** — `super()` (`:373`) |
| 5 | `"UnexpectedKey"` | `UnexpectedKey` (`:400`) | `ast : SchemaAST.AST` (`:405`) | yes (`:421`) |
| 6 | `"Composite"` | `Composite` (`:445`) | `ast : SchemaAST.AST` (`:450`); `issues : readonly [Issue, ...Array<Issue>]` (`:454`) | yes (`:475`) |
| 7 | `"InvalidType"` | `InvalidType` (`:511`) | `ast : SchemaAST.AST` (`:516`) | yes (`:532`) |
| 8 | `"InvalidValue"` | `InvalidValue` (`:572`) | `annotations : Schema.Annotations.Issue \| undefined` (`:577`) | yes (`:594`) |
| 9 | `"Forbidden"` | `Forbidden` (`:646`) | `annotations : Schema.Annotations.Issue \| undefined` (`:651`) | yes (`:668`) |
| 10 | `"AnyOf"` | `AnyOf` (`:698`) | `ast : SchemaAST.Union` (`:703`); `issues : ReadonlyArray<Issue>` (`:707`) | yes (`:728`) |
| 11 | `"OneOf"` | `OneOf` (`:757`) | `ast : SchemaAST.Union` (`:762`); `successes : ReadonlyArray<SchemaAST.AST>` (`:766`) | yes (`:787`) |

Six facts a paraphrase of this table would lose, all pinned:

1. **`Pointer` and `MissingKey` can never carry `input`.** Their constructors
   call `super()` with no arguments (`:337`, `:373`), so `hasInput` (`:84-86`)
   is structurally false for them regardless of `reportInput`. The other nine
   forward `(input, options)`.
2. **`Composite.issues` and `AnyOf.issues` have different arities.**
   `Composite.issues` is `readonly [Issue, ...Array<Issue>]` — non-empty by
   type (`:454`). `AnyOf.issues` is a plain `ReadonlyArray<Issue>` (`:707`) and
   the documentation states it is empty when no union member was applicable
   (`:688`). A model that gives both the same list type admits an rc.112 shape
   in one direction and refuses one in the other.
3. **`OneOf` is a leaf that carries no inner issue.** It is a member of `Leaf`
   (`:113`), and its second field is `successes : ReadonlyArray<SchemaAST.AST>`
   (`:766`) — the members that *succeeded*. It is the only variant whose
   payload is evidence of success.
4. **`AnyOf` and `OneOf` narrow `ast` to `SchemaAST.Union`** (`:703`, `:762`),
   while `Encoding`, `UnexpectedKey`, `Composite`, and `InvalidType` take the
   full `SchemaAST.AST` (`:265`, `:405`, `:450`, `:516`).
5. **`MissingKey` and `InvalidValue`/`Forbidden` take different annotation
   types.** `Schema.Annotations.Key<unknown>` (`:365`) versus
   `Schema.Annotations.Issue` (`:577`, `:651`). Both ultimately extend the open
   `Annotations` index signature — see §4.
6. **`Filter.filter` is typed `SchemaAST.Filter<unknown>`, not
   `SchemaAST.Check<unknown>`** (`:210`). The only construction site observed
   passes `check` from the non-`FilterGroup` branch of `collectIssues`
   (`SchemaAST.ts:4142-4145`). That is a call-site observation over the pinned
   bytes, not a totality claim about every producer.

### 1.2 Non-class exports of the module

This section lists the *module surface*, not the alphabet. Besides the eleven
classes, the module exports the guards `isIssue` (`:51`) and `hasInput`
(`:84`), the type aliases `Leaf` (`:107`), `Issue` (`:142`), `Formatter` (`:854`), `LeafHook`
(`:870`), `CheckHook` (`:959`), the hooks `defaultLeafHook` (`:912`) and
`defaultCheckHook` (`:982`), the formatter factories
`makeFormatterStandardSchemaV1` (`:1026`) and `makeFormatterDefault` (`:1149`),
the shared `defaultFormatter` (`:1154`), and three `@internal` constructors:
`makeCompositeAtKey` (`:600`), `makeSingle` (`:811`), and
`normalizeFilterOutput` (`:826`). There is no codec, decoder, schema, or
`toJSON` in the module — see §3.

## 2. Recursion

The issue tree is recursive, on exactly five fields, in two shapes.

**Single-child wrappers (3):**

| Variant | Field | Type |
| --- | --- | --- |
| `Filter` | `issue` | `Issue` (`SchemaIssue.ts:214`) |
| `Encoding` | `issue` | `Issue` (`:269`) |
| `Pointer` | `issue` | `Issue` (`:325`) |

**List-valued children (2):**

| Variant | Field | Type | Empty allowed? |
| --- | --- | --- | --- |
| `Composite` | `issues` | `readonly [Issue, ...Array<Issue>]` (`:454`) | no, by type |
| `AnyOf` | `issues` | `ReadonlyArray<Issue>` (`:707`) | yes (`:688`) |

The remaining six — `InvalidType`, `InvalidValue`, `MissingKey`,
`UnexpectedKey`, `Forbidden`, `OneOf` — hold no `Issue` and are exactly the
declared `Leaf` union (`:107-113`). The two recursive walkers in the module
agree with that partition: `toDefaultIssues` recurses at `:1068` (`Filter`),
`:1079` (`Encoding`), `:1081` (`Pointer`), `:1083` (`Composite`), and `:1091`
(`AnyOf`), and falls through to the leaf hook at `:1094`; `formatIssue`
recurses at `:1165`, `:1175`, `:1177`, and `:1181` with the same fall-through
at `:1187`.

There is a **second, distinct recursion axis** that is not through `Issue`:
`Filter.filter` (`:210`) is a `SchemaAST.Filter`, and `SchemaAST.Check` is
`Filter | FilterGroup` (`SchemaAST.ts:3290`) where `FilterGroup.checks` is a
non-empty array of `Check` (`SchemaAST.ts:3257`). `formatCheck` walks that
second tree (`SchemaIssue.ts:1106`). Effect4 can still use one recursive issue
carrier: its `Filter` constructor may carry a separate first-order check
descriptor. No second issue carrier is needed. What would lose information is
flattening the check descriptor into the issue recursion or duplicating the
issue constructors inside a check type.

A `FilterGroup` combines check results conjunctively only along a
**normal-return** execution. `Filter.run` is executable (`SchemaAST.ts:3209`)
and can throw; the finite observation `Q2` saw such a throw propagate rather
than become an issue. A future check denotation therefore needs a separate
defect/control outcome and must not state unconditional conjunction over all
host executions.

`Pointer.path` is `ReadonlyArray<PropertyKey>` (`:321`), so nesting a path is
also expressible by nesting `Pointer` nodes; the formatter concatenates them
(`:1081`, `:1177`).

## 3. Are issues persisted? — no codec found in the surveyed pin

This is the load-bearing question. In the surveyed pinned surfaces, the
rc.112 issue alphabet is a **runtime-only diagnostic carrier**: no issue
codec, decoder, or round trip was found. Every examined wire boundary converts
an issue to a **string** or to a flattened `{message, path}` record before it
leaves the process, and no inverse was found in those same surfaces. These are
bounded source-search results, not an impossibility theorem about the package
or its consumers.

The runtime-code evidence, in order of weight:

1. **The surveyed module declares no codec and has no runtime `Schema`
   binding.** `SchemaIssue.ts` imports both
   `Schema` and `SchemaAST` as **types only** — `import type * as Schema`
   (`:17`) and `import type * as SchemaAST` (`:18`). A type-only import
   contributes no runtime binding, and the inspected module contains no
   `Schema.*` codec construction. Contrast `SchemaRepresentation.ts`, which
   imports `Schema` as a value and builds `DocumentFromJson` and `MultiDocumentFromJson`
   (`SchemaRepresentation.ts:1098-1110`) plus their `encodeSync`/`decodeSync`
   adapters (`:1112-1115`).
2. **The persisted representation alphabet does not mention issues.** An
   unretained lexical search for `Issue` in the surveyed
   `SchemaRepresentation.ts` bytes returned nothing. The persisted
   families are `Representation` (`:406`), `Check` (`:436`), `Document`
   (`:480`), and `MultiDocument` (`:491`). No issue node exists in the
   persisted grammar.
3. **The RPC server stringifies before sending.** On a schema failure the
   server maps the cause through `SchemaIssue.defaultFormatter` and sends the
   resulting **string** as a defect: `unstable/rpc/RpcServer.ts:642` and
   `:716`. The issue value itself never enters the transport.
4. **`SchemaError` renders rather than carries.** `SchemaError` holds the issue
   as a live field (`Schema.ts:1180-1182`) but its `message` getter is
   `SchemaIssue.defaultFormatter(this.issue)` (`Schema.ts:1193-1195`) and its
   `toString` wraps that (`:1196-1198`).
5. **The Standard Schema boundary flattens.**
   `makeFormatterStandardSchemaV1` returns `{ issues: DefaultIssue[] }`
   (`SchemaIssue.ts:1030-1032`) where `DefaultIssue` is exactly
   `{ message: string; path: ReadonlyArray<PropertyKey> }` (`:1036-1039`).
   `Schema.standardSchemaV1` installs it as the failure projection
   (`Schema.ts:1312`, used at `:1317`). The module doc states the returned
   Standard Schema issues do **not** receive an `input` field
   (`SchemaIssue.ts:1001-1002`).
6. **The formatter type is one-way.** `Formatter<in Value, out Format>` is
   `(value: Value) => Format` (`Formatter.ts:41-43`). There is no inverse
   direction in the interface, and no inverse was found among the surveyed
   `Formatter` and `SchemaIssue` exports.

Consequence for the repo's layering: rc.112 issues sit on the **wrong side of
the `docs/SCHEMA-CUTOVER.md` §1 Structural representation rule that "the
carrier contains no `Lean.Expr`, Lean continuation, JavaScript function,
promise, runtime object, or reviver closure"**. They are not persisted Schema
content for the same reason `SchemaAST.AST` is not (`docs/SCHEMA-CUTOVER.md`
§Decision: it "is not persisted Schema content because its declarations and
checks contain executable functions") — they contain executable functions,
transitively. See §4.

### 3.1 A finding that cuts across the ruling's refusal table

rc.112 reports **wire-level** refusal of a persisted representation document
through the **same** `Issue` alphabet as ordinary value decoding, because
`fromJson` is itself a schema decode: `fromJson` calls `decodeDocument`
(`SchemaRepresentation.ts:1177-1179`), which is
`Schema.decodeSync(DocumentFromJson)` (`:1114`).

`docs/SCHEMA-CUTOVER.md` §Refusal and failure ownership splits *Schema issue*,
*wire issue*, and *profile issue* into three rows with three owners. rc.112
uses one `Issue` carrier. This is the issue-layer analogue of the
already-recorded
`E4-SCHEMA-CE-025` claim-scope rule: **no Effect4 issue-kind distinction may
be described as an rc.112 distinction.** There is not yet an implication in
either direction. In particular, an Effect4 profile may refuse a document
that rc.112 accepts, while an rc.112 `Issue` value does not by itself reveal
whether Effect4 would classify its origin as a schema, wire, profile, or
domain refusal. Any relationship must be a future bridge judgment over the
operation and its context, not an implication between carrier memberships.

## 4. Host values inside an issue

An rc.112 issue can carry host values that are not first-order data. This is a
hard boundary for this repository (`AGENTS.md`, representation rules: canonical
program content is first-order data; host closures and runtime objects are not
stored program syntax).

The field families observed below can hold host values. This is deliberately
not called a nine-field census: inherited `input` is reachable on nine
variants, while the table also contains variant-specific fields and one row
that groups two separate annotation fields.

| Field | Where | Host content it can hold |
| --- | --- | --- |
| `input?: unknown` | `Base` (`SchemaIssue.ts:157`), reachable on nine of eleven variants (§1.1) | the actual rejected runtime value, **retained by reference, not copied** (`SchemaAST.ts:529`). Any JavaScript value: a function, a class instance, a promise, a live object graph. |
| `Filter.filter` | `:210` | a `SchemaAST.Filter`, whose `run` is an executable closure (`SchemaAST.ts:3209`) and whose `annotations` may hold `toJsonSchema` and `toCode` function annotations (`Schema.ts:17231-17232`, function types at `SchemaRepresentation.ts:69`) |
| `Encoding.ast` | `:265` | a live `SchemaAST.AST`; `Declaration.run` is a parser factory (`SchemaAST.ts:692`, type at `:666-668`) and `Suspend.thunk` is `() => AST` (`SchemaAST.ts:3146`) |
| `UnexpectedKey.ast` | `:405` | same |
| `Composite.ast` | `:450` | same |
| `InvalidType.ast` | `:516` | same |
| `AnyOf.ast` | `:703` | a live `SchemaAST.Union` |
| `OneOf.ast` | `:762` | a live `SchemaAST.Union` |
| `OneOf.successes` | `:766` | an array of live `SchemaAST.AST` nodes |
| `MissingKey.annotations` | `:365` | `Schema.Annotations.Key<unknown>`, which reaches the open index signature `readonly [x: string]: unknown` (`Schema.ts:17004-17006`) |
| `InvalidValue.annotations`, `Forbidden.annotations` | `:577`, `:651` | `Schema.Annotations.Issue extends Annotations` (`Schema.ts:17547`), same open index signature |

Two further boundary facts:

- **`Pointer.path` is not portable either.** It is `ReadonlyArray<PropertyKey>`
  (`:321`), and `PropertyKey` includes `symbol`. A *local* symbol key is
  exactly the case `Effect4.PropertyKeyKind` deliberately gives no constructor
  (`Effect4/Schema/Representation.lean:450-473`). But this is not another
  instance of persisted-representation counterexample `E4-SCHEMA-CE-010`:
  `Pointer.path` belongs to the runtime issue carrier. It needs the dedicated
  issue-portability counterexample proposed as `E4-SCHEMA-CE-027` in §7.5.
- **A live host `symbol` is written into `input` by rc.112 itself.** The
  unregistered-symbol encode failure constructs
  `new SchemaIssue.Forbidden({ message: ... }, sym, options)` where `sym` is
  the actual symbol (`SchemaAST.ts:4098-4102`).

The two variants that cannot carry a rejected input — `Pointer` (`:337`) and
`MissingKey` (`:373`) — still reach host content: `Pointer` through its `path`
symbols, `MissingKey` through its open annotations record.

**No rc.112 issue field observed holds a thrown object.** Thrown values did
not become issues at the surveyed call sites; they propagated as throws (see
§5 and the finite probe `Q2`). That is a bounded negative result, not a claim
about unsurveyed producers.

## 5. Classification against Effect4's distinctions

`PLAN.md` requires that live frontiers stay distinct from typed failure,
defects, interruption, and domain-specific refusal.
`docs/SCHEMA-CUTOVER.md` §Refusal and failure ownership gives the seven-row
ownership table.

**All eleven constructors inhabit one rc.112 `Issue` error carrier.** Every
parser entry point types the error channel as `SchemaIssue.Issue`
(`SchemaParser.ts:242`, `:459`, `:593`). rc.112 keeps the separation itself:
`getSchemaIssue` returns `undefined` unless *every* cause reason is a
`FailReason` carrying an issue (`internal/schema/cause.ts:5-13`), and the
synchronous adapters state that causes containing defects, interruptions, or
asynchronous work **throw** instead of becoming issues
(`SchemaParser.ts:67-68`, `:446-448`), which
`getSchemaIssueOrThrow` implements (`internal/schema/cause.ts:17-25`). This is
a statement about host carrier placement, not a static semantic classification
of each constructor.

Effect4 should keep one issue carrier and classify an issue's **origin in
context**: operation, parse options, union mode, and surrounding issue tree
are inputs to the classification judgment. `Pointer`, `UnexpectedKey`, and
`OneOf` remain constructors of that carrier; the words "location", "profile
refusal", and "domain refusal" below are possible outputs of the contextual
judgment, not invitations to mint parallel refusal types.

Provisional contextual readings against the ruling's rows:

| `_tag` | Contextual Effect4 reading | Note |
| --- | --- | --- |
| `InvalidType` | Schema issue — typed decode/encode failure | the base case |
| `InvalidValue` | Schema issue | check/refinement failure and the carrier for user-supplied messages |
| `MissingKey` | Schema issue | structural absence |
| `Composite` | Schema issue (aggregation) | carries no failure of its own; groups children |
| `Filter` | Schema issue (wrapper) | attributes a child failure to a named check |
| `Encoding` | Schema issue (wrapper) | direction marker only — `findMessage` delegates through it (`:1195`) and both formatters skip it (`:1079`, `:1175`) |
| `Pointer` | location wrapper in the same issue carrier | pure location context; `findMessage` returns `undefined` for it unconditionally (`:1194`) and it never carries an input (`:337`). Its classification follows its child and operation context. |
| `AnyOf` | Schema issue (aggregation) | but see below |
| `UnexpectedKey` | profile-conditioned refusal origin, still an `Issue` constructor | it exists only because `onExcessProperty: "error"` was selected (`SchemaAST.ts:484`). The value may be structurally valid under another profile. |
| `OneOf` | union-mode refusal origin, still an `Issue` constructor | its payload is the list of members that *succeeded* (`:766`). The union's `oneOf` mode refuses ambiguity. |
| `Forbidden` | **does not fit cleanly** — see below | |

Three cases do not fit cleanly, and each is a design hazard for Effect4:

1. **`Forbidden`.** Its own documentation says it is produced "when a forbidden
   operation is encountered during parsing, such as an asynchronous Effect
   running inside `Schema.decodeUnknownSync`" (`SchemaIssue.ts:616-617`). Read
   literally, that is a **live frontier** in this repository's vocabulary —
   execution needs more steps than the boundary allows — and `PLAN.md` forbids
   modelling a frontier as a typed error. But at the pin, no parser call site
   produces it that way: the async-at-sync-boundary case throws
   (`SchemaParser.ts:446-448`, and finite probe `Q1`). The `Forbidden`
   constructions found at the surveyed call sites are the unregistered-symbol
   encode (`SchemaAST.ts:4098-4102`), `SchemaGetter.forbidden`
   (`SchemaGetter.ts:194-200`),
   and encode-only HTTP API schemas (`unstable/httpapi/HttpApiBuilder.ts:1181`,
   `:1200`; `unstable/httpapi/HttpApiClient.ts:1070`, `:1077`) — all of which
   are refusals, not frontiers. **The documented meaning and the observed
   production disagree at the pin.** Effect4 must not import the documented
   meaning; if it models `Forbidden` at all, it must say which of the two it
   means.
2. **`Pointer`.** It has no standalone row because it is a path segment
   attached to a child, but it must remain a constructor of the same recursive
   carrier to reproduce the rc.112 tree. The contextual classifier can recurse
   through it, accumulating a checked portable path (and refusing a local
   symbol at the bridge), without creating a separate `LocatedIssue` or
   duplicating the eleven tags. Shape theorems must account
   for arbitrary wrapper depth; that is a property to prove, not a reason to
   split the carrier.
3. **`UnexpectedKey` and `OneOf` are parse-option- and mode-relative.**
   Whether they can occur at all depends on `onExcessProperty`
   (`SchemaAST.ts:484`) and on the union's `oneOf` mode. Under the ruling those
   are profile and denotation facts respectively (`docs/SCHEMA-CUTOVER.md`
   §Operational semantic rulings: the "`ParseOptions` are first-order inputs"
   bullet, whose observables include excess-property policy, and the "`oneOf`
   succeeds exactly when one member succeeds" bullet), so they are not
   properties of the issue alphabet alone.

Finally, **`disableChecks`** (`SchemaAST.ts:513`) removes `Filter` issues from
the reachable set entirely, and **`errors: "first" | "all"`**
(`SchemaAST.ts:471`) decides whether `Composite` can hold more than one child
(`SchemaAST.ts:4148`). The reachable issue *shape* is a function of
`ParseOptions`, which the ruling already fixes as first-order observable input
(`docs/SCHEMA-CUTOVER.md` §Operational semantic rulings, "`ParseOptions` are
first-order inputs").

Accordingly, a tag-only function `IssueTag → IssueClass` would be too coarse.
The semantic obligation is a contextual relation over the existing issue
carrier; no per-class copy of `Pointer`, `UnexpectedKey`, or `OneOf` is
justified by this survey.

## 6. Finite probes

Three probe scripts were executed against the pinned package's built `dist`
on the build host, under Node v22.23.2. They are **finite probes**, not proofs: they
observe a handful of executions of one build, they are not in this repository,
`lake build` does not run them, and they establish nothing about inputs they
did not exercise. No retained script, expected output, or drift gate currently
backs them, so they cannot discharge a contract or closure row. They are
reported because §3 and §4 are runtime questions.

| Probe | Observation | What it supports |
| --- | --- | --- |
| `P1` | `Object.getOwnPropertyNames(new MissingKey(undefined))` = `["~effect/SchemaIssue/Issue", "_tag", "annotations"]` | the brand is an own property (`:152`) |
| `P2` | a decode failure without `reportInput` yields `InvalidType` with own names `[brand, "_tag", "ast"]`; `hasInput` false | the `Base` gate (`:158-162`) |
| `P3` | with `reportInput: true`, `issue.input === theOriginalObject` is `true`, and `typeof issue.input.fn === "function"` | §4: retention is by reference (`SchemaAST.ts:529`), and a function is reachable through an issue |
| `P4` | `issue.ast === Schema.String.ast` is `true` | the issue holds the identical live AST object, not a copy |
| `P5` | `JSON.stringify` of a `Composite/Pointer/MissingKey` tree emits the brand string as a data key and drops everything non-JSON | there is no round trip; the output is not a codec's output |
| `P6` | a `Filter` issue's `filter.run` is a `function`; `JSON.stringify` silently omits it | §4 and §3 |
| `P7` | `Object.keys(SchemaIssue)` = the 11 classes plus `defaultCheckHook, defaultFormatter, defaultLeafHook, hasInput, isIssue, makeCompositeAtKey, makeFormatterDefault, makeFormatterStandardSchemaV1, makeSingle, normalizeFilterOutput` | the observed build exported no decoder or schema |
| `P8` | a `Pointer` whose path is `[Symbol("k"), 0, "a"]` stringifies its symbol segment to `null` | §4: symbol path segments are silently lost |
| `P9` | a function-valued annotation is silently dropped by `JSON.stringify` | §4 |
| `Q1` | asynchronous work at `decodeUnknownResult` **throws** `Error("Result adapter can only return schema issues")`; no `Forbidden` issue is produced | §5 hazard 1 |
| `Q2` | a defect thrown inside a filter propagates as a throw, not as an issue | §4 and §5 |
| `Q3` | a union type mismatch yields `AnyOf` with `issues.length === 0` | §1.1 fact 2 |
| `Q4` | a `oneOf` ambiguity yields `OneOf` whose `successes` are live `Objects` AST nodes | §1.1 fact 3, §4 |
| `Q5` | a failing transformation yields `Encoding` with own names `[brand, "_tag", "ast", "issue"]` | §2 |
| `Q6` | the observed `SchemaIssue` export object exposes no `decode`, `parse`, `fromJson`, `schema`, or `Schema` member | §3 |
| `R1` | `SchemaRepresentation.fromJson` with `_tag: "NotATag"` throws a `SchemaError` whose `.issue` is a `Composite` | §3.1: wire refusal uses the issue alphabet |
| `R2` | an empty `$ref` is refused with `Expected a value with a length of at least 1 / at ["representation"]["$ref"]` | §3.1, and corroborates `docs/SCHEMA-CUTOVER.md` §Frozen rc.112 persisted census, "an empty `$ref` is refused by rc.112 itself" |
| `R3` | `toJson(toRepresentation(Schema.String.ast))` is `{"representation":{"_tag":"String","checks":[]},"references":{}}` | contrast: persisted content *does* have a codec |

## 7. Ownership proposal for `SC-ISSUE-01`

### 7.1 The obligation exists and has no module

`SC-ISSUE-01` is named as a gate in the Schema graph —
`P3-ALGEBRA-CLOSED + DATA-ROW-01/02/03 + SC-ISSUE-01 typed issue exit ->
SC-GET-P-01 ...` (`docs/SCHEMA-CUTOVER.md` §Proof graph) — and it is named as
open in three places: `PORT-MANIFEST.md` ("ownership of `SC-ISSUE-01` typed
issue exit remains open"), `Effect4/Schema/Getter.lean:52` and `:55`, and
`Effect4/Schema/Transformation.lean:43`. No module owns it.

### 7.2 Recommendation: create `Effect4/Schema/Issue.lean`; allocate its graph at the semantic threshold

**`Effect4/Schema/Issue.lean` should exist.** Its initial finite `IssueTag`
alphabet, spelling map, census, and leaf/composite partition may use a leaf
receipt. Those declarations are closed finite data and elementary case
theorems; they do not by themselves own a diagnostic judgment, refusal,
denotation, or bridge.

The standalone proof graph — proposed name `SCHEMA-PG-ISSUE` — becomes
mandatory **before the first public declaration** of any of these four things:

1. the recursive issue payload carrier;
2. the contextual diagnostic/classification judgment;
3. `SchemaIssueSig` or another effectful failure exit; or
4. an rc.112 host bridge, reification, or differential target.

That threshold follows the repo's allocation rules. The `leaf-receipt`
conditions in `docs/AGENT-ROUTING.md` allow that route only when the declaration "owns no admission, refusal,
diagnostic, judgment, denotation, interpreter, handler, reification,
refinement, generation, or semantic bridge". The full `SC-ISSUE-01`
obligation crosses the threshold because it is the *failure exit of a
denotation*: the Getter shape is
`Option E × ParseOptions → Program (SchemaIssueSig ⊕ₛ S) (Option T)` with
`SchemaIssueSig.Answer _ = Empty` (`docs/SCHEMA-CUTOVER.md` §3 Directional
transformations, the "Proof semantics" item; `Effect4/Schema/Getter.lean:19`).
The graph-trigger list in `docs/AGENT-ROUTING.md` makes "admits,
rejects, refuses, or classifies effectful programs or failures" a graph
trigger outright. It also has a host boundary (§4) and a target/differential
obligation (`SC-HOST-03`, `SC-HOST-04`), each of which `docs/SCHEMA-CUTOVER.md`
§When a standalone proof graph is required forbids a leaf from owning: "a leaf
may have no independent admission, denotation, bridge, target, compatibility,
or host meaning". None of those
facts retroactively turns the finite tag alphabet into a graph-bearing
semantic object.

**Why not `Effect4/Schema/Check.lean`.** `Check.lean` owns admission of
*representations* — `SC-REP-04` and `SC-PROFILE-01..03`, a document-level
classifier over the 22-tag alphabet. rc.112 issues are produced by *value*
decode and encode: `SchemaParser.ts:1205`, `SchemaAST.ts:1757`, `:1787-1788`,
`:1866`, `:2240`, `:2968`, `:3073`, `:4145`. Those are different judgments over
different objects. Merging them would make one module own both "is this
document admissible" and "why did this value fail", which is the ownership
collision `AGENTS.md` §Authority map requires repairing rather than creating.
`Check.lean` already records one naming hazard (`Check` the module versus
`CheckTag` the representation node); adding a third
`Issue`/`Check`/`CheckTag` overlap in the
same file compounds it.

**Why not `Effect4/Semantics/Cause.lean`.** `docs/SCHEMA-CUTOVER.md` §Refusal
and failure ownership gives "Schema issue" and "Cause/Exit" separate rows and
separate owners, and rc.112 keeps them separate at runtime too
(`internal/schema/cause.ts:5-13`; `SchemaParser.ts:67-68`, `:446-448`; probes
`Q1`, `Q2`). Housing the issue alphabet in `Cause.lean` would build exactly
the merge the ruling forbids.

**Why not `Effect4/Protocol/Admission.lean`.** That module owns generic profile
membership and refusal policy — the "profile issue" row, a third row again.

**Why not extend `SCHEMA-PG-REPRESENTATION-TAG`.** Its `semantics`, `laws`,
`bridges`, and `targets` edges are `not-applicable` with authored reasons
(`PORT-MANIFEST.md`, parent-graph edge table). `SC-ISSUE-01` is semantic and
host-bearing; attaching it would require changing four `not-applicable` rows
through a new breaker packet, which is more disruptive than a new graph.

### 7.3 What the obligation should say

Proposed wording for the `SC-ISSUE-01` row, to be ratified by a breaker packet
rather than adopted from this survey:

> **`SC-ISSUE-01` — typed schema issue exit.** `Effect4.Schema.Issue` owns one
> first-order schema-issue carrier and one `Signature` whose `Answer` is
> `Empty` at every operation, so that a Getter's failure exit is an operation
> of the existing effect algebra and never a Lean partial function, an
> exception, or a host object. The carrier reproduces the rc.112 eleven-member
> issue alphabet at the *tag* level. `Pointer`, `UnexpectedKey`, and `OneOf`
> remain constructors of this one carrier; contextual classification never
> clones them into separate refusal types. For every rc.112 field that is not
> first-order data — the field families listed in §4 — the carrier either
> replaces it
> with an explicitly checked first-order surrogate (a declaration identity, a
> representation reference, a portable property-key path) or omits it, and each
> omission is recorded as a named non-claim rather than left implicit. No
> issue value holds a `SchemaAST` node, a filter closure, a reported host
> `input`, or an open `unknown`-valued annotation record.

Two standing claim-scope rules should ship with it:

1. **No Effect4/rc.112 classification implication exists yet.** rc.112 reports
   representation-document wire refusal through the same carrier as value
   decode failure (§3.1). No Effect4 separation of Schema issue, wire issue,
   profile issue, or domain refusal may be attributed to rc.112, and no
   Effect4 refusal may be assumed to produce an rc.112 issue. A future bridge
   must relate an operation and its options to both results explicitly. This
   parallels `E4-SCHEMA-CE-025` and needs its own row.
2. **The issue alphabet is a diagnostics obligation, not a wire-format
   obligation.** Unlike `Effect4.Schema.Representation`, whose surveyed source
   has a codec and a JSON round trip (`SchemaRepresentation.ts:1098-1115`),
   the issue survey found neither for issues at the pin (§3). If Effect4 later
   gives issues a
   canonical encoding, that is an Effect4 invention with no rc.112
   counterpart, and it must be stated as such rather than as fidelity to the
   host.

### 7.4 Proposed exit gate

Split in two lanes, following the precedent that already worked for the
representation tags (`docs/SCHEMA-CUTOVER.md` §Entry gate for implementation,
the "Tag declarations" and payload lanes of the first implementation slice).

**Tag lane — openable now as a leaf receipt; mentions no payload, diagnostic
judgment, signature, host bridge, index, row, or requirement.**

- `SC-ISSUE-01a` exact eleven-constructor alphabet, with `census_length = 11`,
  `census_nodup`, and `mem_census` proved by case analysis — three separate
  theorems, for the reason `E4-SCHEMA-CE-019` already forced.
- `SC-ISSUE-01b` case-sensitive `_tag` spelling function, injectivity, and
  partial inverse, plus a lexical source gate over the pinned bytes that takes
  **two** independent extractions — the closed `Leaf`/`Issue` unions
  (`SchemaIssue.ts:107-113`, `:142-149`) and the
  `export class ... extends Base` / `readonly _tag =` sites — and refuses to
  report agreement unless they match. This is the same two-route design that
  survived the independent reviewer's 23rd-tag mutation on
  `./scripts/check-schema-census.sh`.
- `SC-ISSUE-01c` the leaf/composite partition as a *declared* total predicate
  with a theorem, matching the pinned `Leaf` union — not a comment.
- `SC-ISSUE-01d` its counterexample battery (§7.5).

**Payload and semantic lane — requires `SCHEMA-PG-ISSUE` before its first
declaration and stays open behind the payload carrier and
`DATA-ROW-01/02/03`.**

- `SC-ISSUE-01e` recursive payload carrier with the exact arities of §2: three
  single-child wrappers, one non-empty child list, one possibly-empty child
  list, with a theorem separating `Composite` from `AnyOf` on emptiness. Its
  `Filter` payload references a separate first-order check descriptor; it does
  not duplicate the issue carrier.
- `SC-ISSUE-01f` `SchemaIssueSig` with `Answer _ = Empty`, plus the theorem
  that no issue operation can be answered — that theorem is what makes it an
  exit rather than an ordinary operation.
- `SC-ISSUE-01g` a contextual classification relation over operation,
  `ParseOptions`, union mode, and the one recursive issue carrier. It must
  recurse through `Pointer` rather than recasting it, and it must not define
  issue class as a function of `_tag` alone.
- `SC-ISSUE-01h` the host-boundary register: one row per §4 field family, each
  either
  a checked first-order surrogate with its admission rule or a recorded
  non-claim. This row is the reason the module needs a graph rather than a
  receipt.
- `SC-ISSUE-01i` the explicit non-claims, at minimum: Effect4 issue values
  carry no rejected host input; Effect4 does not model rc.112's
  `reportInput` retention (`SchemaAST.ts:529`, `:549`) as payload, only
  `ParseOptions` as an observation; and Effect4 claims no relation between its
  issue values and rc.112 issue values beyond tag-level correspondence until
  `SC-HOST-04` supplies differential vectors.

No lane closes on an asserted status, and the tag lane closing does not close
`SC-ISSUE-01`; only the generated conjunction does, exactly as
`docs/SCHEMA-CUTOVER.md` §Proof graph requires of every `*-CLOSED` name: it is
"the generated conjunction of every required node in that family", not a
manually assignable status.

### 7.5 Counterexamples this survey says are needed

The highest allocated Schema row is `E4-SCHEMA-CE-025`, so these are proposed
for `026` onward. They are **proposals**; allocating them is the breaker's act,
and this file changes no register.

| Proposed ID | Attacked statement | Refutation available now |
| --- | --- | --- |
| `E4-SCHEMA-CE-026` | An issue may carry the rejected input, as ordinary data | `SchemaAST.ts:529` says retention is by reference; probe `P3` observes `input === host` and a reachable function |
| `E4-SCHEMA-CE-027` | An issue tree, including a `Pointer.path` with a local symbol, is portable because it JSON-stringifies | probes `P5`, `P6`, `P8`, `P9`: filter closures, annotation functions, and symbol path segments vanish silently, and the observed export object has no decoder (`P7`, `Q6`). This is the issue-portability row, distinct from persisted-representation `E4-SCHEMA-CE-010`. |
| `E4-SCHEMA-CE-028` | `Composite` and `AnyOf` share one list arity | `SchemaIssue.ts:454` versus `:707`; `AnyOf` observed empty in probe `Q3` |
| `E4-SCHEMA-CE-029` | Every issue describes an invalid value | `OneOf.successes` (`:766`) records members that succeeded; probe `Q4` |
| `E4-SCHEMA-CE-030` | Asynchronous work at a synchronous boundary is a `Forbidden` issue | `SchemaParser.ts:446-448`; probe `Q1` throws instead. The module doc at `SchemaIssue.ts:616-617` is the trap |
| `E4-SCHEMA-CE-031` | An rc.112 issue tag alone determines its Effect4 issue kind | §3.1 and §5: `fromJson` failures use the ordinary `Issue` carrier, while `UnexpectedKey` and `OneOf` depend on options and union mode; probes `R1` and `R2` are finite corroboration only |

## 8. The second ownership gap: who owns the versioned wire profile

**Recommendation: `Effect4/Protocol/Profile.lean`, not
`Effect4/Schema/Check.lean`.**

The reason is dependency direction, not preference. `docs/ARCHITECTURE.md`
orders the library `first-order data and rows -> algebra and checked flow ->
operational/relational semantics -> logic and classification -> portable
protocol and typed targets -> host conformance harnesses`, and `Effect4.lean`
realises that order: the four `Effect4.Protocol.*` imports come after all nine
`Effect4.Schema.*` imports. So **Protocol may depend on Schema, and Schema may
not depend on Protocol.** The decisive obligation is `SC-WIRE-01`
duplicate-preserving raw JSON (the `SCHEMA-PG-WIRE` edge in
`docs/SCHEMA-CUTOVER.md` §Proof graph, with the rule at §5 Canonical wire
profile: "raw JSON must preserve ordered duplicate keys until the profile
rejects them"): a duplicate key must be rejected *before* any representation
tag is read, so the module owning it needs a byte and parse-order layer and no
Schema vocabulary at all. A module under `Effect4/Schema/` cannot own that
without importing a byte layer that sits downstream of it, which inverts the
arrow. `Effect4/Protocol/Bytes.lean` is already declared owner of "canonical
portable protocol bytes".

This also agrees with what the repository has already ruled twice — at
`docs/SCHEMA-CUTOVER.md` §5 Canonical wire profile and in the
profile-ownership paragraph of `PORT-MANIFEST.md`, both echoed in
`Effect4/Schema/Check.lean`'s own docstring. Under `AGENTS.md` §Authority map
two files agreeing is not a defect; the remaining gap is narrower than "who
decides", and is this: **`SC-WIRE-01` through `SC-WIRE-05`
appear in no module's assigned-obligation list.** `Effect4/Schema/Value.lean`
mentions only the open `SC-WIRE-06`.

The three-way split that discharges the gap without minting a second profile
carrier:

| Module | Owns |
| --- | --- |
| `Effect4/Protocol/Profile.lean` | the `Effect4Rc112` versioned profile identity and its version relation — `SC-PROFILE` identity |
| `Effect4/Protocol/Bytes.lean` | `SC-WIRE-01` duplicate-preserving raw JSON, and the byte-face statements of `SC-WIRE-03`, `SC-WIRE-04`, `SC-WIRE-05` |
| `Effect4/Schema/Check.lean` | `SC-REP-04` and `SC-PROFILE-01..03` — the tag- and field-level classifier and its diagnostics — plus the Schema half of `SC-WIRE-02` decoder soundness, consuming the Protocol facilities and minting no second profile or admission carrier |

Two consequences worth recording before that split is ratified:

1. `docs/SCHEMA-CUTOVER.md` §Refusal and failure ownership assigns the "wire
   issue" row to "the versioned wire profile". If Protocol owns the profile,
   Protocol owns the wire
   diagnostic judgment while Schema owns the recursive schema-issue carrier.
   That ownership split does **not** authorize a second copy of the eleven-tag
   carrier: any bridge should reuse the one `IssueTag` vocabulary or relate
   distinct diagnostics explicitly. It makes the no-implication rule in §7.3
   mandatory rather than optional.
2. `SC-WIRE-06` `normalization_preserves_denotation` is not a well-formed
   theorem statement until `SC-DEN-01` freezes
   (`docs/SCHEMA-CUTOVER.md` §5 Canonical wire profile:
   "`normalization_preserves_denotation` remains an open obligation"). The
   split above must not be read as
   licensing a normalization/denotation claim from either side; it allocates
   the idempotence and injectivity results only.

## 9. What this survey does not establish

- It is an **extraction plus a finite probe**, not a proof about the rc.112
  runtime. The assumption an extraction cannot verify about itself is that the
  closed `Leaf`/`Issue` unions and the `_tag`-bearing exported classes are the
  whole alphabet.
- The lexical searches and probes are not retained by this repository. The
  probes exercised one build of one package on one host and observe the
  executions listed in §6 and nothing else. Until scripts, inputs, expected
  outputs, and drift checks are retained, none of those observations is a
  gate.
- Nothing here is a Lean declaration, theorem, admission rule, or gate. It
  discharges no row of the Schema graph and changes no register.
- The rc.112 field list in §1.1 is a source-reading of the class declarations.
  It is not a decoder result, and no claim of faithfulness is made for any
  future Lean carrier.
- The classification in §5 is a reading against this repository's ruling
  vocabulary. rc.112 does not make those distinctions and cannot be cited for
  them. It also establishes no bridge implication between Effect4 classes and
  rc.112 carrier membership.
