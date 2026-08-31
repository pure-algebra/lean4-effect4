# Effect Core v1 — pinned public-surface reification checklist

Status: staged, pre-grade design; checker implementation is deliberately absent

Subject pin: `effect@4.0.0-rc.112`

Upstream source revision: `2600f62f4532026928454dcea8d1c48557b3f942`

Highest current claim: G0 identity inputs named; no G1–G6 result is claimed here

Status convention: every checklist-defined term, schema, ruling, and command is
**PROPOSED**; every unchecked gate and theorem obligation is **PENDING**.
Qualified existing CAS/Effect names refer to local declarations/evidence and do
not acquire a new status here.

## 0. Ruling carried by this checklist

The operator's premises are accepted directly:

1. the Effect Core operation alphabet is closed;
2. every admitted primitive or registered foreign operation has a direct
   handler;
3. package-surface classification closure is established mechanically from
   the shipped package, not by a handwritten list; and
4. a closed classification is not the same thing as completed proofs.

“Package-surface closed” means finite and total at this exact pin. Every
importable public
module, every exported type/value/namespace, every public member, and every
call or construct overload receives one row. Every row receives exactly one
disposition. Nothing is silently dropped because it is pure, unstable,
type-only, host-facing, implemented by a closure, or outside the first proof
slice.

The **public surface universe** is not the **Core operation alphabet**. The
first contains every public source row, including pure, type-only, target-only,
and refused host shapes. The second contains only reified primitives and
registered foreign operations with first-order request/answer schemas. A
public construct which cannot retain its Effect qualities in project-owned
syntax receives a conservative row disposition and exhaustive admission
profiles. Only a profile naming a registered implementation ID and serializable
payload may become a foreign operation. An arbitrary closure, promise executor,
or custom evaluator is classified but refused or target-only; it never enters
the Core alphabet as a payload. Direct handlers are required for primitive and
registered foreign operations, not for every public surface row.

This document is a build contract for the future hoover, ledger, generated
Lean rows, and gates. It does not authorize their implementation until the
Effect Core v1 packet is frozen.

## 1. Local evidence and exact boundary

Only locally present, pin-addressed evidence was used for this checklist.

| Evidence | Local path | Fact used |
|---|---|---|
| Runtime source lock | `.reference/provenance/sources.lock.json`, row `effect-runtime` (lines 261–287) | commit `2600f62f4532026928454dcea8d1c48557b3f942`, tag and package `effect@4.0.0-rc.112`, root tree `648a01b9c249448716e1a9474f511b17898f9d93` |
| Estate dependency | `library/effects/package.json` (lines 55–75) | exact npm pin `effect@4.0.0-rc.112`, back-reference to the same commit and lock row; `typescript@7.0.2`; `@effect/tsgo@0.38.0` |
| Shipped package identity | `library/effects/node_modules/effect/package.json` | package version, `exports` map, blocked internal routes, shipped `src`, `dist`, and declarations |
| Stable root barrel | `library/effects/node_modules/effect/src/index.ts` | auto-generated namespace barrel; 137 namespace exports and six named pure function exports at this pin |
| Other barrels | `library/effects/node_modules/effect/src/testing/index.ts` and `src/unstable/*/index.ts` | testing and unstable namespace exposures |
| Public declarations | `library/effects/node_modules/effect/dist/**/*.d.ts` | the consumer-visible type surface, including type-only exports and overloads |
| Source declarations/bodies | `library/effects/node_modules/effect/src/**/*.ts` | declaration origins, re-exports, source spans, implementation call graph, and internal provenance |
| Existing runtime census | `experiments/lift-harness/src/genbank.ts` and `models/bank-r0.json` | useful independent runtime-value census; not sufficient as the public type universe |
| Existing typed extractor pattern | `experiments/entity-store-extract/src/{contract,extract,oxc-extract,oxc-check}.ts` | pin checks, deterministic canonical JSON, two-instrument comparisons, coverage checks, and byte gates |
| CAS raw-table counterexamples and bridge anchors | `library/cas/Cas/Lang/Defun.lean`, `library/cas/Cas/Core/Admission.lean`, `library/cas/Cas/Backend/Mcp.lean`, summarized in `.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` | **PENDING snapshot/provenance pin:** raw `PProg` includes empty and dangling-answer tables; existing CAS checking is fail-fast; existing `ofPProg`/inverse/run theorems supply a partial-bridge pattern but not a total `PProg -> CheckedProgram` function |
| Effect-aware compiler configuration | `library/effects/tsconfig.json`, `scripts/patch-toolchain.ts`, and installed `node_modules/@effect/tsgo` | exact TS7 path: `@effect/tsgo@0.38.0` patches the installed TypeScript and oxlint and runs the integrated Effect language service under plugin name `@effect/language-service` |
| Effect-aware native frontend | installed `typescript/package.json` and `@effect/tsgo-darwin-arm64/lib/upstream.json` | TypeScript `7.0.2`, git head `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`, matched by the exact `@effect/tsgo-darwin-arm64@0.38.0` component metadata on this host |
| Historical language-service research pin | `experiments/parser-census/corpus-manifest.json`, row `effect-ts-language-service` | repository `https://github.com/Effect-TS/language-service`, observed research pin `5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4`; historical corpus evidence only, not the TS7 harness tool |

The older source row named `effect` in `sources.lock.json` is the deliberately
decoupled Schema extraction pin at rc.111. It is not an input to this rc.112
Effect Core surface.

### 1.1 Scope sets and the one row universe

The extractor must emit these named sets rather than letting “surface” change
meaning between phases:

- `U_package`: all public import specifiers accepted by the rc.112 package
  `exports` resolver, including `effect/package.json` as metadata.
- `U_code`: `U_package` minus the JSON metadata subpath.
- `U_stable`: root `effect` plus stable direct module subpaths.
- `U_testing`: `effect/testing` and its public module subpaths.
- `U_unstable`: every public `effect/unstable/**` subpath. Instability is a
  field, never a reason to omit a row.
- `U_exposure`: every exported path visible from each public import specifier,
  including namespace members and re-export aliases. This is a relation to
  rows, not itself the classification carrier.
- `U_symbolSpace`: canonical declarations after aliases and duplicate
  exposures are collapsed, with one key for each type, value, or namespace
  declaration space.
- `U_member`: every public instance/static/namespace member, keyed by its
  owner row, member path, and declaration space.
- `U_call`, `U_construct`, and `U_index`: every call, construct, and index
  signature, keyed by its owning symbol/member, signature kind, and source
  ordinal.
- `U_row`: the disjoint union
  `U_symbolSpace ⊎ U_member ⊎ U_call ⊎ U_construct ⊎ U_index`.
- `U_dependency`: the transitive declaration/type dependencies needed to state
  every public signature and every selected semantic mapping. Dependency rows
  are not `SurfaceRowKey`s and cannot affect the `U_row` coverage denominator.
- `U_effect`: `{ k ∈ U_row | effectReachability(k) is nonempty }`.
- `U_non_effect`: `U_row \ U_effect`; this is now a well-typed complement and
  must be closed deliberately, not ignored.

The generated key carrier is closed and disjoint:

```text
SurfaceRowKey =
  | symbolSpace (canonicalSymbolId, space : type | value | namespace)
  | member (owner : SurfaceRowKey, memberPath, space)
  | callOverload (owner : SurfaceRowKey, sourceOrdinal)
  | constructOverload (owner : SurfaceRowKey, sourceOrdinal)
  | indexOverload (owner : SurfaceRowKey, sourceOrdinal)
```

`owner` is structurally smaller, so member/signature ownership is acyclic.
Every exposure resolves to one symbol-space or member key. Every overload has
one symbol/member owner. These five constructors are pairwise disjoint, and
their union—not a mixture of symbols and signatures—is the domain of
effect-reachability, disposition, admission-profile, and zero-counter checks.

The primary phrase “public base effectful API” means rows in `U_effect` whose
owning module lies in `U_stable`.
Package closure means all of `U_package`, including testing and unstable.
Proof slices may prioritize the stable base, but classification cannot.

### 1.2 Observed counts are witnesses, not constants

At the local pin there are 137 stable direct source modules, 361 non-internal
source modules, and 361 matching non-internal declaration modules. The
existing runtime bank records 359 modules, 6,051 runtime values, and zero
import failures. Those numbers must not be copied into the checker as expected
constants; the generated source snapshot owns its derived counts.

The difference already falsifies the old directory walk's exhaustiveness.
`genbank.ts` descends only one level below each unstable group. The package's
`./*` export pattern also exposes these deeper shipped modules:

- `effect/unstable/http/MultipartParser/HeadersParser`
- `effect/unstable/http/MultipartParser/Search`

Both import successfully from the installed rc.112 package and each exports
`make`; neither appears in `bank-r0.json`. The new module closure must find
them by exports-map resolution plus recursive target discovery. The existing
bank remains an independent runtime-value cross-check after that defect is
repaired; it never defines `U_package`, `U_symbolSpace`, or `U_row`.

## 2. Mechanical closure algorithm

Every item below is a gate condition, not an implementation suggestion.

### 2.1 Pin and package preflight

- [ ] Read `library/effects/package.json`, its frozen `bun.lock`, the installed
  `effect/package.json`, and the `effect-runtime` source-lock row.
- [ ] Require exact agreement on package name and version.
- [ ] Require the estate package's recorded commit to equal the source-lock
  commit.
- [ ] Record the npm integrity from `library/effects/bun.lock`, the upstream
  commit/tree, and SHA-256 for every package file actually read.
- [ ] Record the TypeScript frontend version and all compiler options used for
  module and type resolution.
- [ ] Refuse a missing install, symlink to an unrecorded tree, changed package
  bytes, unresolved conditional export, or compiler/config drift.
- [ ] Do not infer source identity from the version string alone.

### 2.2 Public module closure

- [ ] Parse `exports` as Node package-export data, preserving rule order,
  explicit mappings, wildcard mappings, conditions, and `null` masks.
- [ ] Derive the finite candidate target set recursively from shipped files;
  do not bound wildcard depth by a handwritten directory loop.
- [ ] For each candidate, run the package-exports resolver and retain it only
  when the resolver returns that shipped target.
- [ ] Pair each code entry with its `.js`, `.d.ts`, source `.ts`, and source-map
  evidence where present. Absence is a recorded field, not silent fallback.
- [ ] Include root and explicit group barrels under their public spelling.
- [ ] Exclude `effect/index`, `effect/*/index`, `effect/internal/*`, and the two
  masked unstable internal families because the package map resolves them to
  `null`, not because their path contains a magic string.
- [ ] Import every code entry in a fresh process and record success, runtime
  export names, and `typeof` as an independent check. Import success does not
  replace export-map resolution.
- [ ] Assert exact set equality between resolved public code entries and
  paired public declaration entries.

### 2.3 Export, member, and overload closure

- [ ] Build one pinned TypeScript `Program` over all public declaration
  entrypoints; use the `TypeChecker`, not text matching, for symbol identity.
- [ ] Enumerate exports in the type, value, and namespace spaces. A type-only
  export is a first-class row.
- [ ] Follow `export *`, named re-exports, namespace exports, aliases, merged
  declarations, and module augmentations to their declarations.
- [ ] Recurse through public namespace members, class/interface public
  members, static members, callable objects, constructors, properties whose
  values are callable, and nested declared namespaces.
- [ ] Preserve every call, construct, and index overload separately and in
  source order. Data-first and data-last forms are different overload rows
  which may share one semantic expansion.
- [ ] Preserve generic parameters, variance annotations, constraints,
  defaults, conditional types, `this` parameters, predicates, optionality,
  rest parameters, and inferred return types after checker resolution.
- [ ] Emit raw source slices and a checker-normalized signature. Neither
  pretty-printed prose nor runtime `typeof` is a type-surface substitute.
- [ ] Treat root barrel spelling as an exposure edge. For example,
  `effect::Effect.flatMap` and `effect/Effect::flatMap` must resolve to one
  canonical declaration while both remain visible spellings.

### 2.4 Canonical identity

TypeScript's process-local `Symbol.id` is forbidden as stored identity. Each
row carries three related identities:

1. `declarationId` — SHA-256 over the domain separator
   `foldlab:effect-declaration:v1`, upstream commit, package-relative source
   path, declaration syntax kind, source ordinal among same-named
   declarations, and exact source bytes. A merged symbol contains the sorted
   set of declaration IDs.
2. `canonicalSymbolId` —
   `effect@4.0.0-rc.112::<canonical-public-subpath>::<export/member-path>::<space>`.
   The canonical public subpath is selected among exposures resolving to the
   same declaration set by: direct defining module first, then shortest
   subpath, then lexical order. `space` is `type`, `value`, or `namespace`;
   merged spaces have one row per space linked by `mergedGroupId`.
3. `exposureId` — the same form using the actual import subpath and exported
   path seen by a consumer. Every exposure points to exactly one canonical
   symbol.

An overload ID appends `::call[n]`, `::construct[n]`, or `::index[n]` to the
canonical symbol ID. Its `signatureDigest` hashes a versioned canonical
signature record, not TypeScript's display string alone.

- [ ] Declaration IDs are unique within the pin.
- [ ] Canonical symbol IDs are unique within each declaration space.
- [ ] Every exposure resolves to one canonical symbol.
- [ ] Every canonical public symbol has at least one exposure.
- [ ] Alias cycles terminate and are reported rather than truncated.
- [ ] A line-number move changes provenance fields but is not itself used as
  semantic identity.

### 2.5 Dependency closure

Starting from every public signature, traverse the resolved type graph with a
cycle guard. Edges must distinguish:

- alias target;
- generic constraint/default/argument;
- parameter, callback parameter, callback return, and top-level return;
- union/intersection constituent;
- property/member/index/call/construct signature;
- conditional check/extends/true/false branch;
- mapped/indexed/keyof/template-literal component;
- base class/interface and mixin;
- namespace qualification and re-export; and
- implementation mapping dependency: IR node, expansion, direct handler,
  observation, codec, or law.

Each reached declaration is recorded with visibility
`public_export`, `public_reexport`, `private_signature_support`, or
`package_internal_implementation`. Private support declarations remain in
`U_dependency`; they cannot vanish merely because consumers cannot import
their names. Package internals used only to explain implementation receive
`excludedInternal`, but their hashes and source paths remain provenance.

The closure gate is graph closure: every edge target is another recorded row
or one explicit primitive boundary (`typescript-lib`, ECMAScript host,
Node/Bun host, external npm package, or project-owned foreign operation).
Every boundary records package/version/lib file and the reason it is closed
there.

### 2.6 Closed type representation and total elaboration

TypeScript checker objects, display strings, and process-local IDs never enter
generated Lean. The extractor first emits a closed recursive raw type graph.
Every reached checker type has exactly one `RawTsType` node, including forms
which the semantic elaborator later refuses:

```text
RawTsType =
  | primitive (any | unknown | never | void | undefined | null
               | boolean | string | number | bigint | symbol)
  | literal (boolean | string | number | bigint | uniqueSymbol)
  | typeParameter TypeParameterId
  | thisType DeclarationId
  | union (NonEmpty RawTsTypeId)
  | intersection (NonEmpty RawTsTypeId)
  | object RawObjectKind ObjectFlags properties[] signatures[] typeArguments[]
  | tuple elements[] elementFlags readonly
  | array element readonly
  | callable SignatureId | constructible SignatureId
  | conditional check extends whenTrue whenFalse inferBinders[]
  | indexedAccess object index
  | keyof operand
  | mapped binders[] constraint nameType? valueType modifiers
  | templateLiteral head spans[]
  | stringMapping operator operand
  | substitution base constraint
  | typeQuery DeclarationId
  | importType BoundaryId qualifier? typeArguments[]
  | alias DeclarationId typeArguments[]
  | recursiveRef RawTsTypeId
  | externalBoundary BoundaryId
  | unsupported UnsupportedTsType
```

`RawObjectKind`, signature parameter shapes, predicates, modifiers, and every
flag set are themselves closed enums/records generated from the selected
TypeScript frontend. `UnsupportedTsType` records the complete checker flag set,
object flags, canonical source slice, type dependencies, and a stable
elaboration-diagnostic code. It is a total catch-all, never an omitted or
guessed type. A new
TypeScript flag or object kind makes the pin/schema gate red until assigned a
  constructor or explicit unsupported form.

The project-owned normalized grammar is also closed:

```text
TypeExpr =
  | scalar ScalarTy | literal Literal
  | variable TypeBinderId | application TypeConstructorId TypeExpr[]
  | product Field[] | sum Alternative[] | tuple TypeExpr[]
  | function parameters result
  | union TypeExpr[] | intersection TypeExpr[]
  | conditional binders check extends whenTrue whenFalse
  | exclude whole removed | infer TypeBinderId TypeExpr
  | keyof TypeExpr | indexed TypeExpr TypeExpr
  | mapped binders constraint nameType? valueType modifiers
  | templateLiteral head spans[]
  | recursive TypeExprId | external BoundaryId
```

Three total functions own the boundary:

```text
encodeRawType : TsCheckerType -> RawTsType
elaborateType : RawTsTypeGraph -> RawTsTypeId
                -> Either TypeElaborationDiagnostic TypeExpr
elaborateValueTy : TypeExpr
                   -> Either TypeElaborationDiagnostic ValueTy
```

**PROPOSED TERM — `TypeElaborationDiagnostic`.** This is a closed boundary
diagnostic, not a semantic effect refusal:

```text
TypeElaborationDiagnostic =
  | unsupportedRawType UnsupportedTsTypeId
  | externalBoundary BoundaryId
  | illScopedBinder TypeBinderId
  | nonFirstOrderValue TypeExprId
  | hostOnlyValue CarrierId
  | recursionNotAdmissible TypeExprId
  | indexTransformMismatch ProfileId
```

`encodeRawType` is total at the pinned frontend because `unsupported` is data.
`elaborateType` terminates by a visited-node set and emits explicit cycle
references. `elaborateValueTy` accepts only first-order values in the frozen
`ValueTy` universe. Function types may describe source signatures or named
block interfaces but never become serialized values. External and unsupported
types remain in the complete surface/dependency ledger; any admission profile
which needs them as a Core value returns a named elaboration diagnostic and is
refused at admission.

`A/E/R` transforms are `TypeExpr` terms with binder scope, not strings. Their
checker relation compares the normalized `TypeExpr` with the selected overload
and records every explicit refusal. This type grammar must freeze before S1 or
the generated Lean rows cannot be total.

## 3. Recognizing Effect-bearing declarations

Text searches for `Effect<` and runtime `Effect.isEffect` are forbidden. The
recognizer starts from canonical carrier declarations and walks resolved
types.

### 3.1 Closed carrier registry and roots

**PROPOSED TERM — `CarrierRegistryRow`.** Carrier recognition is generated as
a total registry, not inferred from spelling. The frozen seed rows name pinned
canonical declaration IDs for the already-known Effect/subcalculus roots and
packet declaration IDs for proposed carriers. Let `U_carrierCandidate` be the
least finite set containing those seeds and closed under canonical alias,
heritage, HKT/unification support, declared carrier type application, and every
carrier reference introduced by the frozen packet mappings. This construction
does not depend on `effectReachability` or admission-profile output;
reachability is computed afterward against the resulting registry. A profile
may reference only this registry and cannot extend it. Every candidate has
exactly one row:

```text
CarrierRegistryRow = {
  carrierId,
  origin: existingPackage | proposedProject,
  declarationRef: existing CanonicalSymbolId | proposed DeclarationId,
  discovery: seed | reached (NonEmpty<CarrierDiscoveryEdge>),
  disposition: effectCarrier | separateSubcalculusCarrier |
               coreCarrier | targetCarrier | supportOnlyNotCarrier,
  typeRootIds: NonEmpty<RawTsTypeId | TypeExprId | ValueTyId>,
  familyIds: NonEmpty<FamilyId>,
  typeClosureId: TypeClosureId
}
```

The seed set, its pin join, the candidate fixed point, registry, and
`typeClosureId` join are closed by exact set equality. A declaration may be
`supportOnlyNotCarrier`, but it may not disappear after entering
`U_carrierCandidate`. The following are required seed fixtures, not recognizer
name branches:

- `effect/Effect::Effect` and its `Success`, `Error`, `Services`, iterator,
  HKT, and unification support;
- `effect/Context::Key`, because it extends
  `Effect<Shape, never, Identifier>`;
- `effect/Exit::Exit.Proto`, because each Exit is also an Effect;
- `effect/Layer::Layer`;
- `effect/Channel::Channel`, `effect/Stream::Stream`,
  `effect/Sink::Sink`, `effect/Pull`, and `effect/Take`;
- `effect/Fiber::Fiber`, `effect/Scope::Scope`, and runtime eliminators;
- the Tx family and any public transaction carrier found by dependency
  closure; and
- project-owned IR/subcalculus carrier declarations once generated.

Existing-package roots are canonical symbol IDs emitted by the census;
project-owned roots are frozen packet declaration IDs. The recognizer consumes
these versioned data rows and structural discovery edges rather than branching
on source spellings. Every `effectReachability.carrierId`, profile
`primaryCarrierId`, and carrier named in a family/bridge role must resolve to
exactly one `CarrierRegistryRow` and its type-closure row.

### 3.2 Per-overload reachability

For every overload, emit all applicable paths:

- `returnsEffect`: the top-level result is an Effect carrier;
- `acceptsEffect`: a direct parameter is an Effect carrier;
- `callbackReturnsEffect`: a parameter contains a callable whose return
  reaches an Effect carrier;
- `callbackAcceptsEffect`: a nested callable parameter consumes an Effect;
- `containsEffect`: a property, union/intersection, collection, promise,
  conditional branch, constraint, or type argument reaches an Effect;
- `eliminatesEffect`: it accepts Effect but returns a non-Effect observation,
  such as `Promise`, `Exit`, a value, or `Fiber` runtime handle;
- `effectTypeOperator`: a type-only declaration computes or constrains
  `A`, `E`, or `R`; and
- `separateCarrier`: the path reaches Layer, Channel/Stream/Sink, Schedule,
  Tx, or another declared subcalculus.

Each fact carries the exact graph path. Recursive types use a visited set of
instantiated `(symbol, type-arguments)` nodes and emit a cycle edge; they do
not time out into “not effectful.”

The symbol aggregate is effect-bearing if any overload/member is. The
overload rows remain distinct, so one pure overload cannot hide a second form
which accepts or returns Effect.

### 3.3 Closing non-effect code

After effect reachability, compute the well-typed complement
`U_non_effect := U_row \ U_effect`. Every row still receives a conservative
surface disposition and exhaustive admission profiles:

- type-only rows close as `typeOnly` profiles and emit no runtime term;
- a value/function closes as `modeledPure` only when it has a total
  project-owned `PureExpr`/`PureAtom` meaning, an empty world frame, and any
  required host-conformance obligation;
- host values/functions not modeled as pure close as `hostOnly` and are
  forbidden in Core argument maps or values;
- JS/Node/Bun host adapters close as either
  `registeredForeignEffect` or `targetOnly`. A foreign profile requires a
  frozen implementation ID and first-order serializable request/answer data;
  an arbitrary closure instance is refused or target-only;
- a distinct formal carrier closes as `separateSubcalculus`;
- package-hidden implementation closes as `excludedInternal` only when it has
  no public exposure; and
- a public symbol may never be dropped or marked internal solely because its
  module looks auxiliary.

This is the concrete enforcement of R14a: effect-free work stays outside
`Prog`, while still remaining in the complete package ledger. Merely failing
to reach an Effect type establishes none of totality, purity, non-mutation, or
non-throwing behavior.

## 4. Conservative row disposition and exhaustive admission profiles

Every `SurfaceRowKey` has exactly one conservative row-level disposition. No
`unknown`, `todo`, `deferred`, or null disposition is permitted in a closed
ledger. Pending work lives in proof statuses and obligations, not in structural
coverage. Row disposition answers “what is the widest public boundary of this
source row?” It does not select the semantics of every admitted argument shape.

| Disposition | Meaning | Required mapping |
|---|---|---|
| `reifiedPrimitive` | A source construct is represented directly in the closed Effect Core alphabet. | IR node/operation ID, typing rule, direct handler clause, generated TS spelling, observation, laws |
| `derivedExpansion` | The construct is a macro over already classified nodes/subcalculi. | total expansion term, referenced nodes, evaluation-order policy, expansion law and termination/acyclicity evidence |
| `separateSubcalculus` | The construct belongs to a separately typed algebra which embeds into or is handled alongside Effect Core. | calculus ID, carrier/typing, composition, lowering or handler, embedding/adequacy obligations |
| `pureOrHostOnlyClosedOutsideProg` | The public row does not itself enter `Prog`; profiles distinguish `modeledPure`, `typeOnly`, and `hostOnly`. | a total pure model, a type-only boundary, or an explicit host-only prohibition; no inference of purity from type shape |
| `projectOwnedReplacementOrForeignOp` | Some public forms require a project-owned replacement or registered foreign effect; arbitrary host closures remain refused or target-only profiles. | admitted foreign profile names a registered implementation ID, first-order schemas, direct handler, frame, observation, and admission predicate |
| `targetOnly` | The construct eliminates or executes reified programs or configures the concrete target; it is not source syntax. | target adapter/runtime entry ID, accepted input carrier, output observation, G4–G6 bridge |
| `excludedInternal` | A package-hidden dependency detail retained only as pinned implementation evidence. It is invalid for a key in `U_row`. | `DependencyRow`, public-exposure proof of absence, package mask/source path, optional public mapping it implements; never an IR identity |

Disposition precedence is not name-based. A public `sync` overload, for
example, may have a conservative
`projectOwnedReplacementOrForeignOp` row disposition while its profiles are:

1. a closure-converted named block, accepted as a derived first-order graph;
2. a registered implementation ID plus serializable request data, accepted as
   a foreign effect with one direct handler; and
3. an arbitrary thunk, refused or target-only.

Admission-profile predicates are ordered, pairwise disjoint after ordering,
and exhaustive over the selected overload's source shapes. Every profile has
an explicit `accepted`, `refused`, or `targetOnly` decision. Semantic mapping,
`A/E/R`, classification transfers, observations, and proof obligations belong
to the profile. The row-level disposition is never used to infer them.

## 5. Required ledger row

The generated JSON schema must require all fields below. Optional fields are
represented by explicit tagged unions, not absent keys.

```text
SurfaceRow = {
  schemaVersion,

  // identity and pin
  rowKey: SurfaceRowKey,
  canonicalSymbolId, declarationIds[],
  mergedGroupId: none | MergedGroupId,
  package, packageVersion, sourceCommit, rootTree,
  publicSubpath, exportPath[], declarationSpace,
  memberKind: none | MemberKind,
  overloadKind: none | (call | construct | index),
  overloadOrdinal: none | Nat,

  // exposure and source
  exposures[{ exposureId, subpath, exportPath[], kind }],
  stability: stable | testing | unstable,
  visibility,
  source[{ path, start, end, syntaxKind, sha256, sourceSlice }],
  declarationTarget,
  jsTarget: none | Path,
  dtsTarget: none | Path,
  sourceMapTarget: none | Path,

  // signature: structured types plus source witnesses
  rawSignature, canonicalSignature, signatureDigest,
  typeParameters[{ name, variance, constraint: RawTsTypeId,
                   default: none | RawTsTypeId }],
  parameters[{ name, type: RawTsTypeId, optional, rest }],
  thisParameter: none | RawTsTypeId,
  returnType: RawTsTypeId,
  overloadGroupId: none | OverloadGroupId,
  runtimeKind: none | RuntimeKind,

  // closure facts
  effectReachability[{ kind, typePath[], carrierId }],
  dependencyEdges[{ kind, targetId | boundaryId, typePath[] }],
  externalBoundaries[],

  // conservative row classification
  surfaceDisposition,
  primaryCarrierId,
  primaryCarrierTypeClosureId,
  familyRoles: NonEmpty[{ familyId, role:
    primary | parameter | callback | result | bridge | lowering | handler }],

  // exhaustive, profile-owned semantics
  admissionProfiles: NonEmpty[{
    profileId,
    predicateId,
    priority,
    acceptedForm,
    rejectedFormCodes[],
    decision: accepted | refused | targetOnly,
    closureKind: modeledPure | typeOnly | hostOnly |
                 corePrimitive | derivedGraph | separateSubcalculus |
                 registeredForeignEffect | targetAdapter | refused,
    mapping:
      primitive { opDescId, termFormId, directHandlerId }
      | expansion { expansionId, referencedProfileIds[] }
      | subcalculus { subcalculusId,
                      interpretation: lowering LoweringId | handler HandlerId }
      | pure { meaning: expression PureExprId | atom PureAtomId,
               totalityObligationId,
               hostConformanceObligationId }
      | foreign { foreignOpId, implementationId, requestValueTy,
                  answerValueTy, errorRow, requirementRow,
                  directHandlerId, worldFrameId, receiptCodecId }
      | target { targetAdapterId }
      | refusal {
          reason: typeDiagnostic TypeElaborationDiagnosticId
                | admissionDiagnostic AdmissionDiagnosticId
                | casClause ExistingCasRefusalClauseRef
        },
    primaryCarrierId,
    profileTypeClosureId,
    carrierTypeClosureRefs:
      NonEmpty<{ carrierId, role, typeClosureId }>,
    familyRoles: NonEmpty[{ familyId, role }],
    indexTransform[{ inputAER: TypeExpr, outputAER: TypeExpr, ruleId }],
    abstractTransferIds: TotalMap<ClassProductDomainId, AbstractTransferId>,
    domainObligationIds:
      TotalMap<ClassProductDomainId, NonEmpty<ObligationId>>,
    observationProfileIds[], compositionLawIds[],
    generatorSpellingId: none | GeneratorSpellingId,
    obligationIds[], fixtureIds[], mutationIds[]
  }],

  // evidence and completion are independent of closure
  coverageStatus: structurallyClassified,
  notes
}
```

`ClassProductDomainId` is the frozen enumeration from `CLASSIFICATION.md`:
`aer`, `operations`, `world`, `control`, `dependence`, `progress`, `choice`,
`scopes`, `resources`, `resumptions`, `temporal`, `cancellation`, `causes`,
`foreign`, `reification`, `observations`, and `provenance`. Every profile has
one abstract-transfer entry and at least one named obligation for every domain.
An admitted program-producing profile names its semantic transfer and
soundness/precision obligation. A pure/type-only/host-only/refused/target-only
profile uses an explicit `notProgram` or proved-pure boundary entry; it cannot
inherit the empty-effect summary merely by absence.
Proof, axiom, lowering, and G3–G6 bridge statuses have one source of truth: the
profile's joined `TypeClosureRow`. They are not copied into `SurfaceRow`, and
the profile's obligation/fixture/mutation references must equal the applicable
closure-edge references by generated join checks.

Required auxiliary rows:

- `ModuleRow`: exports rule, public specifier, targets, hashes, stability,
  import result, runtime exports, and declaration entry.
- `DependencyRow`: private support declaration or explicit external boundary.
- `ExpansionRow`: normalized project-owned term and all source overloads using
  it.
- `HandlerRow`: one primitive or registered foreign operation, handler state,
  result carrier, direct clause, observations, and emitted target function.
- `AbstractTransferRow`: one `ClassProductDomainId`, primitive/expansion
  transfer equation, concretization reference, precision grade, and theorem
  obligation.
- `TypeGraphRow`: the closed `RawTsType` graph, normalization result, explicit
  boundaries/elaboration diagnostics, and TypeScript frontend pin.
- `CarrierRegistryRow`: every existing-package or proposed-project carrier,
  its total candidate disposition, type roots, families, and `typeClosureId`.
- `LawRow`: quantified statement, side conditions, observation, Lean theorem
  name, and status.
- `BridgeRow`: exact accepted domain, translation, source/target observations,
  tool/runtime pins, evidence paths, and gate.

### 5.1 Per-profile and per-carrier proof closure

**PROPOSED TERMS — `TypeClosureSubject`, `TypeClosureEdge`, and
`TypeClosureRow`.** Structural census closure and proof closure use different
carriers. Every admission profile has one subject row, and every
`CarrierRegistryRow`—whether `existingPackage` or `proposedProject`—has one
subject row. The links are mandatory even when the subject is refused,
type-only, host-only, or target-only:

```text
TypeClosureSubject =
  | surfaceProfile (rowKey : SurfaceRowKey) (profileId : ProfileId)
  | carrier (carrierId : CarrierId)

ClosureRequirement =
  | required ObligationId
  | justifiedAbsence JustificationObligationId

TypeClosureEdge = {
  requirement: ClosureRequirement,
  status: open | discharged EvidenceId,
  theoremId: none | TheoremId,
  proofStatus: notTheorem JustificationId | unstarted | stated | kernelChecked,
  axiomStatus: notApplicableNonTheorem | unreported |
               axiomsPresent AxiomId[] | axiomFree
}

TypeClosureRow = {
  typeClosureId,
  subject: TypeClosureSubject,
  typeRoots: NonEmpty<RawTsTypeId | TypeExprId | ValueTyId>,
  constructorsAndGrammar: NonEmpty<ConstructorId> x TypeClosureEdge,
  admission: AdmissionJudgmentId x TypeClosureEdge,
  semantics:
    (modeled SemanticCarrierId DenotationId
     | boundary SemanticBoundaryId) x TypeClosureEdge,
  classProduct:
    TotalMap<ClassProductDomainId,
      { abstractTransferId, obligationIds: NonEmpty<ObligationId>,
        edge: TypeClosureEdge }>,
  lowering: { artifact: none | LoweringId, edge: TypeClosureEdge },
  bridges:
    TotalMap<g3 | g4 | g5 | g6,
      { artifact: none | BridgeId, edge: TypeClosureEdge }>,
  redControls: NonEmpty<RedControlId x TypeClosureEdge>,
  proofSummary: { required, discharged, open },
  axiomSummary: { notTheorem, unreported, withAxioms, axiomFree }
}
```

`justifiedAbsence` is a proof-bearing boundary, not a missing edge; its
justification must itself be discharged before the edge closes. A lowering or
bridge artifact is present exactly when that edge's requirement is `required`.
A theorem edge has a theorem ID, never uses either non-theorem status, and must
be kernel-checked before discharge. An executable census/red-control edge has
no theorem ID and uses `notTheorem` plus `notApplicableNonTheorem`; its named
gate evidence discharges it. A semantic law or justified absence cannot be
misclassified as an executable-only edge.
A refused profile still has a total admission/refusal judgment and semantic
boundary; a type-only or host-only profile still has explicit `notProgram`
transfers. Every
`classProduct` map contains all seventeen `ClassProductDomainId` keys. Every
`SurfaceRow.admissionProfiles[].profileTypeClosureId` resolves to the matching
`surfaceProfile` subject. Every `carrierTypeClosureRefs[]`, row-level
`primaryCarrierTypeClosureId`, and `CarrierRegistryRow.typeClosureId` resolves
to the matching `carrier` subject. No subject has two closure rows.

**PROPOSED RULING — existing CAS refusal ownership.** Type-elaboration, parse,
decode, and admission diagnostics report boundary failure; they do not mint
CAS semantic refusals. For a CAS profile,
`ExistingCasRefusalClauseRef` is a reference to the existing
`Cas.Lang.Refusal.Clause` constructors and wire spelling in
`library/cas/Cas/Lang/RefusalMap.lean`; its host relation is the existing
`RefusalMap.table`. The generated ledger may project those rows and their
source digest, but must not define another CAS refusal enum, tag table, or
correspondence. Fuel exhaustion remains interpreter state `running`, and a
finite-approximation request frontier remains a frontier; neither is a
refusal reason.

**PROPOSED RULING — checked CAS ingress.** Raw CAS `PProg` remains a
representable sublanguage input, but it is not intrinsically checked. In
particular, the empty table has no entry/result and an answer operand may point
outside the preceding answer history. Therefore the packet must never declare
or generate a total `PProg -> CheckedProgram` injection. The bridge shape is:

```text
CasPProgAdmissible p =
  p.Nonempty
  and (forall line in p, line.WF)
  and (PProg.envelope p).dataflowClosed = true
  and CasEntryResultWF p

CheckedPProg = { p : PProg // CasPProgAdmissible p }

admitCas : PProg -> Except CasIngressDiagnostic CheckedPProg
injectCas : CheckedPProg -> CheckedProgram casAER
```

An equivalent `injectCas? : PProg -> Option (CheckedProgram casAER)` or
`injectCasE : PProg -> Except CasIngressDiagnostic (CheckedProgram casAER)` is
permitted if it factors through the same admission predicate. CAS profile
`TypeClosureRow.admission` references this checked domain. The existing
`RunParams.ofPProg`/`toPProg_ofPProg`/`run_ofPProg` pattern is reusable bridge
prior art, but its line/wire well-formedness alone does not discharge Core
entry, result, and dataflow obligations.

**PENDING THEOREM SET — CAS ingress.** The repaired slice owes
`admitCas_sound`, `admitCas_complete`, `injectCas_checked`, and
`injectCas_run_agree`, all quantified over `CheckedPProg` or successful
admission. Empty and dangling-answer tables are permanent negative witnesses;
no theorem may quantify `injectCas_checked` over arbitrary `p : PProg`.

**PROPOSED RULING — diagnostic registers.** The checker signature is:

```text
check : RawProgram -> Except CheckDiagnostic (Sigma CheckedProgram)
```

It and `admitCas` are deterministic, fail-fast admission boundaries; a failure
returns one selected diagnostic under a frozen traversal order. The
surface/profile census is a different register:
it accumulates every row, obligation edge, and zero-counter violation in its
generated reports. Census accumulation does not imply that the program checker
returns every condemnation, and checker fail-fast behavior does not permit the
census to stop after its first missing profile. A future accumulating
`checkAll` would be a separately named diagnostic tool with separate theorems,
not an alias for `check`.

**PROPOSED TERMS — `TypeClosureCounterId` and `CutoverSummary`.** The generated
ledger reports proof closure separately from surface closure:

```text
TypeClosureCounterId =
  | missingProfileTypeClosureLink | missingCarrierTypeClosureLink
  | duplicateTypeClosureSubject | missingTypeRoot
  | missingConstructorGrammarEdge | missingAdmissionEdge
  | missingSemanticEdge | missingClassProductDomainEdge
  | missingLoweringEdge | missingBridgeEdge | missingRedControlEdge
  | missingProofStatus | missingAxiomStatus
  | unreportedAxiomEdge | disallowedAxiomEdge | openTypeClosureEdge

CutoverSummary = {
  cutoverPolicyId,
  censusClosed: Bool,
  profileClosureRowsComplete: Bool,
  carrierClosureRowsComplete: Bool,
  requiredTypeClosureEdges,
  dischargedTypeClosureEdges,
  openTypeClosureEdges,
  zeroCounters: TotalMap<TypeClosureCounterId, Nat>,
  fullCutoverEligible: Bool
}
```

**PENDING THEOREM — `fullCutoverEligible_iff`.** The Boolean is true exactly
when `censusClosed`, both closure-row completeness fields are true,
`openTypeClosureEdges = 0`, and every `zeroCounters` entry is zero under the
frozen `cutoverPolicyId`. Consequently, any missing/duplicate link, open
required profile/carrier edge, open justified-absence obligation, unreported
axiom set, or disallowed axiom forces `fullCutoverEligible = false`, even if the
package census is structurally closed.

**PENDING THEOREM SET — generated closure checks.** The generated Lean
projection must expose, at minimum:

```text
profile_typeClosure_unique :
  forall row profile, profile in row.admissionProfiles ->
    exists! closure, closure.subject = surfaceProfile row.rowKey profile.id

carrier_typeClosure_unique :
  forall c, c in carrierRegistry ->
    exists! closure, closure.subject = TypeClosureSubject.carrier c.carrierId

classProduct_typeClosure_total :
  forall closure domain, exists! edge, closure.classProduct domain = edge

open_edge_blocks_cutover :
  exists closure edge, requiredOpen closure edge ->
    fullCutoverEligible summary = false

cas_refusal_projection_exact :
  projectedCasClauses = Cas.Lang.Refusal.Clause.all and
  projectedCasRows = Cas.Lang.RefusalMap.table
```

The first three depend only on generated row decidability and exact-set joins;
the cutover theorem also depends on the frozen policy and current axiom report.
The CAS theorem imports the existing CAS definitions rather than restating
their constructors.

## 6. Closed semantic families and constructive mapping

The public surface universe maps through profile-owned roles into the packet's
closed first-order model. This checklist does not introduce a second Core
carrier. The only carrier and operation shapes it may name are:

```text
OpDesc = request ValueTy
       × answer ValueTy
       × typedErrors ErrorRow
       × requirements RequirementRow
       × resumption/cancellation/observation metadata

RawProgram = finite serializable tables of regions, code points, blocks,
             handlers, pure atoms, foreign atoms, and an entry
CheckedProgram A E R = RawProgram plus ProgramWF and synthesized A/E/R
Block = typed parameters × owning RegionId × one Term
Term = close | jump | call | perform | raise | die | branch | scope | provide
     | onExit | fork | join | interrupt | yield | race | mask
Resume = destination BlockId × typed first-order ArgMap × one-shot ownership
```

Every continuation, cause arm, handler body, finalizer, scope body, child, and
race arm is a `CodeId`/`BlockId` plus explicit serializable captures. No census
row or generated program stores `X -> Core`, `Cause -> Core`, `Restore -> Core`,
or another host function. Cycles and recursion are first-order code-point
references. `perform` refers to an `OpDesc`, so its answer, typed-error, and
requirement contributions are available to `A/E/R` synthesis.

Only `corePrimitive` and `registeredForeignEffect` mappings own direct handler
rows. A derived expansion closes over operations which have handlers; a
subcalculus owns a typed lowering or its own handler/embedding; pure, host-only,
type-only, refused, and target-only mappings own no Core handler.

| Semantic family | Public anchors at rc.112 | Constructive representation | Composition/laws to register | Direct handler/observation |
|---|---|---|---|---|
| Type indices and carrier | `Effect.Effect<A,E,R>`, `Success`, `Error`, `Services`, `Variance`, HKT/Unify helpers | `CheckedProgram A E R`; all three source indices are covariant at `src/Effect.ts:117–157` | weakening; union of errors/services under composition; service discharge by `Exclude` | type elaborator; no runtime event |
| Success and failure | `Effect.succeed`, `fail`, `failCause`, `die`, `exit`; `Cause`; `Exit` | `close`, `raise`, `die`, typed cause exits; project `CauseTree`; pinned runtime `CauseV4 = List Reason` | pure/failure branch laws; project cause topology; explicit lossy quotient to pinned reason combination | outcome handler; project full-cause observation or runtime reason-list observation, never conflated |
| Sequencing | `flatMap`, `map`, `flatten`, `andThen`, `tap`, `all`, `forEach`, `gen` | `bind` primitive plus derived normalized terms; `gen` elaborates to bind spine | left/right identity, associativity, evaluation order, short-circuiting | sequential handler |
| Error handlers | `catch`, `catchCause`, tag/reason/filter variants, `match*`, `sandbox`, `unsandbox`, `either`/`result` forms | named body and cause-exit regions plus derived selectors | success bypass, failure selection, unhandled-cause propagation, handler associativity under named observation | cause operation handlers and machine region semantics |
| Environment and services | `Context.Key/Service/Reference`, `Effect.service`, `context*`, `provide*`, `updateService*` | typed `ask key`, `environment`, `localEnv/provide`; Reference default is an explicit handler clause | ask/provide, shadowing, unrelated-service commutation where stated; A/E/R transforms exactly mirror signatures | environment-map handler; lookup/provision trace |
| Layer graph | `Layer.Layer<ROut,E,RIn>`, constructors, `build`, `provide`, `merge`, `memoize`, `launch` | `LayerCore` separate subcalculus: service nodes, dependency edges, scoped acquisition, ordered composition, memo key | identity/associativity for typed composition; dependency discharge; memoization and merge laws only with stated observations | direct Layer builder lowering to scoped Core; build trace |
| Scope and resources | `Scope`, `scoped`, `acquireRelease`, `acquireUseRelease`, `addFinalizer`, `ensuring`, Pool/Resource/Scoped* | scope region plus allocate/register/release operations | exactly-once release, close idempotence, reverse sequential finalizers, exit-aware release, cause combination; parallel strategy separately | scope-state handler; acquisition/finalizer trace |
| Fibers and interruption | `forkChild`, `forkIn`, `forkScoped`, Fiber `await/join/interrupt/poll`, interrupt masks, `yieldNow` | child-program `fork`, `await`, `interrupt`, `poll`, `yield`, `mask/restore`; explicit fiber IDs/topology | structured parent/child ownership, join/Exit law, pending interruption, mask restoration; scheduler-qualified equations | scheduler/fiber handler; labeled event tree and terminal exits |
| Parallel/race | concurrent `zip/all/forEach`, `race*`, timeout combinators | derived or primitive policy nodes over fork/await/interrupt; profile decides by evaluation semantics | winner rule, loser interruption, every loser finalized before parent resume, all-failure rule, deterministic special cases; equivalence only under declared trace quotient | concurrency handler parameterized by schedule |
| Time, scheduling, recurrence | `Clock`, `sleep`, `delay`, `timeout`; `Scheduler`; `Schedule`/`ExecutionPlan`/`Cron` | TimeSig `now/sleep`; scheduler policy is handler state; Schedule is a pure/typed recurrence subcalculus lowered into repeat/retry | virtual-time monotonicity, schedule step laws, retry/repeat unfolding, no wall-clock equation without host assumptions | virtual-clock/direct scheduler handler; time/schedule events |
| Randomness and crypto | `Random`, random combinators, `Crypto` | RandomSig sample operations with explicit generator state; crypto/host entropy as separate foreign ops | seeded state transition and range laws; distribution claims require separate evidence | deterministic seeded handler for proofs; host handler for G6 |
| Async and host suspension | `suspend`, `sync`, `promise`, `callback`, `withFiber`, custom `Effectable` | closure-converted named block becomes a code-point graph; only registered implementation ID plus serializable payload becomes `ForeignEffect`; arbitrary callback/promise/evaluator is refused or target-only | one-shot resume/cancel laws, synchronous-resume case, callback totality for admitted blocks | registered foreign-op direct handler; resume/cancel trace |
| Mutable state and coordination | `Ref`, `SynchronizedRef`, `Deferred`, Queue/PubSub, Semaphore/Latch, Cache/Pool, subscriptions and fiber collections | abstract handle allocation plus typed get/modify/await/offer/take/publish/acquire/release operations | sequential state equations; blocking/wakeup/permit conservation; concurrency properties under event-tree semantics | store/coordination handler with explicit state |
| Transactions | `TxRef`, `TxQueue`, `TxDeferred`, other `Tx*`, and their Effect commit boundary | `TxCore` separate subcalculus with read/write/retry/orElse/commit and atomic lowering | isolation/atomic commit, retry wakeup, rollback, orElse laws | transactional state handler; commit/retry trace |
| Requests and batching | `Request`, `RequestResolver`, request/cache/batching APIs | RequestSig plus resolver handler, cache and batch state | resolver naturality, batching partition/order policy, cache hit equivalence under stated observation | request handler; request/batch/cache trace |
| Channel family | `Channel`, `Pull`, `Take`; `Stream` and `Sink` | `ChannelCore` separate typed transducer calculus; Stream/Sink are typed views/lowerings | pipe identity/associativity, emit/read/done/fail, concat, resource and concurrency laws with side conditions | Channel handler into Core/event tree |
| Schema and other description algebras | `Schema*`, `JsonSchema`, formatting/equivalence modules | their own closed calculi; pure construction stays outside Core, effectful decoding/encoding crosses through explicit ops | owned codec/refinement/transformation laws | direct schema handler or project-owned codec boundary |
| Runtime and execution | `Runtime`, `ManagedRuntime`, `runFork`, `runPromise*`, `runSync*`, scheduler installation | `targetOnly` eliminators over closed Core | observation extraction and bridge composition, never a Prog constructor | pinned Effect runner, compiler, and host adapters |
| Testing and unstable domains | `effect/testing/**`, `effect/unstable/**` | classified by profile carrier/family roles exactly as stable rows; TestClock etc. may provide alternative primitive/foreign handlers | same family laws plus a stability flag; no blanket exclusion | handler only on primitive/registered-foreign profiles |
| Pure support | Array, Option/Result, collections, functions, predicates, ordering, formatting, types | profile split: `modeledPure` total definitions, `typeOnly`, or `hostOnly`; all outside Prog | ordinary pure laws and totality only for modeled profiles; host-only has no purity claim | no effect handler; pure evaluator only for a proved/model-backed profile |

### 6.1 Project cause topology and the pinned runtime quotient

The project model deliberately retains more causal topology than rc.112:

```text
CauseTree E = fail E | die Defect | interrupt FiberId
            | then (CauseTree E) (CauseTree E)
            | both (CauseTree E) (CauseTree E)

ProjectCause E = none | some (CauseTree E)
RuntimeReason E = Fail E | Die Defect | Interrupt FiberId
RuntimeCauseV4 E = List (RuntimeReason E)
```

`none` represents the pinned runtime's empty cause value. The only stock-runtime
bridge is the explicit lossy quotient:

```text
forgetCause none                  = []
forgetCause (some (fail e))       = [Fail e]
forgetCause (some (die d))        = [Die d]
forgetCause (some (interrupt f))  = [Interrupt f]
forgetCause (some (then x y))     = forgetCause (some x) ++ forgetCause (some y)
forgetCause (some (both x y))     = forgetCause (some x) ++ forgetCause (some y)
```

Parallel children use canonical child order before quotienting. `forgetCause`
is intentionally non-injective: `then x y` and `both x y` can have the same
rc.112 reason list. Therefore:

- Lean/model and `TsCore` claims may observe full `CauseTree` topology;
- stock rc.112 G4 claims observe only the ordered reason list (plus separately
  declared runtime events); and
- no G4 statement through the unmodified runtime may claim preservation or
  reflection of full sequential/parallel cause topology.

A stronger hosted claim requires separately pinned instrumentation which emits
project cause-topology receipts; it is not a claim about stock `Cause` alone.
Every cause law and bridge row names either `projectCauseTree` or
`runtimeReasonList` as its observation profile.

### 6.2 Static `A`, `E`, `R` obligations

Each admission profile's `indexTransform` is not descriptive prose. It is a
normalized `TypeExpr` checked against the selected overload and the profile's
accepted source shape. Examples from the pin which must appear as fixtures
include:

- `flatMap`: `A -> Effect<B,E1,R1>` transforms
  `Effect<A,E,R>` to `Effect<B,E1 | E,R1 | R>`;
- `catchCause`: transforms `Effect<A,E,R>` with a handler returning
  `Effect<A2,E2,R2>` to `Effect<A | A2,E2,R | R2>`;
- `provideService`: removes the provided identifier from `R` with `Exclude`;
  and
- `provide` with a Layer unions Layer errors and inputs while excluding the
  services supplied by the Layer.

The generated Lean type-expression representation must preserve unions,
`Exclude`, conditional inference, `never`, and overload quantifier scope. A
runtime test cannot establish these static facts.

## 7. Mapping and direct-handler completeness

An admission profile is accepted only when its own mapping obligation is
structurally closed:

- [ ] Each `corePrimitive` profile names exactly one `OpDesc`/region form and
  exactly one direct handler clause.
- [ ] Each direct handler states its carrier/state monad, input/output types,
  error/cause behavior, service environment, trace labels, and terminal
  observation.
- [ ] Each `derivedGraph` profile references only already classified profiles
  or an explicitly recursive code point; the expansion graph is acyclic
  otherwise. It owns an expansion law, not a duplicate direct handler.
- [ ] Each `separateSubcalculus` profile has either a total lowering into Core or a
  direct handler plus an embedding relation. “Separate” never means unmodeled.
- [ ] Each `registeredForeignEffect` profile has a closed operation name,
  registered implementation ID, first-order payload/result/error/service
  schema, world frame, receipt codec, admission predicate, and exactly one
  direct handler. No field contains the arbitrary source closure.
- [ ] Each arbitrary closure/promise/evaluator profile is explicitly `refused`
  or `targetOnly`; no fallback turns it into a serializable operation.
- [ ] Each `targetOnly` profile names the runner/adapter and bridge observation.
- [ ] Each `modeledPure` profile has a total model and empty world frame;
  `typeOnly` emits no runtime value; `hostOnly` cannot appear in a Core term.
- [ ] `excludedInternal` occurs only on dependency evidence and cannot be used
  as a generated public import or IR identity.
- [ ] Every admitted program-producing profile has a total `ClassProductDomainId`
  transfer map and per-domain proof obligations.
- [ ] Every IR node has a source-origin set or an explicit project-owned
  rationale; orphan nodes are red.

Internal runtime labels are evidence, not language identity. The rc.112
implementation's `Primitive` protocol and `makePrimitiveProto/makePrimitive`
live at `src/internal/core.ts:365–458`; package exports mask internal imports.
The checker may record those implementation paths and compare handler
behavior, but public canonical IDs and generated programs use public APIs.

## 8. Effect language service harness

The generation/reification harness must run the Effect language service in
addition to the independent export/type census and ordinary TypeScript checks.
For TypeScript 7, the required route is the estate's already pinned
`@effect/tsgo@0.38.0`: its native frontend includes the Effect diagnostics,
quick fixes, and refactors and exposes the configuration plugin name
`@effect/language-service`. The older standalone package is not installed and
is not prescribed for this lane. No source is fetched and no new tool is
admitted by this checklist.

### 8.1 Pin state and required fields

The TS7 execution path is exact and singular:

- `typescript@7.0.2`, git head
  `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`;
- `@effect/tsgo@0.38.0`;
- the matching platform package, `@effect/tsgo-<os>-<arch>@0.38.0` (locally
  `@effect/tsgo-darwin-arm64@0.38.0`);
- platform `upstream.json` entry mapping TypeScript `7.0.2` to that same git
  head; and
- the dedicated tsconfig plugin entry named `@effect/language-service`.

`library/effects/scripts/patch-toolchain.ts` is the existing installation
route: it invokes `effect-tsgo patch --typescript --oxlint`. The harness must
verify that patch state rather than assuming the dependency's presence means
the active `tsc` is Effect-aware. The old repository pin in parser-census is
retained only as historical provenance for the lineage of the language
service; it is not executed, installed, or made a second diagnostics leg.

The language-service run record must contain:

- `@effect/tsgo` npm package/version, integrity, lockfile row, resolved path,
  CLI `--version`, package hash, and the Effect-TS/tsgo repository pin once it
  has a G0 source-lock row;
- platform binary package name/version/integrity/hash and its complete
  `upstream.json` digest;
- TypeScript package/version/git head/integrity and proof that the platform
  component metadata selects the same git head;
- successful patch receipt for both `--typescript` and `--oxlint`;
- Effect peer/dependency range and actually resolved Effect version;
- Node/Bun/OS/architecture used to host the service;
- complete plugin configuration, rule severities, overrides, and SHA-256;
- diagnostic-rule catalog digest and code-action/refactor catalog digest;
- generated input file hashes, the exact expected file set, and the exact file
  set reported by `--list-files`; and
- normalized diagnostics, quick fixes, refactors, and output edit hashes.

Any change in those fields is a red drift event requiring an explicit
re-admission and refreshed fixtures. Diagnostic message prose is evidence but
not identity; stable rule code, action kind, source span, and edit bytes form
the normalized key. The standalone `Effect-TS/language-service` version/pin is
recorded as historical lineage only and cannot satisfy or drift this TS7 gate.

### 8.2 What the language service checks

Run with diagnostics, refactors, quick information, completions, and code
actions enabled under a dedicated harness config. From the locally installed
machine-readable schema, the relevant Effect-aware classes include:

- dropped/floating Effect values and effects run inside effects;
- missing `A`, `E`, or `R` context/service information and leaking
  requirements;
- invalid or noncanonical `Effect.gen` yield/return shapes;
- opportunities and mistakes around `Effect.fn`, `map`/`flatMap`, `pipe`,
  catch/provide chains, and Layer dependency composition;
- unsafe Effect type assertions, lazy effects/promises, raw `Promise`, async
  functions, and try/catch in generators;
- host globals such as console, date/time, fetch, randomness, timers,
  `process.env`, abort controllers, and Node builtins where configured;
- duplicate Effect packages, outdated API forms, deterministic service keys,
  service-class shapes, and Schema/Effect source patterns; and
- canonical code actions/refactors associated with those recognized patterns.

This makes the tool an excellent Effect-aware source-pattern critic for
generated TypeScript and a second witness that generated code uses idiomatic,
recognized public forms.

It cannot establish any of the following:

- exports-map/module/symbol/overload closure;
- canonical source-symbol identity;
- completeness or correctness of the disposition ledger;
- source-to-Core typing or denotation preservation;
- direct-handler laws, expansion laws, or subcalculus embeddings;
- agreement with the Effect runtime;
- TypeScript-to-JavaScript compilation preservation; or
- Node/Bun hosted behavior.

Those remain independent G3–G6 obligations. Language-service silence is not a
semantic proof.

### 8.3 Cross-check and clean generated-program gate

- [ ] Run the machine-readable command
  `bun run --cwd experiments/effect-core-surface typecheck` from the repository
  root. Require the package script to equal `effect-tsgo diagnostics --project
  tsconfig.json --format json --strict --list-files`. Running in the experiment
  directory is required for discovery of its pinned local TypeScript install.
  The dedicated config is a frozen, handwritten harness input, not a generated
  file.
- [ ] Require valid JSON, zero stderr except declared progress output, and the
  exact schema fields `diagnostics`, `files`, and `summary`.
- [ ] Require `summary.filesChecked = summary.totalFiles` and set equality
  between the canonicalized `files[].file` paths and the dedicated tsconfig's
  independently resolved source set. A tool which silently skips a generated
  file is red even when diagnostics are empty.
- [ ] Require every file row to report `detectedEffect: "v4"` and
  `supportedEffect: "v4"`.
- [ ] The independent census runs first and owns canonical symbol IDs.
- [ ] Every Effect symbol named in a language-service diagnostic/action must
  resolve to a census exposure and canonical symbol ID.
- [ ] Every import inserted by a quick fix must resolve through the package
  exports map and land in `U_package`.
- [ ] A language-service rule catalog is not allowed to add or remove public
  universe rows; it is a separate relation over source fixtures.
- [ ] All generated positive programs parse, typecheck, and produce zero
  unapproved Effect-language-service diagnostics under the dedicated config.
- [ ] Suggestions are included in the captured output even if they do not
  affect process exit; the clean gate decides them explicitly.
- [ ] No global message-text baseline or blanket rule disabling is allowed.
  A necessary exception is keyed by rule code, canonical symbol/fixture,
  reason, and expiry pin.
- [ ] Diagnostics and actions are canonical JSON sorted by file, span, rule
  code, action kind, and edit digest; two fresh runs are byte-identical.

The local control run over the current `library/effects/tsconfig.json` observed
43 checked files out of 43, every file detected/supported as Effect v4, with
zero errors, warnings, or messages. That is a live-path witness for the current
project, not the future generated-program gate and not a semantic claim.

### 8.4 Canonical quick-fix loop

For each admitted code action/refactor fixture:

1. start from canonical fixture bytes with exactly the expected triggering
   diagnostic/action set;
2. select the action by normalized `(ruleCode, actionKind, targetSpan,
   descriptionKey)`, never by array position;
3. apply its text edits with overlap/order checks;
4. parse and typecheck the result;
5. resolve every inserted import against `U_package` and the canonical census;
6. elaborate/parse back into the project-owned IR and compare with the
   fixture's declared expected IR or declared semantic change;
7. render the fixed IR/source through the canonical printer;
8. rerun the language service and require the triggering diagnostic to be gone
   with no new unapproved diagnostics; and
9. apply the same action pipeline again and require zero edits and
   byte-identical output.

This is the quick-fix/parse-back/idempotence gate. For a style-only fix, the
pre- and post-fix IR must be identical. For an explicitly semantic fix, the
fixture names both IRs and the intended translation; no action is presumed
semantics-preserving merely because it is offered.

### 8.5 Language-service red controls

The self-test suite must plant at least:

- an ignored floating Effect;
- an Effect executed from inside another Effect;
- a raw `new Promise`/async boundary in an Effect path;
- a generator with missing `yield*`, nested/returned Effect misuse, and
  try/catch;
- a missing service dependency or leaking requirement;
- an unsafe Effect type assertion;
- a noncanonical map/flatMap or Effect.fn pattern with an expected quick fix;
- a Layer dependency-composition defect;
- a forbidden host global in an Effect path;
- a duplicate or mismatched Effect package fixture;
- a quick fix that inserts a nonexistent or null-masked import;
- overlapping/out-of-order quick-fix edits;
- a fix whose output does not parse or typecheck;
- a style fix whose parse-back changes the IR;
- a non-idempotent fix which produces edits on the second pass; and
- a planted language-service version/config/catalog drift.

Also remove one generated file from the dedicated tsconfig and arrange one
extra unrelated file in the diagnostics result: each direction must fail the
file-set equality gate even with an empty diagnostics array.

Each mutant must make the dedicated gate red for its intended reason. A
mutant caught only by ordinary TypeScript or only by the export census does
not establish that the language-service leg is live.

## 9. Closure invariants

The future gate must check all invariants in one run and report the first
counterexample plus full totals.

1. `resolvedExportTargets = publicJsTargets = publicDtsTargets` for code
   entries.
2. Every public entry imports successfully; every null-masked control fails
   through normal package resolution.
3. Every public exposure resolves to exactly one canonical symbol; every
   canonical public symbol has an exposure.
4. `U_symbolSpace`, `U_member`, `U_call`, `U_construct`, and `U_index` are
   pairwise disjoint and their union is exactly `U_row`; every member and
   signature has one structurally smaller owner and overload ordinals are
   unique in their group.
5. Every dependency edge closes on a row or explicit boundary.
6. Every `U_row` key has exactly one conservative `surfaceDisposition`, one
   `primaryCarrierId`, and a nonempty set of family/bridge roles.
7. Every effect-reachability fact carries a path to a canonical carrier.
8. Every row's admission-profile predicates are ordered, disjoint, and
   exhaustive; every profile has one decision and its own mapping,
   `indexTransform`, observations, and obligations.
9. Every profile has one abstract transfer and a nonempty proof-obligation set
   for every `ClassProductDomainId`; nonprogram profiles use explicit
   `notProgram`/proved-boundary transfers rather than omitted keys.
10. Exactly primitive and registered-foreign profiles own direct Core handler
    IDs; expansions close through referenced operations, and no other profile
    owns a duplicate handler.
11. `excludedInternal` occurs only in `DependencyRow`, and no such dependency
    has a public exposure or IR identity.
12. `modeledPure` has a total model and empty frame; `typeOnly` and `hostOnly`
    emit no Core node or value; arbitrary closures are refused or target-only.
13. `targetOnly` appears only at a run/configuration/observation boundary.
14. Every `derivedGraph` expansion is closed over mapped profiles and its evaluation
    order is explicit.
15. Every subcalculus has a typed handler or total lowering.
16. Every registered foreign operation has first-order closed schemas,
    implementation ID, frame, receipt codec, and exactly one direct handler.
17. Every generated public import resolves without `internal` paths.
18. Every generated positive program is TypeScript-clean and
    language-service-clean under the frozen configurations.
19. Every generated artifact is byte-identical to a fresh run.
20. Counts and digests are derived and recorded; no expected surface count is
    hardcoded in extractor source.
21. `U_carrierCandidate` equals the set of `CarrierRegistryRow` subjects; every
    existing-package or proposed-project carrier has exactly one registry row,
    one `typeClosureId`, and only recorded carrier dispositions.
22. Every admission profile has exactly one matching profile
    `TypeClosureRow`; every carrier registry row has exactly one matching
    carrier `TypeClosureRow`; every row/profile carrier reference joins to the
    same subject rather than to an untyped identifier.
23. Every `TypeClosureRow` has nonempty type roots and constructor/red-control
    evidence, one admission edge, one semantic edge, explicit lowering, a
    total G3–G6 bridge map, and exactly one transfer/obligation edge for every
    `ClassProductDomainId`. Every required edge records proof and axiom status.
24. CAS semantic refusals referenced by the ledger are exactly existing
    `Refusal.Clause` values projected through the existing `RefusalMap`; there
    is no second CAS refusal enum or table. Fuel exhaustion is `running`, and
    request frontier is frontier, never refusal.
25. The census closure summary must be zero in missing/duplicate row keys,
    profile gaps/overlaps, unresolved types or dependencies, missing profile
    mappings, missing required handlers, missing per-domain transfer IDs, and
    missing exposures. Proof statuses may remain open without reopening this
    structural census.
26. The type-proof closure summary must separately report these counters, all
    of which are zero before full cutover:
    `missingProfileTypeClosureLink`, `missingCarrierTypeClosureLink`,
    `duplicateTypeClosureSubject`, `missingTypeRoot`,
    `missingConstructorGrammarEdge`, `missingAdmissionEdge`,
    `missingSemanticEdge`, `missingClassProductDomainEdge`,
    `missingLoweringEdge`, `missingBridgeEdge`, `missingRedControlEdge`,
    `missingProofStatus`, `missingAxiomStatus`, `unreportedAxiomEdge`,
    `disallowedAxiomEdge`, and `openTypeClosureEdge` (including an open
    `justifiedAbsence` obligation).
27. `requiredTypeClosureEdges = dischargedTypeClosureEdges +
    openTypeClosureEdges`, and `openTypeClosureEdges` equals the
    `openTypeClosureEdge` zero-counter entry. All summary counts are recomputed
    from rows, never maintained independently.
28. `fullCutoverEligible` is false whenever any counter in invariant 26 is
    nonzero or any required profile/carrier closure edge is open. It cannot be
    inferred from `censusClosed` alone.
29. Every CAS-to-Core profile accepts `CheckedPProg` or the successful branch of
    an `Option`/`Except` admission function. No generated declaration has type
    `PProg -> CheckedProgram`; the empty table and dangling-answer table are
    rejected before injection.
30. Program/CAS admission returns one fail-fast diagnostic under frozen order.
    Surface/profile census reports accumulate all structural and proof-closure
    violations. No theorem or counter equates these two diagnostic registers.

## 10. Red falsifier matrix

The checker is not accepted until `--self-test` proves that each planted defect
turns the intended gate red.

| Mutant | Required red result |
|---|---|
| Add a public file two or more directories below an unstable barrel | module/export closure changes; no depth-bound omission |
| Remove either MultipartParser module from the expected fresh census | missing-module failure |
| Add a `.d.ts`-only exported type | type surface changes even though runtime `typeof` does not |
| Add a runtime export absent from declarations | JS/DTS set disagreement |
| Add a null-masked `internal` candidate | excluded from public set; forced import fails |
| Alias one symbol through root and direct module | two exposures, one canonical symbol |
| Merge a value/type/namespace under one name | separate declaration-space rows linked by merge group |
| Give one overload a pure shape and another an Effect callback | both overloads retained; aggregate effect-bearing |
| Add data-first and data-last overloads with reversed argument order | distinct overload IDs, same declared expansion if appropriate |
| Hide Effect under callback return, conditional branch, type alias, union, or generic constraint | exact effect-reachability path emitted |
| Add a recursive type alias | terminating dependency cycle record, not omission |
| Reference a non-exported support type from a public signature | private support row in dependency closure |
| Omit one member, call, construct, or index constructor from `SurfaceRowKey` | row-universe partition/coverage failure |
| Place an overload row in `U_effect` and subtract it from a symbol-only carrier | row-domain type/partition failure |
| Add a new TypeScript `TypeFlags`/`ObjectFlags` case | explicit `unsupported` row or schema-drift failure; never silent omission |
| Require an unsupported/external type as a Core value | named `TypeElaborationDiagnostic`; surface row remains present |
| Drop or duplicate a disposition | totality/uniqueness failure |
| Leave an admission-profile source shape uncovered or covered twice | profile exhaustiveness/disjointness failure |
| Give one profile a semantic mapping only at row level | profile-owned-mapping failure |
| Remove one profile's family role, A/E/R transform, observation, or ClassProduct transfer | profile completeness failure |
| Remove a profile's `profileTypeClosureId` or point it at another profile | missing/mismatched profile-closure-link failure |
| Add a proposed or existing carrier without its `CarrierRegistryRow` or carrier `TypeClosureRow` | carrier-universe/type-closure failure |
| Duplicate a `TypeClosureSubject` under two closure IDs | type-closure subject uniqueness failure |
| Remove one constructor/grammar, admission, semantics, lowering, bridge, red-control, proof-status, or axiom-status edge | named type-closure edge counter becomes nonzero |
| Remove one domain from a closure row's `classProduct` map | per-domain type-closure totality failure |
| Alter a cutover total without changing its closure rows | summary-count equation failure |
| Mark `fullCutoverEligible` true while any required type-closure edge is open | cutover-equation failure |
| Give `injectCas` the total domain `PProg` | empty-table and dangling-answer witnesses refute `ProgramWF`; CAS-ingress-domain failure |
| Admit an empty CAS table or a table whose `.ans i` is not strictly earlier | `admitCas` soundness/negative-control failure |
| Require the fail-fast checker to return every simultaneously condemning clause | diagnostic-register theorem-shape failure |
| Stop the surface/profile census after its first violation | accumulated-census completeness failure |
| Mark a public exposure `excludedInternal` | visibility/disposition failure |
| Mark a host closure `derivedGraph` without an admission predicate | foreign-boundary failure |
| Serialize an arbitrary closure inside a foreign request | first-order ValueTy/admission failure |
| Remove a primitive/registered foreign handler or observation | handler-completeness failure |
| Attach a direct Core handler to a pure/target/refused row or derived expansion | handler-ownership failure |
| Add a derived expansion cycle | expansion-closure failure |
| Remove a subcalculus lowering/handler | subcalculus-completeness failure |
| Define a second CAS refusal enum/table or change a projected clause spelling | existing `Refusal.Clause`/`RefusalMap` identity failure |
| Report fuel exhaustion or a request frontier as refusal | status/frontier-versus-refusal disjointness failure |
| Claim rc.112 G4 preserves `CauseTree.then` versus `CauseTree.both` | observation-profile failure: stock runtime exposes only the lossy reason list |
| Emit an internal import | public-import failure |
| Change package version, integrity, source commit, compiler, or config | pin/drift failure before extraction |
| Hand-edit one generated byte | regeneration byte gate failure |
| Plant each language-service defect from §8.5 | language-service self-test failure for the named leg |

## 11. Generated artifacts and command contract

These exact paths and task names are proposed for the frozen packet. They do
not exist yet and must not be implemented before freeze.

### 11.1 Hoover outputs

Under `experiments/effect-core-surface/generated/`:

- `source-snapshot.json` — source/npm/compiler/effect-tsgo language-service
  identities and every read file's digest;
- `module-closure.json` — exports rules, resolved public specifiers, targets,
  imports, and runtime-value cross-check;
- `symbol-closure.json` — exposures, canonical identities, members,
  declaration spaces, overloads, and signatures;
- `type-graph.json` — the closed `RawTsType` graph, normalized `TypeExpr`
  results, explicit external/unsupported boundaries, and elaboration
  diagnostics;
- `dependency-closure.json` — the complete typed dependency graph and explicit
  boundaries;
- `effect-reachability.json` — carrier roots and every reachability path;
- `reification-ledger.json` — conservative row dispositions, exhaustive
  admission profiles, the complete `CarrierRegistryRow` set, primary carriers,
  family/bridge roles, first-order mappings, `A/E/R` transforms, abstract
  transfers, handlers, laws, observations, and statuses;
- `type-proof-closure.json` — every profile and every existing/proposed carrier
  subject, its type roots, constructor/grammar, admission, semantics,
  per-domain transfer, lowering, G3–G6 bridge, red-control, proof, and axiom
  edges, plus `CutoverSummary`;
- `language-service-report.json` — tool/config pins, normalized diagnostics,
  actions, fix runs, parse-back, and idempotence results;
- `coverage-report.json` — all set cardinalities and invariant counters;
- `red-controls.json` — named mutants and the gate which killed each; and
- `change-report.json` — old/new set and signature differences on an explicit
  pin-change run.

All JSON is canonical, schema-versioned, newline-terminated, and generated.
The runtime census is a joined input/cross-check, not copied into these files.

### 11.2 Model and human projections

- `formal/effect-core-v1/EffectCore/Generated/PublicSurface.lean` — generated
  first-order row keys, structured types, conservative dispositions, profiles,
  family roles, carrier registry, mappings, abstract-transfer IDs, dependency
  edges, type-closure links, and obligation IDs;
- `formal/effect-core-v1/EffectCore/Generated/SurfaceChecks.lean` — decidable
  totality/uniqueness/census predicates over those rows;
- `formal/effect-core-v1/EffectCore/Generated/TypeClosure.lean` — generated
  profile/carrier closure subjects and edges, zero counters, and cutover
  Boolean consumed by proof modules; and
- `formal/effect-core-v1/generated/EFFECT-PUBLIC-SURFACE.md` — generated human
  semantic projection from the same ledger, never a second maintained table.

Generation of the Lean and Markdown projections begins only after the JSON
schema, carrier/family/bridge-role IDs, `TypeClosureRow` edge vocabulary, and
abstract-transfer registry are frozen. Proof modules discharge generated
closure edges and consume generated rows; they do not regenerate or
reinterpret upstream TypeScript.

### 11.3 Exact future commands

```text
mise run gen:effect-core-surface
mise run check:effect-core-surface
mise run check:effect-core-surface:red
mise run check:effect-core-v1
mise run check:effect-core-v1:cutover
mise run check
mise run check:ci
```

Command meanings:

- `gen:effect-core-surface` runs the hoover and all projections from declared
  pins and writes only the paths above.
- `check:effect-core-surface` verifies pins, regenerates to a temporary
  directory, checks independent export/runtime and language-service legs,
  asserts structural invariants and proof-counter consistency, and compares
  bytes. Open proof edges are reported and force cutover false; they do not
  make a structurally complete census fail.
- `check:effect-core-surface:red` runs the planted mutants and requires every
  intended failure.
- `check:effect-core-v1` builds the Lean project under `--wfail`, runs the
  axiom report, and runs surface checks plus the G3/G4 fixtures available at
  the slice's declared grade.
- `check:effect-core-v1:cutover` additionally requires every invariant-26
  counter zero and the generated `fullCutoverEligible` Boolean true under the
  frozen policy.
- root `gen` and `gen:ci` receive matching normal/`--force` entries; root
  `check` and `check:ci` receive matching check entries. `EnvLedger` must see
  the same sources/outputs/driver/gate relation as every existing emitter.

The generation task's declared sources must over-include the whole extractor,
frozen packet, schemas, `library/effects/package.json`, `bun.lock`, dedicated
`experiments/effect-core-surface/tsconfig.json`, provenance lock,
installed-package snapshot manifest, and the existing
`library/cas/Cas/Lang/{RefusalMap,Defun}.lean`,
`library/cas/Cas/Core/Admission.lean`, and
`library/cas/Cas/Backend/Mcp.lean` whenever CAS rows are projected. Its outputs
are exactly the files above. No task is accepted if it depends on ambient
`node_modules` bytes without first verifying them against the frozen lock and
source snapshot.

## 12. Closure versus proof completion

Package-surface structural closure is achieved when:

- the module, exposure, `SurfaceRowKey`, raw-type, and dependency sets are
  complete for the pin;
- every row has one conservative disposition, one primary carrier, and a
  nonempty family/bridge-role set;
- every row has exhaustive, disjoint admission profiles with profile-owned
  mappings, `A/E/R`, observations, transfers, and obligations;
- every primitive or registered foreign profile—and only those profiles—has
  exactly one direct handler ID;
- every boundary and pending obligation is explicit; and
- the structural census counters named in invariant 25 are zero.

This can be true while most `proofStatus` fields are `unstarted`. It licenses
only the statement “the rc.112 public package surface has one mechanically
complete row key per selected declaration/member/signature and every row has
populated schema-v1 structural dispositions, profiles, mappings, and pending
obligations.” It does not license “the semantic classifications are correct,”
“the classifier is sound,” “Effect is fully modeled,” “the generated code
preserves semantics,” or “the runtime conforms.”

Proof completion is per law and bridge. It requires kernel-checked theorems,
axiom reports, accepted-source judgments, conformance evidence, compiler
relations, and host assumptions. A later proof cannot retroactively promote a
different row or observation.

Proof-index readiness is separate from census closure: every profile and every
existing/proposed carrier has exactly one populated `TypeClosureRow`, while its
required edges may remain open. Per-type proof closure is stronger and
mechanically local: a profile or carrier closes only when every required edge
in its own row is discharged, all `justifiedAbsence` edges have checked
justification obligations, and its axiom summary is current. Full cutover is
stronger again: all invariant-26 counters are zero and
`fullCutoverEligible_iff` is kernel-checked while `fullCutoverEligible`
evaluates true. Thus `censusClosed = true` and `fullCutoverEligible = false` is
an expected state through the proof slices, not a contradiction.

## 13. Successive implementation slices

The order closes the universe early and raises proof grade without reopening
identity.

1. **Freeze.** Ratify `SurfaceRowKey`, `RawTsType`/`TypeExpr`, canonical IDs,
   row/profile schemas, seven conservative dispositions, carrier/family/bridge
   role IDs, `CarrierRegistryRow`, `TypeClosureRow` and edge vocabulary,
   `ClassProductDomainId` transfer registry, observation profiles, generated
   paths, command names, and the exact TS7 `@effect/tsgo` language-service
   route. Freeze the rule that CAS profiles reference the existing
   `Refusal.Clause`/`RefusalMap` only.
2. **S0 — source/module census.** Pin verification, recursive exports-map
   resolution, JS/DTS/source pairing, fresh imports, and the two known deep
   MultipartParser controls. No semantic inference.
3. **S1 — row/type/dependency census.** Build the disjoint row universe,
   type/value/namespace spaces, members, call/construct/index overloads,
   canonical aliases, `RawTsType` graph, `TypeExpr` elaboration decisions,
   signature digests, dependency closure, Effect reachability, and the
   well-typed non-effect complement.
4. **S2 — total structural classification.** Join every row to one
   conservative disposition, primary carrier, nonempty family/bridge roles,
   exhaustive profile set, profile-owned mapping and `A/E/R`, required handler
   ownership, observations, complete per-domain abstract-transfer IDs, and
   proof obligations. Generate one open `TypeClosureRow` for every profile and
   every existing/proposed carrier. All structural census counters close here;
   `fullCutoverEligible` remains false. No transfer or denotational soundness
   claim is made until its theorem is kernel-checked.
5. **S3 — sequential Core.** Success/failure/Cause/Exit, bind/gen expansions,
   folds/catches, and environment/service operations; direct denotation and
   reference handler; monad, branch, and index laws. Preserve CAS through
   fail-fast `admitCas` followed by `injectCas : CheckedPProg ->
   CheckedProgram casAER`; keep empty/dangling tables as red controls.
6. **S4 — Layer and resources.** LayerCore, scope/finalizers,
   acquire/release, environment provision, and their handler/lowering laws.
7. **S5 — fibers and nondeterministic flow.** scheduler-parameterized
   event-tree semantics, fork/join/interruption/yield, parallel zip/race,
   time, schedules, and randomness.
8. **S6 — stateful effects.** refs, deferreds, queues/pubsub, semaphores,
   requests/batching/caches, pools, and transaction calculus.
9. **S7 — Channel and remaining public domains.** ChannelCore,
   Stream/Sink/Pull/Take, Schema crossings, testing handlers, and all unstable
   subcalculi/registered foreign operations. Structural profile coverage was
   already closed in S2; this slice closes their semantic and classification
   transfer edges without changing the census.
10. **S8 — generator and G3.** Generate only the accepted closed TS fragment,
    run ordinary TypeScript and the pinned language-service quick-fix gates,
    parse back, and prove the admitted translation relation.
11. **S9 — G4.** Compare the reference handlers with the unmodified pinned
    Effect runtime under each named observation; retain counterexamples and
    bounds.
12. **S10 — G5/G6.** Pin compiler/configuration and Node host, state source and
    target semantics/assumptions, and discharge compilation/host bridge
    obligations at their honest grades.
13. **Cutover gate.** Regenerate the per-type closure ledger and axiom report;
    require every required profile/carrier edge discharged, every invariant-26
    counter zero, `censusClosed = true`, and `fullCutoverEligible = true`.
    This gate reports eligibility only; promotion/ratification remains a
    separate operator act.

## 14. G3–G6 bridge obligations for generated TypeScript

### G3 — admitted source extraction

**PROPOSED TERM — `RawTsTarget`.** The parse carrier is a closed target grammar,
not an open TypeScript AST wrapper:

```text
RawTsTarget = module TargetImport[] TargetTypeDecl[] TargetFunction[]
                     TargetConst[] TargetEntry
TargetImport = publicImport PublicSubpath ImportBinding[]
ImportBinding = censusSymbol SurfaceRowKey LocalId
TargetTypeDecl = alias TypeDeclId TypeBinderId[] TypeExpr
TargetFunction = function FunctionId Parameter[] TargetBlock
Parameter = parameter LocalId TypeExpr
TargetConst = constant LocalId TypeExpr TargetExpr
TargetBlock = statements TargetStmt[] TargetExpr
TargetStmt = let LocalId TargetExpr | evaluate TargetExpr
           | ifThenElse TargetExpr TargetBlock TargetBlock
           | switchVariant TargetExpr (NonEmpty TargetCase)
TargetExpr = value Value | local LocalId | record FieldExpr[] | tuple TargetExpr[]
           | variant VariantId TargetExpr[]
           | publicCall SurfaceRowKey ProfileId TargetExpr[]
           | callFunction FunctionId ArgMap
           | typeApply TargetExpr TypeExpr[]
FieldExpr = field FieldId TargetExpr
TargetCase = case VariantId LocalId[] TargetBlock
ArgMap = finiteMap ParameterId TargetExpr
TargetEntry = runProgram TargetExpr
```

- [ ] Require every public symbol/profile reference to resolve in the generated
  census and every `FunctionId` to resolve exactly once. There is no catch-all
  expression constructor, compiler-owned `TSNode`, process-local checker object,
  dynamic property name, `eval`, or host function value. Named target functions
  are code declarations with explicit parameters; they are not serializable
  closure values.
- [ ] Define closed `ParseDiagnostic` and `DecodeDiagnostic` grammars. They are
  extraction boundary diagnostics and cannot contain or alias CAS semantic
  `Refusal.Clause` values.
- [ ] Define the explicit pipeline
  `Bytes -> Either ParseDiagnostic RawTsTarget
  -> Either DecodeDiagnostic RawProgram
  -> check -> Either CheckDiagnostic (Sigma CheckedProgram)`.
- [ ] Define `AcceptedTs pins bytes target checked` only when parsing and
  structural decoding recover `target`, `check` produces `checked`, ordinary
  TypeScript and Effect-tsgo evidence uses the exact pins, and canonical
  rerendering agrees. Diagnostic silence alone cannot construct `ProgramWF`.
- [ ] Preserve `A`, `E`, and `R`, evaluation order, callbacks/code points,
  service provision, causes, scopes, and concurrency policies.
- [ ] Prove preservation/reflection against a formal semantics of that admitted
  source grammar; AST-to-data extraction alone is not G3.
- [ ] Require generate → independent TypeScript/language-service evidence →
  parse closed grammar → structural decode to `RawProgram` → check to the same
  `CheckedProgram` under the declared canonical relation.

### G4 — pinned Effect implementation conformance

- [ ] Map every reified primitive and registered-foreign direct handler to the
  selected public rc.112 APIs or explicit host boundary.
- [ ] Execute generated fixtures through public runtime eliminators and retain
  full raw `Exit`/event observations before normalization.
- [ ] Compare with an independent Lean/reference handler, not generator output
  interpreted by the same implementation twice.
- [ ] State domains, schedule/fuel/size bounds, host services, and observation
  quotients per family.
- [ ] For rc.112 `Cause`, compare only `runtimeReasonList` after
  `forgetCause`; do not claim stock-runtime G4 preservation/reflection of
  project `CauseTree.then` versus `CauseTree.both`.
- [ ] Language-service success is only a source-quality premise here.

### G5 — compilation preservation

- [ ] Pin TypeScript compiler, full config, standard libraries, module
  resolver, package lock, emitted JS, and source maps.
- [ ] Define the source and emitted-JS observations and the translation between
  them, or record a separately validated compiler bridge with its limits.
- [ ] Check that emitted imports and overload-selected calls still refer to the
  intended package and that tree-shaking/bundling does not change the accepted
  boundary.
- [ ] Relate generated source digest, emitted JS digest, and fixture/result
  digest in lineage data.

### G6 — hosted execution

- [ ] Pin the claim-target engine (`node@22.23.2` under the current root
  toolchain), OS/architecture, flags, module loader, clocks, timers, random
  source, filesystem/network contracts, and process environment.
- [ ] Name assumptions about microtasks, task dispatch, cancellation,
  finalizers, signals, and resource shutdown.
- [ ] Run host-specific fixtures for every admitted registered-foreign and
  primitive direct handler and retain raw observations separately from
  normalized ones.
- [ ] Do not transfer a Node result to Bun or a different host without a
  separate G6 row.

## 15. Freeze and acceptance checklist

Before checker implementation:

- [ ] The Effect Core v1 packet is marked frozen.
- [ ] `SurfaceRowKey`, the seven-value conservative disposition enum,
  `RawTsType`/`TypeExpr`, carrier/family/bridge-role IDs,
  `CarrierRegistryRow`, `TypeClosureRow`, `CutoverSummary`/cutover policy, and
  `ClassProductDomainId` are ratified.
- [ ] Canonical identity, row/profile schemas, elaboration diagnostics,
  type-closure edges, and profile coverage rules are frozen and versioned.
- [ ] Primitive/registered-foreign handler signatures, cause quotient, abstract
  transfer registry, and observation profiles are frozen.
- [ ] CAS refusal references are frozen as projections of the existing
  `Cas.Lang.Refusal.Clause`/`RefusalMap`; no replacement enum is admitted.
- [ ] `CasPProgAdmissible`, checked/partial CAS ingress signatures, the
  fail-fast `CheckDiagnostic` order, and the separate accumulated census report
  are frozen. No total all-`PProg` injection is present.
- [ ] The `@effect/tsgo` package/platform/TypeScript git-head relation is
  G0-resolved and tool-registered; the historical standalone repository is not
  an executable dependency.
- [ ] Generated paths and task names in §11 are accepted.

Before calling the public universe closed:

- [ ] S0–S2 gates pass from a clean checkout/install.
- [ ] The runtime census defect is repaired or explicitly joined as a known-red
  independent leg; the two deep public modules are present.
- [ ] The structural census counters in invariant 25 are zero; open proof edges
  in invariant 26 are reported but do not reopen the census.
- [ ] Every red control in §§8.5 and 10 is observed failing for the intended
  reason.
- [ ] The empty-table, dangling-answer, fail-fast-diagnostic, and
  accumulate-all-census controls fail for their intended distinct reasons.
- [ ] A second fresh run is byte-identical.
- [ ] The generated human projection is derived from the same ledger.

Before full cutover:

- [ ] Every surface admission profile and every existing/proposed carrier has
  exactly one `TypeClosureRow` and all joins resolve.
- [ ] Every required constructor/type-grammar, admission, semantics,
  ClassProduct-domain transfer, lowering, G3–G6 bridge, and red-control edge is
  discharged; every justified absence is proved; proof and axiom status is
  current under the frozen cutover policy.
- [ ] CAS profile closure rows discharge admission only for `CheckedPProg` (or
  successful `Option`/`Except` admission), and their run-agreement theorem uses
  that same domain.
- [ ] Every counter in invariant 26 is zero and the pending theorem
  `fullCutoverEligible_iff` is kernel-checked.
- [ ] `censusClosed = true`, `openTypeClosureEdges = 0`, and
  `fullCutoverEligible = true` in a fresh generated report. Any open required
  edge forces the last field to remain false.

Before any “fully reified” statement:

- [ ] Every admission profile's per-domain proof and bridge status is reported;
  “full” names the exact closed row universe, admitted profile domain,
  observations, and highest satisfied gate.
- [ ] Every primitive, expansion, subcalculus, registered foreign op, pure
  atom, and target adapter has its required laws/bridges at the claimed grade;
  refused/host-only profiles remain visible and are not counted as modeled.
- [ ] The axiom report and all pending assumptions are published with the
  claim.
