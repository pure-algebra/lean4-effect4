# Effect-native CAS replay library — implementation plan

Status: Pass-A implementation plan; M0 domain contract ratified by grilling,
2026-08-26. Vocabulary is owned by
[docs/effect-replay/CONTEXT.md](../../docs/effect-replay/CONTEXT.md)
Claim posture: planning input only; no model, specification, source-bridge, or
implementation-conformance claim is admitted by this document

## 1. Decision summary

The proposed first slice is a TypeScript library implemented with public Effect
v4 operations. It provides content-addressable storage and replay as Effect
services, and it can derive replaying adapters for explicitly described Effect
services. Lean 4 owns a small semantic model and establishes laws for that
model. TypeScript is the runtime implementation; Lean is never part of the
runtime.

The initial target is deliberately narrower than arbitrary Effect program
replay:

> For every admitted reified sequential model program whose replay-relevant
> leaf operations are mediated by the replay handler: given a
> request-compatible, outcome-admissible flat history, substitution replay
> consumes that history exactly, returns the recorded typed outcomes, and
> never selects live delegation; given any other history, it returns a typed
> rejection at the first divergence, consumes no occurrence beyond it, and
> still never selects live delegation.

That sentence is the ratified model-contract target (M0, 2026-08-26), not a
current claim. The TypeScript side has a deliberately weaker first boundary:
ordinary orchestration is conforming under a documented discipline rather than
admitted by a source checker. G2 traceability must retain that quantifier
mismatch. Exact declaration names and types remain Pass-B work; the minted
vocabulary lives in the owning context document.

For this slice, matching separates two checks with distinct rejection
categories. Request-side compatibility compares what the running program emits
against the next history entry: operation identity, revision, canonical
request payload, and order. Outcome-side admissibility is a condition on the
history itself: each recorded outcome must decode against its operation's
declared success or typed-failure Schema, checked when the entry is consumed.
The running program emits no outcome to compare; outcomes are what history
supplies. No program identity is modeled. Two different TypeScript programs
that emit the same admitted request stream are indistinguishable to this
replay protocol.

The architectural split is:

```text
project-owned operation descriptions
             |
             v
pure replay reducer <---------- Lean semantic model
             |                    and model theorems
             v
Effect replay service and service adapters
             |
             v
CAS store adapter / host runtime
```

CAS stores immutable object graphs. Replay interprets service operations using
those graphs. CAS does not itself decide whether a service body runs.

## 2. Authority and research basis

Canonical repository documents remain authoritative. Copies under
`research/docs/` are convenience snapshots only.

| Input | Role in this plan | Status |
| --- | --- | --- |
| [`effect-operational-semantics-reference-sweep.md`](../../docs/research/effect-operational-semantics-reference-sweep.md) | Separates model, source, compilation, and hosted-execution layers; supplies the restricted-semantics method | Research input |
| [`effect-runtime-ground-truth-extraction-scope.md`](../../docs/research/effect-runtime-ground-truth-extraction-scope.md) | Pins runtime facts and recommends an abstract typed environment for Context rather than copying its overlay/cache representation | G0 research input |
| [`cas-effect-program-replay.md`](research/cas-effect-program-replay.md) | Separates program identity, execution history, handler identity, checkpoints, and replay witnesses | Conception-mode research input |
| [`CLAIM-GATES.md`](../../docs/effect-typescript-semantics/CLAIM-GATES.md) | Governs G0–G6 wording and evidence | Canonical gate vocabulary |
| [`DEVELOPMENT-INVARIANTS.md`](../../docs/DEVELOPMENT-INVARIANTS.md) | Requires project-owned semantic types, explicit state, typed failures, and separate adapters | Canonical development law |
| [`sources.lock.json`](../../.reference/provenance/sources.lock.json) | Owns the Effect source identity | Effect commit `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, package `effect@4.0.0-rc.111` |
| [`MACHINE-ALGEBRA.md`](../machine/MACHINE-ALGEBRA.md) | Supplies the house canonicalization, framing, typed-reference, store-obligation, and hash-hypothesis patterns | Pre-grade design input; M0 must choose instantiation or a deliberate fork |
| [`CONFORMANCE-WORKFLOW.md`](CONFORMANCE-WORKFLOW.md) | Dual-lane development workflow: statement schemas, manifests, mutation metric, cycle state, lane roles | Ratified workflow authority, 2026-08-26 |
| [LLVM Content Addressable Storage guide](https://llvm.org/docs/ContentAddressableStorage.html#cas-library-implementation-guide) | Supplies the `data + references`, object-store, identifier, loaded-object, and action-index pattern | Architecture pattern only; exact source pin and license receipt pending |

### Prior-art disposition ledger

This ledger guides design; it does not admit new evidence into the Source Lock.

| Source | Revision | License status | Useful guarantee or pattern | Mismatch with this project | Disposition |
| --- | --- | --- | --- | --- | --- |
| Effect v4 source | `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, `effect@4.0.0-rc.111` | MIT | Public Effect, Context, Layer, Schema, Exit, and Cause implementation surface | Subject implementation, not Foldlab semantics | Adapt through a pinned public interface |
| Foldlab Effect semantics surveys | 2026-08-24 snapshots | CC BY 4.0 | Layered claim discipline and exact runtime inventory | Earlier recommended slices are broader than CAS replay | Adapt the method and selected Context/service facts |
| Foldlab CAS replay report | 2026-08-26 snapshot | CC BY 4.0 | Replay modes, history discipline, occurrence identity, negative cases | No ratified contract or implementation | Adapt into the first domain contract |
| Foldlab machine algebra | 2026-08-25 draft | CC BY 4.0 | Parameterized kind, framed pre-image, O1–O20 obligations, Level 0/1/2 hash discipline | Pre-grade and not yet selected as a dependency | Reuse or deliberately fork at M0 |
| LLVM CAS guide | live page inspected 2026-08-26 | Pending provenance receipt | Immutable data/reference DAG, interchangeable stores, and separate action index | Compiler-oriented object handles; no Effect service or replay semantics; action index has no first-slice consumer | Pattern only; index deferred to recomputation |
| Blaze checkout | commit `76cf4cb0e7d68fc71f17eed539b411b194c9ca38` | Pending Source Lock/license review | Handler, state, resource, and concurrency proof architecture | Rocq/Iris language, not Effect TypeScript | Pattern only, deferred |
| *A Relational Separation Logic for Effect Handlers* | DOI `10.1145/3776676` | Paper use only; catalog admission pending | Relational reasoning about handlers and state | No Foldlab judgment or TS bridge | Pattern only, deferred |

Before a G3 or stronger claim uses an Effect runtime file, the relevant file
identity must be added to the Source Lock. Before LLVM terminology or contracts
become normative, the exact documentation source must receive a provenance
receipt.

The effects library must not silently re-derive a second canonical-store
discipline. M0 decides whether its CAS node kinds instantiate the machine
algebra or copy only its obligation shapes while the machine remains pre-grade.
Either route adopts the machine's hash-hypothesis lattice:

- **Level 0:** no premise about the hash; canonicalization, pre-image framing,
  kind/version separation, deduplication by equal encoding, and collision
  behavior live here whenever possible;
- **Level 1:** address-to-content reflection requires an explicit named
  `hInj` premise; and
- **Level 2:** no theorem assumes collision resistance. Concrete collisions are
  characterized as implementation behavior instead.

## 3. Pending domain contract

Names in this section are minted in the Effect Replay context document; this
section is the design view and defers to it.

### Objects

- **Operation description:** stable operation identity and revision, request
  Schema, success Schema, typed-failure Schema, and leaf-replay admission.
- **CAS node:** versioned kind, canonical payload bytes, and ordered references
  to other nodes.
- **Content identifier:** digest of a project-owned, domain-separated pre-image
  with the provisional shape `versionByte ++ kindTag ++ frame(encode(canon
  node))`. Schema validates and interoperates at typed boundaries; its default
  JSON encoding is never the digest pre-image.
- **History entry:** one logical operation occurrence, retaining request,
  decision, outcome, and predecessor information.
- **Replay session:** mode, execution identity, history root, current
  flat-history cursor, ordered decision trace, and terminal abort state. A
  record-mode append failure aborts the session through the transport seam:
  orchestration cannot catch it, no later wrapped operation runs, and it
  surfaces as the session's typed store error — histories are truthful
  prefixes, never gapped subsequences, structurally.
- **Service adapter:** an implementation of an existing Effect service
  interface that delegates each described operation through the replay
  service.
- **Session outcome:** tagged result of a session: `Completed` with the
  terminal; `Rejected` with category, position, and — for the
  unconsumed-suffix case only — the program's terminal so far; or `Violated`
  with the ambient-service violation.
- **Replay witness:** immutable account of the mode, execution identity,
  consumed history, decision trace, and session outcome. It carries execution
  identity and never program identity.

### Operations

- store and load a canonical CAS node;
- begin a record or replay session;
- invoke a described leaf operation;
- append a record-mode occurrence;
- consume one replay-mode occurrence;
- finish a session only when its terminal conditions hold; and
- wrap an explicitly described Effect service implementation with the same
  caller-facing service interface.

### Initial observations

The primary observation is an ordered decision trace emitted by the pure
reducer. Its working decision cases must distinguish at least live delegation,
record-mode occurrence append, recorded substitution, history consumption,
typed rejection, and completion. Whether a live leaf adapter was requested is
a derived projection of that trace, not a separate Boolean oracle.

The remaining observations are:

- typed terminal result: success or admitted typed failure;
- ordered operation occurrences;
- consumed history prefix and final cursor;
- first mismatch and its stable rejection category; and
- CAS roots and referenced node identities.

Allocation, wall-clock cost, tracing, Effect's internal Context representation,
layer memoization, and runtime primitive steps are not initial observations.

### Mismatch taxonomy

Eight ratified categories. Request-side, checked against the entry at the
cursor: operation mismatch, revision mismatch, request mismatch, and history
exhausted. Completion-side: unconsumed suffix. Outcome-side, checked at
consumption: outcome inadmissible. Protocol-side, checked in record mode
against the outstanding delegation: delegation outstanding, when an invocation
arrives while one is already in flight, and unsolicited outcome, when a
recorded outcome arrives with no delegation outstanding or beside a different
one. "Order mismatch" is deliberately not a category — under exact positional
matching it always manifests as a request-side case at the current position.
CAS storage failures are a distinct typed error family, never mismatch
categories; ambient-service violations are a distinct session-outcome case.

### Initial equalities and distinctions

- CAS nodes are equal when their admitted canonical representations are equal;
- equal admitted canonical pre-images yield equal identifiers at Level 0;
- identifier equality reflects pre-image equality only under explicit Level-1
  `hInj`;
- histories are not equal merely because their final outcomes are equal;
- repeated identical requests remain distinct logical occurrences;
- handler/environment identity and execution identity remain separate;
- program identity is absent rather than inferred from request history;
- transparent orchestration and substituted leaf operations have different
  roles in one flat trace; and
- implementation observations are related to model observations only through
  a named normalization and comparison relation.

### Environment and scope

Initial scope:

- one fiber and a finite sequential history;
- finite, Schema-encoded requests, successes, and typed failures;
- explicit operation descriptions;
- transparent orchestration code whose leaf dependencies are wrapped;
- substitution at leaf operations only;
- exact positional matching and no implicit live fallback;
- an in-memory CAS adapter first;
- a small manually mirrored TypeScript reducer kept suitable for line-by-line
  audit; and
- public Effect imports only.

Conforming orchestration must not perform ambient host effects or consult
Effect-provided default services such as Clock or Random except through a
described leaf operation. `R = never` is not treated as evidence of purity.
The ratified policy is reject-first: time, randomness, and jittered scheduling
are rejected from conforming examples; replay-mode sessions install tripwire
Clock/Random defaults that surface ambient use as a `Violated` session outcome;
deterministic overrides are deferred until a fixture demands one. The raw-host
channel (`Date.now`) remains discipline plus permanent counterexample fixtures.
The tripwire mechanism is verified against the pinned source (2026-08-26):
`Clock.Clock` and `Random.Random` are `Context.Reference` keys overridable per
scope with `Effect.provideService`; `Effect.sleep` routes through the clock
service, and `Schedule.jittered` draws through the random reference.

Deferred:

- arbitrary JavaScript or arbitrary `Effect` value ingestion;
- a TypeScript source checker for orchestration admission;
- defects, interruption, full Cause combination, Scope, and finalizers;
- concurrency, races, scheduler observations, and causal-DAG replay;
- retry and exactly-once external behavior;
- ActionIndex and recomputation/cache mode;
- framed histories and opaque substitution of an outer orchestration service;
- checkpoints, history collection, migration, and remote replication;
- ambient `Date.now`, `Math.random`, network, filesystem, mutable globals, or
  other host operations outside a described service operation;
- transparent validation of destructive operations; and
- TypeScript compiler or JavaScript-engine relation claims.

### Positive, negative, boundary, and overclaim cases

Positive witness:

1. An orchestration service calls two described leaf services in sequence.
2. Record mode invokes both live adapters and stores typed outcomes.
3. Replay mode runs the orchestration again, substitutes both outcomes in the
   recorded order, consumes the complete history, and invokes neither live
   leaf adapter.

Required negative witness:

- the second replay request differs by operation revision or canonical request
  payload; replay returns the first typed mismatch and performs no live
  fallback.

Boundary cases:

- two byte-identical requests occur consecutively and remain two occurrences;
- two different TypeScript programs emit the same admitted request stream and
  are indistinguishable to the first-slice replay protocol;
- a changed program consumes an old history until its first request divergence;
- history contains an extra entry after the program terminates;
- stored bytes decode but are non-canonical or use an unknown node kind; and
- the live operation succeeds but history persistence fails afterward.

Counterexample to the strongest tempting overclaim:

> A program calls `Date.now()` directly, consults a default Clock/Random
> service, or uses a jittered retry schedule between two replayed service
> calls. Its service history can match exactly while its whole-program result
> changes.

Therefore the first result is a service-protocol theorem, not a theorem about
arbitrary Effect programs.

### Assumptions, facts to prove, and deployment evidence

| Class | Initial contents |
| --- | --- |
| Assumptions | Project-owned deterministic canonical byte codec; explicit `hInj` only for Level-1 address reflection; described orchestration performs no ambient host effect and consults no default Clock/Random service except through described operations; live adapters obey their declared request/result Schemas |
| Lean facts to establish | Replay determinism; fail-closed mismatch; exact consumption; replay traces never select live delegation; occurrence distinctness; CAS graph well-formedness; interpreter composition laws |
| G2 traceability limitation | Lean quantifies over reified admitted programs; ordinary TypeScript orchestration is discipline-conforming until a source judgment exists |
| TypeScript facts to test | Schema decoding/encoding behavior; Effect service/layer wiring; replay construction without a live dependency; adapter delegation; decision-trace agreement on fixtures; store corruption/error handling; package public imports |
| Deployment facts to monitor later | Filesystem atomicity; process crash windows; remote availability; host runtime/compiler versions; digest implementation behavior; secret handling |

## 4. Effect surface decision

The existing runtime surveys cover more of Effect than this slice requires.
The plan uses them to select an abstraction rather than reproduce the runtime.

| Effect surface | First-slice use | Lean treatment | Deferred risk |
| --- | --- | --- | --- |
| `Effect` sequencing | Compose orchestration and adapter calls | Small reified `return`/`call`/`bind` program or an explicitly selected handler algebra | Arbitrary callbacks and runtime primitives |
| `Context.Service` | Public CAS, replay, and wrapped-service interfaces | Abstract finite environment of typed handlers | String-key collisions, References, runtime overlay/cache layout |
| `Layer` | Construct and substitute in-memory/live/replay adapters | Not modeled initially; layer wiring receives integration tests | Memoization, scope, dynamic layer replacement |
| `Schema` | Validate durable node, operation, request, outcome, error, and witness representations | Project-owned value relations and codec obligations; no digest-byte authority | Full SchemaAST and effectful transformations |
| `Exit` / `Cause` | Retain success versus admitted typed failure | Initial two-case outcome with a later embedding into richer causes | Defects, interruption, annotations, finalizer failures |
| `Ref` or `SynchronizedRef` | Possible implementation carrier for session state | Explicit immutable replay state and transition function | Concurrency and atomic multi-step updates |
| `Clock`, `Random`, `Schedule` | Rejected in conforming orchestration; replay-mode tripwire defaults surface ambient use | Absent from the first model | Default services and jitter bypass the visible `R` requirements |
| `Crypto` or platform digest | Concrete digest adapter | Abstract address function with Level-0 laws and explicit Level-1 `hInj` | Concrete algorithm, collisions, and host/FFI behavior |
| `Scope`, `Fiber`, `Scheduler` | Excluded | Absent | Resources, cancellation, nondeterminism |
| `unstable/eventlog`, `unstable/persistence`, `unstable/workflow` | Prior-art inspection only | No semantic authority | Version-sensitive dependency and mismatched workflow contract |

The runtime report's T3 recommendation is adopted narrowly: service lookup is
modeled as an abstract typed map. Context overlays, cache roots, and fiber cache
refresh are implementation facts relevant only if a later conformance claim
observes them.

## 5. Module architecture

Each module should expose one small interface and hide representation,
normalization, and adapter complexity behind it.

```text
Operation description ----+
                           |
CAS node/codec --------+   |
                       v   v
                  Replay reducer
                       |
          +------------+-------------+
          |                          |
      Replay service           model fixtures
          |
    wrapped service adapter
          |
       user program

CAS store <----- replay service
```

### Candidate TypeScript modules

Names remain provisional until the domain contract is ratified.

| Module | Interface responsibility | Hidden implementation |
| --- | --- | --- |
| Operation | Define a replayable operation and its Schemas/admission class | Type inference helpers, revision validation, canonical request encoding |
| CAS node | Validate, encode, and identify immutable `data + references` nodes | Canonical field order, domain separation, digest input construction |
| CAS store | Store and retrieve nodes by identifier | In-memory map first; filesystem/remote adapters later |
| Decision | Define the reducer's decision cases and normalized trace | Case constructors, trace encoding, and derived projections such as live invocation |
| Replay reducer | Pure transition from state and request to decision, result, and new state | Flat cursor, decision trace, mismatch, and exact-consumption rules |
| Replay service | Expose reducer-driven operations in Effect and own a session | `Ref`/state carrier, store calls, Schema errors |
| Service adapter | Kit constructor producing the live role tag plus record/replay constructions for one described service | Method interception, operation-to-method routing, runtime wrap brand |
| Witness | Finalize and encode replay evidence | Root assembly and observation normalization |

### Public interface constraints

- A pre-existing service can be wrapped only with explicit method/operation
  descriptions; TypeScript reflection is insufficient.
- One kit constructor per described service mints an internal live role tag
  and returns the record and replay constructions; a by-value overload builds
  on it. Wrapper bodies never resolve the public tag — a named defect with a
  must-fail fixture.
- Wrapped services carry a runtime string-keyed brand checked at construction;
  double wrapping is rejected with a typed error, never normalized. Type-level
  brands are ruled out by caller-facing type identity.
- The replay-mode adapter constructor must not require or receive the live
  service. Its Effect environment contains replay dependencies only. Record
  construction receives the live service separately. Capturing a live reference
  before replay construction is a named residual risk and a rejected design.
- The caller-facing service method types should not expose CAS internals.
- CAS storage failures and replay mismatches remain distinct typed errors.
- Replay rejections, violations, and record-mode append failures travel from
  wrapped methods to the session boundary through a named defect-class
  transport seam; caller-facing method types stay byte-identical across
  live, record, and replay modes.
- Digest pre-images come only from the project-owned framed canonical encoder;
  Schema's default JSON encoding is never hashed.
- Layer constructors accept dependencies; they do not create hidden global
  stores or host capabilities.

### Proposed repository shape

Use one mixed-language project until independent release lifecycles justify a
workspace split:

```text
library/effects/
  IMPLEMENTATION-PLAN.md
  CONFORMANCE-WORKFLOW.md
  README.md
  package.json                 # added at implementation milestone M1
  bun.lock                     # exact versions, added with package.json
  tsconfig.json
  src/
    Operation.ts
    CasNode.ts
    CasStore.ts
    Decision.ts
    ReplayReducer.ts
    Replay.ts
    ServiceAdapter.ts
    Witness.ts
    index.ts
  test/
    CasNode.test.ts
    ReplayReducer.test.ts
    ReplayService.test.ts
    ServiceComposition.test.ts
    ModelFixtures.test.ts
  Effects.lean
  Effects/
    Value.lean
    Cas.lean
    Signature.lean
    Program.lean
    History.lean
    Replay.lean
    Interpreter.lean
    Laws.lean
    Fixtures.lean
  research/
```

M1 resolutions: the package is `@foldlab/effect-replay` (private), exports
flow through `src/index.ts`, the compiler is the admitted `typescript@5.9.2`
with `@effect/tsgo` deferred until its native port stabilizes (adoption is a
re-admission event per the tool register's version-drift rule), and the
Effect dependency is exact `effect@4.0.0-rc.111`, whose manifest names the
pinned provenance revision it targets. The test harness is vitest with
`@effect/vitest`, both exact-pinned — the `@effect/vitest` version equals
the pinned effect rc, from the same monorepo commit. Source and test trees
typecheck under separate configurations, both strict.

## 6. Lean semantic plan

### Chosen semantic level

Model a project-owned, sequential, first-order operation language and replay
machine. Do not model raw Effect objects, Context overlays, Layer construction,
JavaScript closures, or a JavaScript heap.

The minimum useful model has:

- a typed operation signature family;
- a free sequential program or another explicitly selected reified handler
  syntax;
- explicit handlers/environments;
- canonical CAS nodes and references;
- histories with distinct logical occurrences;
- record and replay modes;
- a total pure reducer returning decisions and new state;
- a derived transition relation with an agreement obligation; and
- an interpreter that threads replay state through program composition.

The TypeScript reducer is a manual mirror for the first slice. It must remain
small enough for line-by-line review, with complexity represented as explicit
decision data rather than hidden control flow. Lean-to-TypeScript generation is
a later extraction lane, not an M1–M6 dependency.

### Dependency-ordered declaration DAG

Exact names and types are pending Pass B.

```text
Value / canonical bytes
  |
  +--> node kinds / references / raw nodes
  |       |
  |       +--> node well-formedness / canonical encoding / abstract address
  |
  +--> operation signature
          |
          +--> request / typed outcome / operation policy
          |       |
          |       +--> invocation / history entry / occurrence identity
          |                    |
          |                    +--> history well-formedness / flat cursor
          |
          +--> sequential program / handler environment
                               |
                               +--> direct interpreter

mode / replay state / decision / mismatch
          |
          +--> reducer step / multi-step run / terminal witness
                               |
                               +--> replaying handler transformer
                                             |
                                             +--> program replay interpreter
                                                           |
                                                           +--> laws and fixtures
```

### Provisional theorem inventory

The names below are planning handles, not frozen declarations.

CAS and codec:

- canonical encoding is deterministic;
- decoding canonical bytes round-trips admitted nodes;
- normalization is idempotent;
- every stored reference of a well-formed graph resolves within the declared
  closure;
- storing the same admitted node yields the same abstract address at Level 0;
- pre-image kind/version separation and equal-encoding deduplication require no
  hash premise;
- address equality reflects admitted node equality only with explicit
  `hInj : Injective H`; and
- concrete collisions are characterized rather than excluded by a theorem.

Replay state:

- pending well-formedness obligation: every reducer step from an admitted
  state produces an admitted state/history pair;
- substitution replay is deterministic;
- the reducer's decision stream is deterministic for a fixed admitted input;
- a matching request consumes exactly one permitted occurrence;
- a mismatch consumes no later occurrence and produces a typed rejection;
- replay-mode traces never select the live-delegation decision;
- successful complete replay consumes exactly the declared history;
- record mode extends history by one occurrence while leaving its prefix
  unchanged;
- identical invocation content does not collapse distinct occurrences;
- an append-failed record session admits no further occurrences, and its
  history is a prefix of the record-mode trace; and
- terminal histories reject ordinary appended entries.

Composition:

- interpretation respects `return` and sequential `bind` across both outcome
  cases (success and typed failure);
- wrapping a handler commutes with sequential program interpretation under
  explicit state threading;
- extending the environment with an unrelated service leaves existing
  observations unchanged;
- transparent orchestration retains the declared ordered observations of
  wrapped leaf calls;
- double wrapping is rejected or normalized according to one ratified policy.

Framed child histories and opaque substitution of an outer orchestration
service are deferred to the M7 extension list and are not part of the M3–M5
theorem inventory.

The machine/direct agreement theorem for this slice should compare the reified
program interpreter with the reducer-driven interpreter, not with arbitrary
JavaScript execution.

### Representation questions for Pass B

1. Are operation signatures intrinsic indexed families or raw descriptions
   checked into an indexed representation?
2. Is occurrence identity structural `(execution, index)` data, a node address,
   or a separate nonce?
3. Which exact framing and scalar encodings instantiate the project-owned
   canonical digest pre-image?
4. Which parts of Schema encoding are modeled directly and which are external
   checked translations?
5. Do the effects CAS kinds instantiate the pre-grade machine algebra directly,
   or discharge a deliberately forked copy of its obligation shapes?
6. If the opaque extension is admitted at M7, does an opaque outer occurrence
   retain one child-root reference or an exact start/end interval?

## 7. Obligation ledger

IDs are provisional planning identifiers.

| ID | Obligation | Evidence target | Negative/falsification case | Trust boundary |
| --- | --- | --- | --- | --- |
| `CAS-001` | Project-owned canonical node encoding has one byte representation per admitted node | Lean model theorem plus Schema boundary fixtures | same node encodes differently by property order or Effect version | codec implementation |
| `CAS-002` | Graph admission rejects dangling or wrong-kind references | Lean theorem and TS negative tests | missing referenced node loads successfully | store adapter |
| `CAS-003` | Every address law is assigned to hash Level 0 or carries explicit Level-1 `hInj`; no theorem occupies Level 2 | theorem signatures and docs review | collision resistance appears as an axiom or unnamed premise | concrete digest |
| `CAS-004` | A value's canonical encoding is the UTF-8 bytes of its compact JSON rendering — codepoint-sorted keys, integers only, JSON short-escape strings — one encoding per structure, language-neutral | model-executed encoding vectors consumed by the value projection | a second writer formats the same value differently and splits its content identity | value projection canonical JSON |
| `RPL-001` | Replay is deterministic for fixed admitted state/request | Lean theorem | two permitted decisions from one state | none beyond model |
| `RPL-002` | Replay-mode decision traces never select live delegation, and replay construction has no live-service requirement | Lean theorem at M3; layer typecheck and controlled TS fake at M4 | live dependency appears in replay construction or live counter increments | service adapter/runtime |
| `RPL-003` | Matching consumes exactly the permitted occurrence | Lean theorem and fixtures | skip, duplicate, or reuse one occurrence | reducer mirror |
| `RPL-004` | Mismatch fails closed | Lean theorem and integration test | missing entry falls back to live adapter | adapter wiring |
| `RPL-005` | Completion rejects unconsumed suffix entries; the rejection carries the program's terminal so far | Lean theorem and fixture | same final value hides an extra history call | observation normalizer |
| `SES-001` | Record-mode append failure aborts the session through the transport seam; histories are truthful prefixes, never gapped subsequences | Lean record-mode theorem and fault-injection integration test | a caught store error lets later appends continue | transport seam and session state |
| `SES-002` | Every reducer step preserves session-state well-formedness | Lean WF-PRESERVE instance | a step drives the cursor outside the history or breaks the record-mode cursor pin | none beyond model |
| `SES-003` | Record-mode delegation is exclusive and outcome-solicited; unsolicited steps fail closed and lawful record runs append in invocation order | Lean FAIL-CLOSED instance, protocol vectors, and session-layer refusal tests | interleaved live calls record completion order, or a cross-wired outcome appends under the wrong invocation | session cell and reducer mirror |
| `CMP-001` | Sequential interpretation threads replay state compositionally across success and typed-failure outcomes | Lean bind/interpreter law over both cases | nested call resets or forks the cursor | session state carrier |
| `CMP-002` | Identical requests remain separate occurrences | Lean theorem and repeated-call fixture | CAS deduplication shortens history | CAS storage versus history seam |
| `CMP-003` | Deferred to M7: transparent and opaque policies have distinct, declared framed traces | two semantic rules and tests, when admitted | outer substitution silently leaves child cursor inconsistent | policy adapter |
| `CTX-001` | Wrapped service construction supplies the same caller-facing interface without recursive lookup | TypeScript typecheck and layer integration tests | wrapper resolves itself as its live dependency | Context/Layer wiring |
| `CTX-002` | Conforming orchestration cannot consult default Clock/Random behavior; replay-mode tripwires surface ambient use as a `Violated` outcome | conformance rule, tripwire defaults, and negative integration fixtures | jittered retry or default time/random changes the trace | Effect default services |
| `ADM-001` | G2 traceability distinguishes reified Lean-program quantification from discipline-conforming TypeScript orchestration | contract review and claim matrix | model theorem is presented as universal over ordinary TS programs | source-admission boundary |
| `BRG-001` | Model fixtures and TS reducer compare one declared normalized decision trace | generated manifest and differential suite | comparator drops live-delegation or mismatch decisions | manual reducer mirror |
| `BRG-002` | Pinned Effect integration agrees on the enumerated domain | reproducible G4 observations | runtime/version/config drift | compiler, bun/node, Effect runtime |
| `DUR-001` | No exactly-once claim crosses the live-action/history-append crash gap | contract review and fault test | external action succeeds, append fails | external system and persistence |
| `PRJ-001` | Value-descriptor identity is explicit and checked: kind tag and revision are declared, and reading verifies the expected root kind | TypeScript typecheck and fixtures | a root of another kind decodes silently | CAS store |
| `PRJ-002` | A value round-trips through its descriptor: get after put returns the declared domain canonicalization | TypeScript round-trip fixtures; Lean CODEC lift deferred until the declared encoding is modeled | a lossy or renormalizing read | declared canonical value encoding |
| `PRJ-003` | A payload failing the descriptor's schema is rejected with a typed projection error distinct from the CAS error family and the mismatch taxonomy | TypeScript fixtures | a decode failure surfaced as StoreFailure or swallowed | projection codec failure taxonomy |
| `PRJ-004` | Fixed-root hydration matches by-value construction: the layer builds the same caller-facing shape, construction errors stay on the layer, and method error unions never widen | TypeScript typecheck and integration fixtures | hydration widens a method error union or hides a construction failure | service kit and CAS store |
| `PRJ-005` | Hydrated record construction stays non-recursive and single-wrapped: layerAs targets the internal live role only, never resolves the public wrapper, and double wrapping stays rejected | must-fail TypeScript fixtures | the wrapper resolves its public tag or accepts a wrapped live role | service kit |
| `PRJ-006` | Equal roots imply no stronger value equality than the hash-hypothesis lattice permits | standing review rule | prose or API implying content equality from address equality | hash-hypothesis lattice |
| `RMT-001` | No remote-loaded node reaches the cache or the caller without passing standard admission; a wire-supplied digest is a routing hint, never an identity | Lean TRACE-EXCLUDES instance and TS fixtures | a node cached or returned before admission | remote client machine |
| `RMT-002` | Declared sizes and counts are checked against declared budgets before any hashing or decoding | Lean FAIL-CLOSED instance (no verification or admission decision past budget) and R2 TypeScript streaming-budget fixtures (declared oversize prevents body consumption; a byte counter stops underreported or chunked bodies) | an oversized declaration reaches hashing or decoding | exchange-alphabet budgets; key-count budget at R3 |
| `RMT-003` | An integrity failure is terminal for those bytes: no wire attempt ever repeats unchanged content | Lean TRACE-EXCLUDES instance | a retry decision with unchanged bytes after integrity rejection | remote client machine |
| `RMT-004` | An already-present exact-digest upload resolves as success with zero additional transfer commands | Lean EXACT-STEP instance | a duplicate upload emits a transfer command | find-missing negotiation |
| `RMT-005` | No admission or publication decision is taken on a presence answer alone, and absence is never negatively cached by default | Lean TRACE-EXCLUDES instance | presence alone admits, publishes, or writes a negative cache | presence semantics |
| `RMT-006` | A batch response accounts for every requested key per-key; an unaccounted or misaligned key fails the batch closed with no cross-key substitution | Lean FAIL-CLOSED instance | a misaligned batch partially succeeds or substitutes across keys | batch protocol |
| `RMT-007` | Children upload before parents and the root publishes last; server acceptance of a parent never implies closure | Lean TRACE-EXCLUDES instance | a root-publish command precedes a child's confirmed upload | upload ordering |
| `RMT-008` | At any declared interruption point, no partial node is admitted, no root is published, and resources are closed | Lean FAIL-CLOSED instance over scheduled interruptions | an interruption leaves a partial admit or a published root | fault schedule |
| `RMT-009` | Interrupted transfers resume only from a re-queried, server-reported committed offset, tolerating regression | Lean FAIL-CLOSED instance | a resume from a locally remembered offset | resume protocol |
| `RMT-010` | Retries are bounded by declared policy, rendered as decisions, and never repeat a non-idempotent wire attempt | Lean TRACE-EXCLUDES instance | an unbounded or non-idempotent retry | retry policy |
| `RMT-011` | Server-declared limits are discovered at layer acquisition and honored by splitting or rerouting | TypeScript typecheck and fixtures | a hardcoded limit exceeds a declared capability | capability probe |
| `RMT-012` | Verification and credential scope are independent of transport origin; credentials never cross redirect hosts | TypeScript fixtures | a credential follows a redirect or verification depends on origin | transport shell |
| `RMT-013` | Presence-style operations carry a namespace; no global existence query exists on the surface | standing review rule | a global does-this-digest-exist call | API review |
| `RMT-014` | Batch framing, capability documents, and presence indexes parse fail-closed with the same posture as node bytes | Lean FAIL-CLOSED instance and TS fixtures | malformed control state partially applied | control-state codecs |
| `RMT-015` | A successful remote load implements the logical admitted-node load | Lean AGREEMENT instance | a remote load succeeding with a node the logical load would not produce | AGREEMENT family |
| `RMT-016` | A local admitted-node hit is observationally equivalent to a successful remote load for immutable nodes | Lean AGREEMENT instance | a cache hit observably diverging from the remote answer | cache discipline |
| `RMT-017` | Attested presence confirms for publish: a key the peer reports present whose bytes the client holds and verifies locally enters the confirmed set; without the presence report or the local verification the attestation is refused, and attestation never admits to the cache | Lean FAIL-CLOSED instance and attestation schedule vectors | a presence claim alone confirming publication, or attestation admitting to the read cache | machine confirmation rule |
| `SRV-001` | The server's semantic core is the interpretation of the model's finite request trees over the storage seam: for every scripted session, the implementation returns the model's outcomes and issues exactly the model's storage events, in order | model-executed session vectors (outcomes and reified transcript from one run of the model server) | a skipped admission check, an extra or reordered storage event, or an outcome the tree does not produce | server tree denotation |
| `MRK-001` | One chunk-tree root per declared recipe and content: chunking is a lossless declared partition, and the root is a function of the recipe parameters and the bytes | Lean CODEC instance (rejoining chunks restores the bytes; chunking injective) | a recipe inferred from data, or a lossy rechunk minting a second root | declared chunking recipe |
| `MRK-002` | The streaming decoder emits a chunk only after it verifies against its expected subtree address; against a committed chunk list, every emission matches, or a hash-collision witness exists in the consumed prefix — the decoder is not obliged to detect the collision | Lean TRACE-EXCLUDES instance plus the named soundness-with-witness theorem | an unverified chunk emitted, or a mismatched emission with no extractable collision | verified-streaming decoder |
| `MRK-003` | No decoder run observes the length or end-of-input before the final chunk validates against the root | Lean TRACE-EXCLUDES instance (temporal over the run) | a truncated or length-tweaked run exposing length before final-chunk validation | verified-streaming decoder |
| `MRK-004` | A complete decode determines its root: the recomputed root of the emitted output equals the expected root, so no output completely decodes under two roots | Lean carrier theorem over the decoder run | one output accepted to completion under two distinct roots | verified-streaming decoder |
| `MRK-005` | Slice decoding agrees with the whole decode restricted to the requested range | Lean AGREEMENT instance (relational) | a slice emitting bytes the whole decode would not emit at those offsets | slice extractor and decoder |
| `MRK-006` | The inclusion verifier accepts exactly the openings whose recomputed root matches; honestly generated paths verify; and two accepted openings of one root and index with different leaves yield a computable collision | Lean reflection iff, completeness theorem, and binding extraction | acceptance without matching recomputation, or binding violated with no extracted collision | inclusion verifier |
| `MRK-007` | The consistency verifier accepts exactly the related root pairs, and consistency forces prefix agreement or exhibits a collision | Lean reflection iff and prefix-agreement corollary (second Merkle slice) | consistent roots whose committed prefixes diverge with no extracted collision | consistency verifier |
| `MRK-008` | The decoder is a pure fold: runs compose over input concatenation, so transport fragmentation below the parser cannot change any emission, rejection, or terminal | Lean carrier theorem (run composition) now; TypeScript rechunk-equivalence fixtures at the implementation slice | a run whose outcome depends on input grouping | verified-streaming decoder |
| `MRK-009` | Slice and encoding bytes are transport, never identity: only roots and decoded bytes are identity-bearing, and encoding malleability is documented rather than fought | standing review rule; negative fixtures at the implementation slice | an API comparing encodings byte-for-byte or minting identity from a slice or proof carrier | API review |
| `MRK-010` | An accepted opening binds its index's committed chunk: bytes accepted at an index equal the chunk the tree commits at that index, or a collision is exhibited — so a proof replayed at another index can never make a position serve bytes its leaf does not hold (position binding; the target the informal source admits it lacks; note a chunk legitimately stored at two indices verifies at both) | Lean binding extraction theorem composed from per-index binding and completeness | an accepted cross-index replay serving foreign bytes with no extractable collision | inclusion verifier |
| `MRK-011` | Inclusion-opening documents parse fail-closed and exactly: sides are never encoded, truncation and malformed fields are rejected, and a successful decode's input is exactly the canonical encoding of its result | Lean CODEC instance over the bounded opening carrier | a non-canonical opening document decoding | proof-document codec |
| `MRK-012` | Range-stream documents parse fail-closed and exactly over the decoder's input alphabet: unknown tags and truncated items are rejected, and a successful decode's input is exactly the canonical encoding of its result | Lean CODEC instance over the bounded stream carrier | a malformed stream byte string decoding as items | proof-document codec |
| `MRK-013` | Ranged stream generation is complete: for any requested range the honest extractor's stream decodes to its done status and emits exactly the owed ranged emissions | Lean carrier theorem (ranged generation completeness) | an in-range request whose generated stream rejects or under-emits | range extractor |
| `MRK-014` | The Merkle address function instantiated as the address of the canonical blob-node encoding makes a blob root an ordinary content identifier, and a bounded pre-image collision transfers to a byte-level hash collision | Lean carrier theorems (root-address tie; collision transfer) | a blob root that is not the address of its materialized root node | blob node graph |
| `MRK-015` | Byte-level frame parsing is incremental and fragmentation-invariant: all fragmentations of one complete body yield the same parsed inputs and terminal, and truncation never yields completion | Lean incremental-parser carrier theorems; TypeScript channel-framer fixtures | a parse outcome depending on fragment boundaries, or a truncated body completing | incremental frame parser |
| `MRK-016` | Every input trace accepted for a root and range emits exactly the committed bytes at those positions or supplies a collision witness; honest-generator completeness is a separate theorem | Lean carrier theorem (adversarial ranged binding) | an accepted hostile trace emitting foreign bytes with no extractable collision | ranged decoder |
| `MRK-017` | Successful byte-range slicing equals the flattened whole restricted to the requested byte window under the declared bounds | Lean carrier theorem over the byte-slice planner | a byte slice emitting bytes outside the window or disagreeing with the whole | byte-slice planner |
| `MRK-018` | A blob manifest commits recipe identity, total bytes, and leaf count; readers select semantics from the recipe id and unknown ids fail closed; changing any identity-affecting recipe parameter changes the manifest id | Lean manifest model and CODEC rows | a reader guessing semantics for an unknown recipe, or totals trusted from an unauthenticated channel | blob manifest |
| `MRK-019` | A proof response is exactly one complete decode: trailing content after the machine's done status is rejected at the framer, and responses are bounded by declared output and proof-amplification budgets | Lean framer-closure carrier theorem and budget rows | trailing frames absorbed after completion, or a tiny range licensing unbounded proof bytes | response framer |
| `MRK-020` | A ranged blob read touches exactly the proof-necessary nodes: the manifest, the parents on intersecting paths, the intersecting leaves, and their chunk data — never a node outside the range's spine | model-executed access-set vectors consumed by a load-counting store | a linear walk loads the whole tree for a one-chunk slice, or a reader skips a boundary leaf | blob read planner |
| `SRV-001` | A successful root-head transition implies the manifest and selected closure were admitted at that transition under its compare-and-set precondition, and no failed transition changes the visible head; crash survival is a distinct adapter property | Lean server transition model | a visible head whose closure was never admitted, or a failed publish mutating the head | server machine |
| `SRV-002` | Server admission runs bounded receive, closed decode, address recomputation, and reference checks before write-if-absent, and loads revalidate bytes before crossing the semantic seam | Lean server model; adapter contract suite | bytes stored or served without recomputation | admission pipeline |
| `SRV-003` | Write-if-absent distinguishes stored, already-present-identical, and same-address-different-bytes; the third is an integrity fault that fails, is observable, and blocks publication | adapter contract suite over the declared outcomes | a corrupt resident silently reported as already present | object-store contract |
| `SRV-004` | Served capabilities are the intersection of implementation, principal policy, store properties, registry properties, and configured limits; a served capability never exceeds an enforced one | Lean derivation model; fixtures | a served capability the backend cannot honor | capability derivation |
| `SRV-005` | Adapters declare a durability class and success claims never exceed the declaration; the memory adapter is volatile, and crash-persistent claims carry platform-pinned write, rename, and flush evidence | adapter contract suite per declared class | a durability claim without its declared-class evidence | storage adapters |
| `SRV-006` | Root heads move only by compare-and-set; concurrent publishers serialize; stale expectations fail with the standard precondition semantics | Lean server model; registry contract suite | a lost or torn head update | root registry |

## 8. Test and evidence strategy

The layers below are stages of the ratified dual-lane loop
([`CONFORMANCE-WORKFLOW.md`](CONFORMANCE-WORKFLOW.md)): layers 5–6 belong to
the conformance lane, layers 1–4 and 7 to the implementation lane, with the
versioned ratified manifest as the only coupling.

### Test layers

1. **Pure TypeScript tests:** reducer, node admission, canonicalization, cursor,
   mismatches, and witness construction.
2. **Schema laws:** construction, decode/encode, supported round trips, malformed
   nodes, and stable error categories.
3. **Effect integration tests:** service lookup, layer substitution, isolated
   sessions, typed failure propagation, and controlled live-adapter counters.
4. **Composition tests:** orchestration calling two wrapped leaf services,
   repeated identical calls, transparent nesting, and recovery after a
   substituted typed failure. Opaque subtree skipping begins with the M7
   extension.
5. **Lean examples and theorems:** positive witnesses, invalid examples, state
   invariants, reducer laws, and composition laws.
6. **Differential fixtures:** one versioned case manifest interpreted by the
   Lean model and manually mirrored TypeScript reducer, comparing ordered
   decision traces while retaining raw and normalized results separately.
7. **Pinned runtime observations:** public Effect imports only; results remain
   sampled G4 evidence unless a source translation is proved.

Use `effect/testing` FastCheck for domain properties beyond built-in Schema
assertions. Pin seeds and run counts for reproducibility. Tests involving state
use explicit `Ref`, `Deferred`, `Queue`, or test hooks; no wall-clock sleeps are
allowed in the initial suite.

### Fixture families

- empty history and terminal success;
- one success and one typed failure;
- orchestration recovery after a substituted typed failure;
- nested sequential calls;
- repeated identical invocations;
- wrong operation identity or revision;
- wrong request payload;
- invalid outcome Schema;
- missing entry and extra suffix entry;
- corrupt/dangling CAS reference;
- transparent orchestration with replayed leaves;
- forbidden or deterministically overridden Clock/Random/default-service use;
- store failure before append and after live completion;
- a session structurally aborted by an append failure, its truthful prefix
  retained; and
- attempted double wrap, and ambient host access inside supposedly conforming
  orchestration.

Framed-history fixtures for opaque outer substitution arrive with the M7
extension, not before.

Generated observations must be reproducible from declared sources through mise
tasks. Handwritten scenarios may be canonical inputs; derived snapshots may not
be silently hand-maintained.

## 9. Staged implementation

### M0 — ratify the contract

Status: completed 2026-08-26. The vocabulary and rulings landed in
`docs/effect-replay/CONTEXT.md`; the deliverables below stand as the record of
what was decided.

Deliverables:

- domain-modeling pass over the objects, operations, observations, and
  equalities in section 3;
- grilling pass over every positive, negative, boundary, and overclaim case;
- accepted vocabulary in the owning Context document;
- decision whether to instantiate the machine algebra or deliberately fork its
  pre-grade obligation shapes;
- adoption of the Level-0/Level-1/empty-Level-2 hash discipline;
- decisions for flat-history occurrence identity, leaf-substitution semantics,
  the request-compatibility versus outcome-admissibility split, project-owned
  digest framing, and first codec premises;
- explicit acceptance of the no-program-identity weakening and the Lean/TS
  quantifier mismatch;
- ambient Clock/Random/default-service admission policy;
- ratified placement of a mixed TypeScript/Lean package under `library/`,
  followed by the required `AGENTS.md` orientation update; and
- approved Pass-A declaration and obligation ledgers.

Exit:

- every public target has an informal meaning and falsification route;
- no pending representation question silently changes a theorem target; and
- the README may then describe the selected scope as more than proposed.

### M1 — bootstrap the TypeScript package and freeze foundational interfaces

Status: completed 2026-08-26. Three workflow-scaffolding items are deferred
into the milestones where their consumers land: the manifest printer and
generator plus the mutation tasks and quarantine grep arrive with the first
model slices (M2/M3), and the ledger transition-legality check arrives with
the first status flip.

Deliverables:

- package manifest, exact `effect`, TypeScript, and `@effect/tsgo` versions,
  lockfile, TypeScript configuration, public exports, test runner, and mise
  tasks;
- Source Lock expansion for Effect files used by service/layer integration —
  candidates enumerated by the 2026-08-26 service verification: `Context.ts`,
  `References.ts`, `Clock.ts`, `Random.ts`, `Schedule.ts`, `Effect.ts`,
  `Layer.ts`, `Schema.ts`, `Exit.ts`, `Cause.ts`, `internal/effect.ts`;
- Schema declarations for operation descriptions, CAS nodes, typed outcomes,
  replay modes, and mismatches;
- interface review for the CAS store, replay service, and live/record/replay
  adapter constructors;
- replay-mode construction whose environment has no live-service requirement;
- the conformance-workflow scaffolding per the ratified
  [`CONFORMANCE-WORKFLOW.md`](CONFORMANCE-WORKFLOW.md): the eight
  schema-bundle templates (statement, sentence, kit) in Lean, the canonical
  manifest printer and generator, the mutant quarantine layout with its gate
  grep, the conformance-ledger and briefing generators with the
  transition-legality check, and the mise task growth
  (`gen`/`check:effects:mutation`/`brief:effects`) — the two harness rows
  landed in `TOOLS.md` at ratification; and
- a mise task that refreshes the requested `research/docs/` snapshots from
  their canonical owners and checks byte equality without admitting the copies
  as authorities.

Exit:

- typecheck/Effect diagnostics and empty test suite pass;
- one Effect version is resolved;
- package payload is intentional;
- no implementation choice has become semantic authority by accident; and
- history and witness Schemas remain internal and explicitly subject to an M3
  re-freeze.

### M2 — CAS value vertical slice

Deliverables:

- raw and admitted CAS node representations;
- project-owned framed canonical encoder/decoder and abstract address
  interface; Schema supplies validation but not digest bytes;
- in-memory store adapter;
- Lean CAS carriers, well-formedness, canonicalization, and address premises;
- a mapping from the effects obligations to machine O1–O17, whether by direct
  instantiation or deliberate fork;
- positive/negative Schema and property tests; and
- corruption and dangling-reference errors.

Exit:

- `CAS-001` through `CAS-003` are established for the model or visibly
  pending with exact theorem statements;
- the TS adapters pass their declared tests; and
- no cryptographic or durability conclusion is inferred from the model.

### M3 — pure replay vertical slice

Deliverables:

- flat history, cursor, mode, decision-trace, mismatch, and witness
  representations;
- small manually mirrored TypeScript reducer plus a line-by-line correspondence
  review;
- Lean total reducer, derived transition relation, their agreement obligation,
  replay state/interpreter, and provisional theorem set;
- exact matching, no-fallback, repeated-occurrence, recovery-after-replayed-
  failure, and suffix fixtures;
- history and witness interface re-freeze after their selected representations
  pass review; and
- differential case manifest between Lean and TypeScript.

Exit:

- `RPL-001` through `RPL-005` hold for the Lean model with axiom report;
- TS property tests and differential fixtures pass;
- model results and implementation observations retain separate gate labels.

### M4 — Effect service and adapter vertical slice

Deliverables:

- replay service and session layer;
- distinct live, record, and replay construction roles, with no live dependency
  available to replay construction;
- helper for lifting one existing Effect service through operation
  descriptions;
- transparent orchestration and substituted leaf operations;
- integration fakes exposing live invocation counts;
- typed mapping of CAS, decode, live-service, and mismatch failures;
- replay-mode tripwire defaults for Clock and Random; and
- negative fixtures for Clock, Random, and jittered scheduling surfacing as
  `Violated` session outcomes.

Exit:

- `CTX-001`, `RPL-002`, and `RPL-004` pass at the TypeScript interface;
- replay construction neither requires nor receives the live adapter, and no
  captured live reference is permitted;
- the same caller program runs under live, record, and replay layers.

### M5 — compositional chaining

Deliverables:

- two independent described leaf services and one orchestration service;
- shared-session state threading across nested calls;
- Lean handler/environment extension and bind laws; and
- composition fixtures covering repeats, nested failure, recovery, and
  mismatches.

Exit:

- `CMP-001` and `CMP-002` hold for the selected model;
- a replayed orchestration consumes the expected nested history;
- outer opaque substitution stays on the M7 extension list and does not block
  the transparent core.

### E2–E3 — ergonomics lane (descriptor slices)

Ratified at the descriptor Pass A (2026-08-27) and sequenced after M5,
before M6, so the correspondence gate documents the improved surface.
Working design: leaf-first value descriptors over the declared canonical
encoding; typed roots that never bypass runtime kind validation; the
projection codec failure taxonomy outside the CAS error family; eager
fixed-root service hydration with `layerAs` targeting the kit's internal
live role. The implementing packet also carries the ratified
session-result widening and the replay tracer-timing rider.

E2 deliverables:

- `Cas.value` with typed `put`/`get` over the in-memory store;
- the declared canonical JSON encoding of the Schema's Encoded form —
  documented, versioned by descriptor kind tag and revision, and making
  no cross-claim with the Lean printer;
- the projection codec failure taxonomy; and
- the `PRJ-001` through `PRJ-003` fixtures.

E3 deliverables:

- `Cas.service` with eager `layer(root)` and `layerAs(tag, root)`;
- hydrated record construction demonstrated against a replayable kit; and
- the `PRJ-004` and `PRJ-005` must-fail fixtures.

Exit:

- `PRJ-001` through `PRJ-005` evidenced at the TypeScript interface;
- `PRJ-006` standing; and
- replay semantics, manifests, and the Lean model unchanged.

### R1–R6 — remote lane (ratified at the remote Pass A)

Sequenced after the ergonomics lane and before M6, so the
correspondence gate documents the full surface. Design authority:
[`research/remote-cas-conformance-design.md`](research/remote-cas-conformance-design.md)
over the prior-art compendium. Architecture, as ratified: a sans-io
remote client decision machine over the abstract exchange alphabet
(never HTTP); fault schedules as manifest fixture data executed by the
model, with schedule-vector rows landing additively under the
unchanged declared model version; the four evidence lanes with the
existing flip mechanics (instances, tsSide evidence list,
declared-evidence entries for the property and live lanes); one
declared mutant per falsification case in both directions.

- **R1** — the exchange alphabet and client machine in Lean, the
  schedule-vector emitter, and the `RMT-001`–`RMT-003` instances and
  mutants.
- **R2** — the single-operation TypeScript baseline: sans-io core,
  thin shell, deterministic fake-remote; `RMT-004` and the first
  AGREEMENT instance (`RMT-015`); RMT-002's shell half (a streaming
  byte counter so a declared oversize is never read or buffered).
  R2's architecture, per the R1 review corrections: the deep seam
  `CasStore → verified semantic adapter → RemoteCasTransport →
  HttpClient`, with the raw transport never a `CasStore`, canonical
  decoding and address verification enforced by the semantic adapter,
  and graph closure either a named backend capability (pin, lease, or
  transactional publication) or an explicitly weaker graph-publication
  capability; retries and redirects decided by the semantic core,
  never the HTTP shell (`HttpClient.retryTransient` and
  `followRedirects` are prohibited at this seam); typed remote errors
  replacing the catch-all store failure (not-found, unauthenticated,
  denied, rate-limited, capacity, protocol violation, oversize body,
  integrity rejection, indeterminate upload); explicit authority modes
  (remote-authoritative, local-authoritative, offline) with no silent
  fallback; and concurrency by client-assigned operation identifiers
  matching the machine — never ambient fiber identity. Streaming, per
  the R1-acceptance ruling, is first-class but separated: `CasStore`
  (whole admitted nodes) / `CasTransfer` (streamed mechanics, spooled
  whole-object verification, restartable-source retries, explicit
  byte budgets) / `CasEvents` (advisory notifications; HTTP and gRPC
  stay the primary data planes) / `RemoteCasTransport`
  (adapter-internal untrusted streams). The differential lane binds
  to an abstract conformance-peer interface with LeanServer as the
  ratified first peer, its audited gaps as named detection targets.
  Streaming obligation candidates entering section 7 with their
  slices: fragmentation invariance, terminal completion before
  admission, interruption exclusion, budget enforcement, and
  per-operation stream isolation. The layer-design docket is ratified
  (D1–D8, recorded in the workflow's section 14): one `layerRemote`
  provides `CasStore | CasTransfer` from one shared adapter build,
  `CasEvents` separate, the transport never a service key; one
  additive `CasError` member wraps the typed remote error; explicit
  Schema-validated configuration (four byte budgets, authority mode,
  redacted credentials), never ambient; tagged upload sources
  (`replayable`/`oneShot`) with the address recheck each attempt; one
  uniform verified-bytes download stream in a caller scope; the
  completion witness as the internal channel's typed terminal;
  per-operation child scopes; the abstract conformance-peer
  interface. By operator rider, **R2 assumes real transport**: the
  slice includes the real `HttpClient` realization of the seam under
  a declared project wire profile (versioned, documented, explicitly
  not a standard) and real TypeScript harnesses — an in-process
  reference server plus a raw-socket hostile server for framing
  faults — with the deterministic fake-remote retained as the
  vector-conformance carrier. The R2 Lean half is landed:
  the machine's dedup amendment, `RMT-004` (EXACT-STEP), and
  `RMT-015` (the first relational AGREEMENT), with their schedule
  families and mutants. The slice also dogfoods the ratified
  conformance harness (V1–V8 plus the upstream-semantics rider,
  section 14): the remote families are consumed through the generic
  family-binding machinery, expressed in the test library's own
  idioms with no custom runners, and the replay fixture module
  delegates compatibly.
- **MRK-1 — the Merkle proof lane, first slice** (ratified at the
  Merkle design ratification, sequenced before R3 by operator
  ruling; design authority:
  [`research/merkle-conformance-proof-infrastructure.md`](research/merkle-conformance-proof-infrastructure.md)).
  Conformance-side only: the `Effects/Merkle/` model — structural
  pre-images carrying domain separation and position in constructors
  over the abstract address function; chunking as a declared lossless
  partition; the RFC 9162-shaped root recursion and inclusion paths;
  the executable inclusion verifier with its reflection, completeness,
  and computable binding extraction; the verified-streaming decoder
  as a sans-io machine with temporal laws; slice decoding. Collision
  posture: constructive witness disjuncts, no collision-resistance
  axiom, Level-1 `hInj` only where a statement needs it. Obligations
  `MRK-001`–`MRK-006` and `MRK-008`–`MRK-010` with instances in
  existing families, declared direction-1 mutants, and model-executed
  vector families additive at the unchanged model version. The
  implementation-side consumption (chunked `CasBlob`, early-emission
  `CasTransfer`, TypeScript mirrors and harness lanes) is a LATER
  slice that consumes these ratified families.
- **MRK-2 — consistency proofs and verified partial reads**
  (`MRK-007`, `MRK-011`–`MRK-014`; docket Q1–Q5 RATIFIED 2026-08-27,
  conformance half landed the same day): the RFC 9162 `SUBPROOF`
  shape over the standards split — the consistency verifier with the
  size-derived walk, reflection iff, completeness, and the
  prefix-agreement corollary through the shared-split-point lemma;
  the proof-document codecs (opening; stream header and items over
  exactly the decoder's input alphabet) under the control-codec
  discipline with decode-of-encode identity and exactness; ranged
  stream-generation completeness (the server-half theorem behind the
  range-stream endpoint); and the blob refinement tie — the Merkle
  address function instantiated as the address of the canonical
  blob-node encoding, one declared blob tag with STRUCTURAL
  leaf/parent separation (the pre-image carrier's parent holds child
  addresses only), pre-image collisions transferring to byte-level
  hash collisions on bounded pre-images, and materialized nodes
  byte-bound well-formed under the profile chunk bound. Q5 — the
  key-list codec exactness closing the RMT-014 narrowing
  observation — deliberately waits for the F1 delivery so committed
  manifests do not move mid-slice. Design authority:
  [`research/server-reference-and-verified-reads.md`](research/server-reference-and-verified-reads.md).
- **MRK-3 — verified-reads hardening** (`MRK-015`–`MRK-019`; ratified
  2026-08-27 on the prior-art review's blocking findings): the
  four-kind blob manifest graph with REFERENCED content chunks as the
  headline recipe (manifest committing recipe id, total bytes, and
  leaf count; the landed inline-leaf tie retained as the first frozen
  recipe and the collision-transfer substrate); public byte-range
  semantics over an internal leaf-interval planner; the incremental
  sans-io frame parser with fragmentation invariance; the adversarial
  ranged-binding theorem with the named accepted-prefix judgment and
  root-provenance framing; response-framer closure and
  proof-amplification budgets. Review authority:
  [`research/server-reference-and-verified-reads-prior-art-review.md`](research/server-reference-and-verified-reads-prior-art-review.md).
  F2 was gated on the blob-representation ruling and is now
  unblocked: the F2 packet builds `CasBlob` on the manifest graph,
  never the inline-leaf recipe.
- **S-M — the server model, pulled forward** (`SRV-001`–`SRV-006`):
  **S-M1** the server transition system — staged bytes, admitted
  objects, protected roots, mutable heads, declared durability
  classes — with publication correctness (a client publish theorem is
  never a server durability or closure theorem), the admission
  pipeline, and capability truth as the five-way intersection;
  **S-M2** the object-store and root-registry contracts (three-outcome
  write-if-absent with same-address-different-bytes as an integrity
  fault, declared durability classes, compare-and-set heads, the
  first filesystem adapter append-only to postpone the
  garbage-collection race, maintenance operations separated and never
  remotely reachable by default). The reference server is built only
  on this model.
- **R3** — batching and closure: `RMT-005`–`RMT-008`, `RMT-014`;
  plus discovery-order pull (ruled at the R2 audit: a cold replica
  pulling a reference-carrying root must discover root-first and
  admit children-first — the R2 adapter documents this as a named
  limitation, and the sync-load fixtures' pull planner already
  models both orders). Ratified docket (P1–P8): **P1** presence is
  planning — batch answers land in advisory `reportedPresent`/
  `reportedMissing` sets that no admission state ever derives from,
  a `found` answer's wire bytes are dropped unverified, and no
  negative cache exists; **P2** closure via `confirmed` — a set grown
  ONLY by verified upload acknowledgments and verified loads, with
  publish gated on the root and its declared closure standing
  confirmed and a publish acknowledgment growing `published` only
  (server acceptance never implies closure); **P3** batch accounting
  is exact and order-sensitive — results answer the requested keys
  one for one in request order, anything else rejects the whole
  batch closed; **P4** interruption is a first-class wire event
  resolving any in-flight operation as its typed failure with the
  in-flight entry erased and every admission component frozen;
  **P5** the key-count budget checks `findMissing` requests before
  issue, as a typed rejection; **P6** the capability-document codec
  is closed and exact (`ControlCodec`: big-endian 32-bit fields,
  decode-of-encode identity, decode's image IS the canonical
  encoding); **P7** the R3 vector families run under an extended
  state summary carrying the planning, confirmed, and published
  sizes while the R1/R2 families keep the original renderer
  verbatim; **P8** the TypeScript half stages discovery-order pull
  on the mirrored machine — root-first discovery, children-first
  admission through a staging area that never touches the CAS until
  closure admits.
- **R4** — policy: `RMT-009`–`RMT-012`, `RMT-016`. The standards bind
  the retry obligations: an HTTP retry requires application
  idempotency or evidence the original request was not applied
  (RFC 9110 §9.2.2), and gRPC success is final-trailer gated with an
  explicit commitment boundary — so the machine gains `AttemptId`,
  explicit `knownUnprocessed | possiblyProcessed` evidence, and a
  protocol-completion witness carrying byte counts and terminal
  framing, entering through section 7.
- **R5** — the property/state-machine lane, entering as declared
  evidence.
- **R6** — the live lane and one real backend layer under scoped
  acquisition; the section-4 `Scope` row amendment lands here.
  LeanServer (`AfonsoBitoque/LeanServer`) is ADOPTED for real server
  semantics by operator ruling — planned for absolutely, landing at
  its own slice (not necessarily R2 or R3), always behind the
  abstract conformance-peer interface with its audited gaps as named
  detection targets, never a standards oracle.
- **Implementation-lane sequencing (directed 2026-08-27):** front-end
  slices first — **F1** the remote API to spec (machine-mirror
  catch-up, the five R3 families through the harness, the control
  codec, adapter counterparts, `push`; in flight), **F2** the Merkle
  query surface (TypeScript mirrors consuming the MRK families,
  proof-document codecs, `CasBlob`), **F3** the discovery-order pull
  staging area (ratified P8). The normative wire letter for F1's
  adapter half is [`PROFILE-CAS-HTTP-0.md`](PROFILE-CAS-HTTP-0.md)
  W1–W6.
- **S-lane — server tooling toward publication (directed
  2026-08-27):** **S1** the reference server (`CasServer` over
  pluggable storage, capabilities derived from policy, handlers
  sharing the client codecs) and the conformance kit packaged as a
  black-box server suite; **S2** the LeanServer binding slice and the
  server-machine survey. Target design:
  [`research/server-reference-and-verified-reads.md`](research/server-reference-and-verified-reads.md).
  The splash gate stays: the TypeScript verifier passing end-to-end
  against the reference server.

Exit:

- every `RMT` row green or standing;
- no HTTP, TLS, wall-clock, or server internals in the Lean model; and
- no recorded transcript ever serves as a schedule.

### M6 — correspondence and public library gate

Deliverables:

- versioned fixture generator and observation normalizer;
- reproducible G4 differential suite against the pinned Effect build;
- claim matrix linking each public statement to its highest gate;
- package documentation and examples that state exclusions; and
- public-package dry run with exact files and dependency metadata.

Exit:

- the published claim is limited to proved model laws plus observed agreement
  on the stated implementation domain;
- G3 remains pending unless an admitted source fragment and translation theorem
  exist;
- no compiler or hosted-execution conclusion is implied.

### M7 and later — controlled extensions

Add one semantic dimension per milestone:

1. framed histories and opaque substitution of an outer orchestration
   operation;
2. defect and interruption distinctions;
3. sequential Scope/finalizer behavior;
4. crash-aware journaling and filesystem CAS (write-ahead intent entries
   narrow, never close, the crash gap);
5. ActionIndex with an explicit recomputation/cache consumer;
6. checkpoints and retention;
7. nondeterministic choice; and
8. fibers, causal histories, races, and cancellation.

Each extension re-enters Pass A and receives its own observation profile,
counterexamples, theorem delta, fixtures, and claim gate. Concurrency does not
reuse a sequential list history without adding event identity, causality, and
conflict semantics.

## 10. Claim and correspondence plan

| Gate | Planned statement class | Required work |
| --- | --- | --- |
| G0 | Exact Effect and external source bytes selected | Extend Source Lock with used runtime/service files and receipts |
| G1 | Named laws hold for the Lean CAS/replay definitions | Kernel-checked theorems, pinned toolchain, imports, axiom report |
| G2 | The Lean model implements the ratified CAS/replay contract | Traceability, reviewed quantifiers, examples, counterexamples, observables |
| G3 | An admitted source fragment translates to the model | Accepted-source judgment, translation, and theorem over the named source/model relation |
| G4 | Pinned Effect/TypeScript implementation agrees on a stated domain | Reproducible differential fixtures and normalized observations |
| G5 | Compilation-relation claim for emitted JavaScript | Pinned compiler/configuration and source/target relation |
| G6 | Hosted-execution relation for a named engine and host | Host contracts, versions, runtime evidence or proof |

M0–M5 target G1/G2 for the model and ordinary implementation tests. M6 targets
carefully worded G4 evidence. G3 is not assumed to occur before G4 because a
differential test suite can exist without a proved source translation; the
gate labels remain independent and no later observation promotes an earlier
bridge automatically.

The G2 traceability matrix must state that the Lean theorem ranges over the
reified admitted program carrier, while ordinary TypeScript orchestration is
only discipline-conforming in the first release. No wording may silently replace
the former quantifier with "all Effect programs" or "all programs using the
service."

## 11. Stop conditions and risks

Stop and return to the contract if:

- an arbitrary closure or `Effect` object is treated as serializable program
  identity;
- an operation lacks request, success, and typed-failure representations;
- a replay mismatch falls through to a live adapter;
- replay-mode construction requires, receives, or captures a live adapter;
- ActionIndex is introduced before recomputation/cache mode supplies a real
  consumer;
- orchestration consults a default Clock/Random service or jittered schedule
  without mediation or an explicitly selected deterministic override;
- Schema's default JSON encoding is used as a digest pre-image;
- a witness or compatibility check implies a program identity that the slice
  does not carry;
- Context or Layer internals enter Lean declarations without a declared
  observation requiring them;
- defects, interruption, or finalizer failure are collapsed into typed failure;
- persistence wording implies exactly-once behavior across the live/append
  crash gap;
- a TypeScript test result is described as a Lean or translation theorem;
- concurrency begins before causal and cancellation observations are frozen;
  or
- a generated or external tool output enters gated work without a registered
  role and trust statement.

Primary risks:

| Risk | Mitigation |
| --- | --- |
| Service wrapping appears generic but cannot encode method semantics | Require explicit operation descriptions and stable rejections |
| Wrapper recursively resolves the service it is constructing | Separate live/public construction roles and test the layer graph |
| Replay wrapper can still reach live behavior | Give replay construction no live dependency and reject captured references |
| CAS reuse collapses repeated calls | Keep invocation content and occurrence history as separate nodes |
| Model/TS reducer drift | Shared versioned fixtures, differential tests, and independent review |
| Hash or codec is treated as mathematical authority | Use the Level-0/Level-1/empty-Level-2 lattice and keep concrete adapters outside model claims |
| Schema JSON bytes drift across Effect versions | Hash only the project-owned framed canonical encoding |
| Default Clock/Random services bypass visible requirements | Reject them in conforming orchestration; tripwire defaults in replay mode |
| Replay history is mistaken for program identity | State the weakening in the contract, witness, fixtures, and G2 matrix |
| Crash after live effect but before append | Make the gap observable; prohibit exactly-once language |
| Unstable Effect workflow/eventlog APIs dictate the contract | Use only as version-sensitive prior art; own the public interface |
| Scope expands to arbitrary Effect programs | Enforce the described leaf-operation boundary and retain the ambient-effect counterexample |

## 12. Decisions ratified before M1 (2026-08-26)

The M0 grilling session resolved every open decision:

1. **Machine relationship:** deliberate fork of the machine's obligation
   shapes; no Lake or code dependency on `library/machine`; the hash lattice
   is adopted; the M2 mapping table is the standing correspondence audit;
   convergence to instantiation is expected only after the machine algebra is
   itself ratified.
2. **Names and context:** the Effect Replay context is minted at
   `docs/effect-replay/CONTEXT.md`, fully independent of the Entity Store
   context, with four lexical rules (compound-named admission judgments,
   "conforming" for discipline, no "verdict", "canonical" glossed).
3. **Canonical representation:** pre-image
   `versionByte ++ kindTag ++ frame(encode(canon node))`; one-byte kind plane;
   references inside the framed body as full-length addresses in declared
   order; no digest truncation; SHA-256 platform crypto as the first adapter;
   any pre-image-affecting change bumps the scheme version byte. Byte-level
   framing and scalar encodings are Pass-B work.
4. **Occurrence identity:** structural `(executionId, index)`;
   request-content-keyed reuse answering an occurrence is a named defect.
5. **Typed failures:** Schema-tagged data values in a channel-preserving
   success/failure envelope; nothing host-shaped is recorded.
6. **Service lifting:** one kit constructor per described service minting an
   internal live role tag; record requires the live role and replay service,
   replay requires the replay service only; runtime string-keyed brand checked
   at construction; double wrap rejects.
7. **Ambient policy:** reject-first; replay-mode tripwire Clock/Random
   defaults surfacing as `Violated` (mechanism verified against the pinned
   source, 2026-08-26); deterministic overrides deferred until a fixture
   demands one.
8. **Opaque substitution:** deferred to the M7 extension list; M5 is
   transparent chaining only.
9. **Package:** private until the M6 gate; name candidate
   `@foldlab/effect-replay`, final at M1.
10. **Placement:** mixed TypeScript/Lean tenant ratified under `library/`;
    the `AGENTS.md` orientation row is updated accordingly.
11. **Compilation-techniques PDF:** the local copy stays gitignored;
    paper-lock admission is queued for the papers-lock landing session; no
    estate citation until admitted.

The reducer strategy was closed before the session: a small manual TypeScript
mirror checked by normalized decision-trace fixtures. ActionIndex begins only
with a recomputation/cache consumer.

Every positive, negative, boundary, and overclaim case in section 3 was
grilled in the ratification session; the session-boundary transport, mismatch
taxonomy, session poisoning, tripwire policy, and construction-role rulings
recorded above and in the context document came out of those cases. M1 may
begin.

## 13. Decisions ratified in the language wave (2026-08-28)

The language grilling session resolved the shape of the Lean package and the
schema plane. Every ruling below was operator-ratified in session; the landed
state is in the tree and its gates.

1. **One language, three layers.** The byte grammar (`Cas/Codec`, proved),
   the data grammar (`Cas/Grammar`, sorted trees), and the program grammar
   (`Cas/Lang`, signature-parameterized operation trees) are three layers of
   ONE language; each layer's semantics is elaboration into the layer below,
   and every law quantifies over the abstract address function `H`.
2. **One package, staged directories.** `library/cas` is the language
   package: stage directories `Codec/ Core/ Values/ IR/ Grammar/ Lang/` in
   abstraction order, stage roots inside their directories, and a flat
   dependency-ordered root import list — the layout studied from the
   lambdaclass/concrete clone (`.reference/clones/concrete@28a25a4e2`,
   Apache-2.0). Examples are a separate Lake library (`CasExamples`,
   `srcDir = examples`) kept in `defaultTargets`: consumers of the language,
   never part of it. The package outgrowing its `cas` name is a named,
   deferred question.
3. **The store word is the IR.** `Word = List (Addr32 × Node)` in
   children-first admission order, first-binding resolution, `toStore` the
   bridge onto the function store. The proved landing bar L1–L7 (all green):
   `wf_toStore_closed`; `address_spec` (definitional); `flatten_wf` at
   lattice Level 1 under named `hInj`; `node_wf` by bounded constructors;
   `step_put_fresh`/`step_put_error` (the interpreter CALLS `Cas.put`, never
   re-derives admission); `step_load_agrees`; `step`/`run_preserves_wf`.
   Named follow-ups: F1 `putTree_correct`, F2 word dedup at Level 1,
   F3 defunctionalized continuations (steps as store-admissible content).
   **F1 and F2 PROVED (2026-08-28, later same wave).** F2:
   `Word.toStore_append_shadowed` (Level 0 — a second binding at an
   occupied address is inert through the bridge) +
   `Grammar.Honest.no_alias` (Level 1 — an honest word never binds one
   address to two nodes; `hInj` + codec non-malleability). F1:
   `Cas/Lang/TreeProg.lean` — `Tree.progK`/`Tree.prog` write a grammar
   term as a store program that learns every address from the
   interpreter (never from `H`); `putTree_correct` proves running it
   with node-count-plus-one fuel over any honest admissible word
   completes at exactly `Tree.address`, grows the word by a SUBLIST of
   `flatten` (shared subterms deduplicate through `put`'s duplicate
   outcome — F2 in action), and reaches exactly `flatten`'s store
   through the bridge; `putTree_correct_empty` is the from-nothing
   corollary. One packaged step (`step_put_honest`) carries the
   fresh-or-duplicate dichotomy; conflict is unreachable over honest
   words at Level 1. F3 remains the open follow-up.
4. **The LLM is a first-class signature.** Core `CasSig` is the store
   algebra only (`put`/`load`/`fail`); the LLM extension is `LlmSig` with
   `infer` (the old `ask` is dead); languages compose by signature sum and
   interpret by monad morphism (`handleLlm`). An inference is an
   acquisition; admission is the only gate by which it becomes load-bearing;
   attestation is an executor's claim, never a proof.
5. **SHA-256 is transcribed, not invented.** `Cas/Codec/Sha256.lean` carries
   the FIPS 180-4 spec as `BitVec` mathematics — per-block pipeline
   transcribed with credit from concrete's `Sha256Spec.lean`, padding and
   multi-block completed here — gated by the NIST known-answer vectors as
   build-time interpreter asserts (never kernel `decide`). The toy fnv1a
   digest is dead everywhere; `sha256Addr` is the production vector digest,
   collapsing the two-tier vector design to one tier.
6. **The CAS typeclass.** `Canonical` (encode, closed decode, forward
   correctness, image exactness) with the hash-hypothesis lattice proved
   once generically; `AdmittedNode` instantiates it at zero proof cost;
   grammar trees are addressable through elaboration (`toAdmitted`), not
   `Canonical` themselves.
7. **The schema hierarchy.** Our canonical schema is the ROOT — nothing
   stands above it; its identity is the digest of its canonical bytes, so
   schemas are store content (reserved kind tag `0x53`). Effect is the
   primary runtime and Effect Schema is a CARRIER of the canonical schema,
   never an authority; JSON Schema is an export projection only. The
   SchemaAST census and the entity-store extract/generate pipeline are
   re-aimed as the carrier-adequacy record (admission map per AST variant).
   Standing law of the plane: no canonical construct's identity lives in a
   function.
8. **The canonical schema revision 1, both directions.**
   `src/cas/CanonicalSchema.ts` (`Cas.CanonicalSchema`) uses Effect's native
   `SchemaAST.AST` and persistent `SchemaRepresentation.Document`; TypeScript
   defines no parallel AST algebra. The annotation API snapshots a strict,
   recursively frozen representation, with bytes ALWAYS derived on read,
   never stored. `fromAst` snapshots through the native representation and
   revives a runtime carrier; the package declaration reviver restores
   tag-pinned `refWithTag` value-plane semantics, so reference edges remain
   admission-checked by the store. Revision 0's tagged document is a strict
   read-compatibility path only. Deferred to the schema commission:
   references carrying their target schema's address and schema-to-schema
   edges as real CAS references.
9. **The two-minute rule** (operator-ordered lane law,
   `library/cas/AGENTS.md`): a stalled proof stops after two minutes and
   consults standard literature, prior art, and the skills — never grinds.
   Bit-level machinery is imported and credited when a determination exists,
   never re-derived.

**The vector lane LANDED (2026-08-28, same wave).** The registered
replay surface, patterned on lean4-tree-sitter's `GrammarSpec`
registration (the registered thing is a first-class typed value; one
registry; a tracking manifest):

- `library/cas/Cas/Vectors/Vectors.lean` — `ConformanceVector`
  (name, description, word) with its canonical JSON projection
  (`Json.render` manifest form, so regeneration is byte-identical by
  construction) and the `index.json` manifest builder.
- `library/cas/tools/Vectors.lean` (`lake exe vectors`) — ONE registry
  of four vectors seeded through the grammar under `sha256Addr`
  (value-single, blob-two-leaves, file-readme, journal-two-entries;
  22 bindings total); every word is gated on `Word.wf` at emission;
  `--check` is the byte-identity gate. Fixtures committed under
  `library/cas/vectors/`.
- `src/cas/ConformanceVector.ts` (`Cas.ConformanceVector`) — the TS
  twin: wire schemas hand-mirroring the Lean emitter (the drift
  tripwire), `toNodeInput` projection; on the barrel.
- `test/ConformanceVectors.test.ts` — the replay: every binding put
  through `layerMemoryLive` (real WebCrypto SHA-256) answers the
  Lean-computed address; roots read back byte-identical through the
  verified load path; a root put out of order refuses with
  `DanglingReference` (admission order is semantics); the index rows
  match the fixtures. Follows the ratified V1–V8 harness rulings at
  this scale (loading inside Effect, case id in the assertion, no
  snapshots, decode failure is red).
- One independent cross-check performed at landing: `value-single`'s
  address recomputed by hand-assembling the preimage under .NET
  SHA-256 — byte-identical to the Lean digest.
- mise wiring: `check:cas` now runs `lake --wfail build` + `lake exe
  vectors --check`; `gen:cas-vectors` regenerates; `gen` includes it.
- **Described addendum (same day, revised to schema revision 1):** the vector format is itself a
  described tree. Lean: `vectorAst`/`indexAst` are canonical schema
  codes (strictly sorted, literal codes pin the digest-scheme and
  format-version values), the document is `Schema.encode` of the
  vector's `El` image (no hand-rolled projection survives), and
  validation is DERIVED — `decode_json`/`validates_json`/`json_exact`
  are instances of the universe's one-time forward and exactness
  theorems at the vector code. The refactor reproduced every committed
  fixture byte-for-byte (`--check` passed unregenerated). TS now consumes
  generated `vectorSchema`/`indexSchema` values made solely from Effect's
  native constructors, and the richer wire schemas carry those native
  persistent representations via the annotation API (carrier/identity
  split). Asserting the schema bytes agree across runtimes (the
  canonical-schema pin) was BLOCKED
  on the schema commission's Lean Ast codec — **UNBLOCKED and LANDED
  2026-08-28**: `Cas.Schema.SelfCodec` (the codes' JSON projection,
  envelope, and canonical payload), the `cas_struct` authoring
  notation (`Cas.Schema.Notation`: one declaration → structure +
  `Described` instance + raw-schema surface), the `lake exe schemas`
  registry with committed byte fixtures under `library/cas/schemas/`,
  and `test/CanonicalSchemaPin.test.ts` asserting
  `CanonicalSchema.payloadOf` answers the Lean-emitted bytes for every
  registered code (the vector document/index codes among them — the
  hand-mirror tripwire is now byte-armed). Same day, the byte-level
  revision-0 rendering theorem LANDED kernel-checked
  (`Cas/Schema/Codec/Laws/Render.lean`, `Values/Json.lean`,
  `SelfCodec.lean`): `encode_canonical` + `renderCompact_encode`
  prove the encode image is canonically spelled and the canonical
  rendering performs no reordering on it; the renamed
  `legacyEnvelope_renderPlain` binds legacy schema payloads the same way;
  `ofJson_toJson`/`toJson_inj` give that self-codec a proved round trip (one
  code per payload value). Revision 1's independent Lean/TypeScript byte pin
  is green; its corresponding byte theorem remains pending.
  Remaining open direction, named precisely: injectivity of the
  canonical rendering itself (bytes determine the canonical value —
  a verified-parser development).

**THE FIRST CAS (2026-08-28, delegated wave 1, coordinator-verified):**
the library now demonstrably creates a real, durable, on-disk store.
`test/FileCas.test.ts`: a file-backed store in a temp directory —
replay of every Lean vector at the Lean-computed addresses; every
`objects/<2hex>/<62hex>` file byte-identical to the canonical
encoding; a completely FRESH composition over the same directory
serves every root through the verified load path; second replay
answers identical ids and moves no bytes; `roots/<id>` publication and
listing. The `FileSystem` realization over `node:fs/promises` is test
scaffolding (effect v4 core ships only `makeNoop`;
`@effect/platform-node` is NOT a dependency — adding a production Node
realization is an operator dependency decision, surfaced and pending).
Vector loader factored to `test/fixtures/vectors.ts`. Lean side:
`examples/CasExamples/PutTree.lean` runs F1/F2 through the interpreter
at build time (distinct 6→6; shared 5→4 deduped; replay inert binding
for binding), and the fifth vector `shared-chunk` commits a word with
a genuine duplicate binding — the executable witness that `Word.wf`
accepts duplicates and replays dedup them. Gates re-run by the
coordinator personally: 273 TS tests, typecheck 0, lint 0,
`check:cas` green (49 jobs, 5 vectors).

**Wave 2 finding (2026-08-28): `Cas.Transfer` is not locally
composable.** The service's only shipped constructor is
`layerRemote(remoteConfig)` over a pinned HTTP transport, so two local
stores cannot meet through the Transfer surface without an HTTP peer.
`test/DiskSurfaces.test.ts` performs the push law by hand (closure
enumeration + children-first puts, identity asserted down to disk
bytes). A local `CasTransfer` realization over a second
`ByteReader`/`ByteWriter` pair would close the gap — queued as a
lib-finishing candidate, operator's call.

## 14. The grammar grill (2026-08-28, six rulings, operator-ratified)

What belongs in the language grammar, walked branch by branch:

1. **Charter.** The grammar is the full metalanguage: content,
   computation, AND schema. Everything the store can hold is a
   production of the grammar.
2. **Sorts.** All seven sorts ratified into core — value(1), chunk(8),
   tree(9), manifest(10), file(11), entry(12), context(13); registry
   rows owed. A consumer-extension mechanism (profiles, the
   GrammarSpec registration pattern) is a named follow-up, not
   retrofitted.
3. **The schema sort.** `.schema` (0x53) minted NOW with an
   opaque-payload discipline: payload = canonical schema bytes from
   the schema plane, refs empty in v0; the payload-IS-rendering law
   arrives with the schema commission's Lean Ast codec. Named
   follow-up: schemas referencing schemas as typed edges (the $defs
   graph as real CAS references — where recursion naturally lives
   content-addressed).
4. **Computation (F3 shape).** Defunctionalized code points, the
   Reynolds move: a program compiles to a finite table of first-order
   nodes (operation + typed refs to captured environment + next code
   point), new step/cont sorts; running is an interpreter walking
   content; the correctness theorem is F1's pattern extended. No
   binder metatheory; the word stays the run's history.
5. **Operations.** CasSig frozen at put/load/fail. Roots enter as
   RootSig (publish/listRoots) by signature sum, mirroring the TS
   RootStore seam. Presence stays derived. CLI verbs, graph walks,
   transfers: programs, never operations. Extension policy:
   consumer-gated admission — a signature enters only with a real
   consumer through the grill; ClockSig/RandomSig/network refused
   until then (nondeterminism enters only as recorded content, which
   `infer` demonstrates).
6. **Concrete syntax.** The described canonical JSON document (the
   vector format: byte-canonical rendering, proved generic codec,
   derived validation) IS the language's concrete syntax — a sentence
   is a canonical document, a word a sequence of them. Lean macros and
   the future CLI are input surfaces elaborating to it; no new text
   format is ever minted.

**Queued (operator-raised 2026-08-28, marked for later, un-grilled):**
a `cas` CLI surface — ask it about any directory and it answers whether
a store lives there; it emits the canonical store representation (the
described word document above) and can optionally initialize one of
our stores in the directory (the `objects/`+`roots/` store-root layout
the file backend and path reader already share). Operator's framing to
preserve: the CLI IS another grammar/language — commands are
operations of the store language, a session is a program, the
canonical representation is the word. @effect/cli when built; grill
before building.

**CLI grill round 1 (operator-ruled 2026-08-29, all as
recommended):**

1. **Store locate** — git-style, fail-closed: `--store` flag >
   `CAS_STORE` env > walk-up discovery of a `.cas/` directory > refuse
   with guidance. `init` is the only creator; `init --bare <dir>`
   makes the directory itself the store root (the ratified
   `objects/`+`roots/` layout, servable and committable). Rendered
   surfaces say "store" for location; "roots" only ever means
   published addresses.
2. **`put` input** — the described canonical node document
   (kind/payload/refs, the vector wire shape), satisfying concrete-
   syntax ruling 6: elaborate to existing syntax, mint no format.
   Typed `--schema` put and blob ingestion are separate later verbs.
3. **`doctor`** — ships in v0: replay the Lean-minted vectors against
   an ephemeral store of the same backend kind (temp dir /
   `:memory:`), word equality binding for binding. Never mutates user
   data. Vectors ship as generated package data.

**Vocabulary law (operator-ratified 2026-08-29, home corrected same
day):** the user register is pinned in [VOCABULARY.md](VOCABULARY.md)
— a two-register split (everyday / protocol) under the consumer-gating
rule: a term enters the everyday register only when a verb needs it.
`--help` is the ONE surface for commands and vocabulary together —
they must stay coherent; no vocabulary verb, no startup card.
Operator principle recorded: vocabulary is semantics, and semantics
may alter while the grammar (sorts, wire tags, node structure) stays
fixed — which is why help and vocabulary flow toward store content
per the CLI rider (help = described documents), with VOCABULARY.md as
the seed, never a second copy.

**Startup direction (operator-directed 2026-08-29, pre-grill):**
config/startup semantics must be explicit — @effect/cli's built-in
wizard for `init`; `cas status` must surface the concrete data
location (store directory or database file) and the backup/replication
target as inspectable paths, so where the data lives is always one
command away. Status law (operator-ruled 2026-08-29): `status` never
alters anything — read-only by construction; printing is its entire
effect.

**CLI grill round 2 (operator-ruled 2026-08-29, all as
recommended):**

1. **Config home** — `config.json` inside the store directory
   (`.cas/config.json`; `<dir>/config.json` for bare), written by the
   `init` wizard, printed by `status`. Precedence: flags > env >
   config file > defaults. The credential is never inline in config;
   config may name a `credentialFile` path or an env var only, so a
   store root that is rsynced or pushed never carries a secret.
2. **Output registers** — every verb has two: the human register by
   default (even when piped — no TTY magic), and explicit `--json`
   emitting described canonical documents only (generated-schema
   shapes, concrete-syntax ruling 6; never ad-hoc dumps). Agents and
   the wire read the same syntax.
3. **Backup** — surfacing only, no verb. File backend: the directory
   is the store (rsync, commit, push). Sqlite: detect Litestream,
   print target and lag (target named in `config.json` so status can
   say where backups are supposed to be even when the replicator is
   down), and warn loudly when the database file is the only copy.
   Replication configuration stays Litestream's own.

Grill complete for the v0 verb set: `init` (wizard), `status`
(read-only law), `ls`, `show`, `kinds`, `verify`, `put` (node
document), `doctor` (ephemeral twin), `serve`. Standing tripwires: no
run/exec/naming verbs until the F3 decoder and naming-record grill
land; no transport-adapter claims until the R11 manifest exists.

Owed: provenance
receipts for the concrete transcription and catalog rows for
predictable-machines lean4-json-schema and lean4-tree-sitter; CONTEXT
entries for the terms minted this wave (store word, the language layers,
the CAS typeclass, canonical schema) in their proper format — several may
belong to a broader context than effect-replay, which is its own pending
ruling.
