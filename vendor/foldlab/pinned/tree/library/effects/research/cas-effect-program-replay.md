# Content-addressed replay of effect programs

Status: conception-mode research draft

Snapshot: 2026-08-26

Claim posture: **G0/G1-unadmitted research hypotheses**

This report is research input for `library/effects`. It is not a domain
contract, a ratified definition set, a proof submission, or an implementation
claim. Exact external revisions are recorded where they could be resolved, but
this pass made **no Source Lock additions**. Except for already admitted estate
inputs explicitly identified in the source ledger, external provenance remains
pending under the repository's [claim gates](../../../docs/effect-typescript-semantics/CLAIM-GATES.md).

## Exact question

How should Foldlab describe, identify, record, and replay a deliberately
restricted class of Effect TypeScript programs when:

1. the program and its closed dependencies are identified by content;
2. effect requests and their outcomes can be recorded without confusing a
   history with program meaning;
3. replay rejects incomplete, incompatible, corrupt, or under-specified inputs;
4. a future Lean model can state the relevant obligations without importing
   JavaScript closures or host behavior as semantic authority; and
5. generated TypeScript uses public Effect operations from one pinned Effect
   revision?

The central finding is that **content addressing and replay solve different
problems**. A content address can identify canonical bytes and link immutable
objects. Replay additionally needs an effect protocol, a history discipline, a
program/environment compatibility rule, an observation policy, and explicit
treatment of nondeterminism. Neither mechanism by itself makes external actions
single-occurrence, makes an execution deterministic, or establishes that two
implementations have the same behavior.

### Non-goals

This pass does not:

- select canonical vocabulary for the library;
- define a Lean carrier, judgment, theorem, or serialization;
- claim correspondence with arbitrary `Effect<A, E, R>` values;
- serialize JavaScript closures, continuations, objects with identity, or live
  resources;
- choose a storage engine, network protocol, hash function, encryption scheme,
  or garbage collector;
- make CAR, IPLD, Temporal, Restate, Golem, Unison, Nix, Bazel, rr, Interaction
  Trees, Choice Trees, or Blaze a dependency;
- turn a recorded result into evidence that the current external world would
  return that result; or
- permit destructive live side effects during ordinary replay.

## The distinctions the design must retain

The following are role labels for this report, not minted estate definitions.

| Role | What it identifies | Why it must remain separate |
| --- | --- | --- |
| Program description / code identity | Canonical syntax accepted by the restricted language and the generator version that interprets it | Equal source names or emitted text do not necessarily identify the same accepted program |
| Dependency closure | Every referenced block, schema, library pin, and generated-code dependency reachable from the program root | A root syntax hash that omits transitive behavior is an incomplete cache key |
| Handler / environment identity | Effect-operation signatures, selected handler implementations, non-secret configuration, runtime policy, and named host capabilities | The same program can produce different observations under different handlers or environments |
| Effect history | Ordered or causally related requests, decisions, outcomes, failures, interruption, and resource events for one execution | A history is execution data; it is not the program, handler, or a general law |
| Checkpoint / snapshot | A state image tied to a program/environment identity and an exact history prefix | A state image without its prefix and decoder version is ambiguous |
| Replay witness | The replay mode, identities used, consumed history, produced observations, and first mismatch or successful terminal status | “Replay succeeded” is meaningless without the mode and comparison policy |
| Host evidence | Compiler/runtime versions, external receipts, signatures, service attestations, and observations made outside the model | Hashing a receipt gives it byte identity; it does not make the represented event true |

A useful discipline is therefore:

```text
program identity  != execution identity
execution history != handler meaning
checkpoint        != history
replay witness    != host attestation
content identity  != authority, availability, or behavioral agreement
```

## Primary-source precedents

### Unison: content-addressed code and effects are adjacent, not identical

Unison identifies definitions by hashes of their syntax trees, treats names as
separate metadata, and substitutes dependency hashes into the hashed form. Its
official description also uses this closure to move computations and request
missing dependencies on demand. This is strong precedent for program and
dependency identity, but it does not identify an execution history or the
external state consulted by a handler. ([pinned Unison repository README](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/README.md),
[official “big idea” page, provenance pending](https://www.unison-lang.org/docs/the-big-idea/))

Unison abilities place required effects in function types and handlers provide
their interpretation. Distributed computation is exposed through abilities as
ordinary language-level programming. The relevant lesson is to hash the
effectful program and name the handler/environment separately; the ability set
alone does not identify which handler ran. ([official ability reference,
provenance pending](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/),
[official distributed example, provenance pending](https://www.unison-lang.org/docs/at-a-glance/))

### Temporal: command/history matching and explicit code evolution

Temporal persists a Workflow Execution's events in an append-only Event
History. During replay, Workflow code re-emits Commands, and the worker checks
them against existing history; an out-of-sequence or different Command causes a
nondeterminism error. External calls belong in Activities rather than directly
in replayed Workflow code. ([pinned Event History page](https://github.com/temporalio/documentation/blob/4d6668766030e4ed17f197a9d9e93566ba3a77db/docs/encyclopedia/event-history/event-history.mdx),
[pinned deterministic-constraints page](https://github.com/temporalio/documentation/blob/4d6668766030e4ed17f197a9d9e93566ba3a77db/docs/encyclopedia/workflow/workflow-definition.mdx))

Temporal also separates in-memory workflow caching from history replay and
offers worker versioning or patch markers for code evolution. The precedent is
fail-closed command matching plus an explicit version path. The mismatch is
that Temporal's primary history is an ordered service log, not a typed
content-addressed graph, and its workflow model is not the proposed Foldlab
effect subset. ([pinned workflow-execution page](https://github.com/temporalio/documentation/blob/4d6668766030e4ed17f197a9d9e93566ba3a77db/docs/encyclopedia/workflow/workflow-execution/workflow-execution.mdx),
[pinned versioning discussion](https://github.com/temporalio/documentation/blob/4d6668766030e4ed17f197a9d9e93566ba3a77db/docs/encyclopedia/workflow/workflow-definition.mdx#versioning-workflows))

### Restate: journal ownership and replay/processing phases

Restate's service invocation protocol models an invocation as a state machine
and logs transitions in an invocation journal. Runtime and service deployment
both track the journal, but the protocol assigns authority differently in
replaying and processing phases; the service deployment may not create new
journal entries while replaying. Syscalls create journal entries, and later
completions are correlated to entry indexes even when completions arrive in a
different order. ([pinned Restate Service Invocation Protocol](https://github.com/restatedev/service-protocol/blob/eaebc104834cf3405267ec180912b0e295340501/service-invocation-protocol.md))

This is useful precedent for a replay phase that cannot accidentally perform
new work. It does not supply content identity for programs or histories, and
its guarantees are scoped to the Restate runtime/protocol. The protocol also
shows why journal order and completion order may need separate representation.
The cited repository was archived in February 2025, so it is used only as a
versioned protocol precedent; correspondence with current Restate behavior
remains separately pending.

### Golem: operation log, live/replay split, and snapshots

Golem 1.5 documents durable agents as recording side effects in an operation
log and recovering by replay. Its lower-level durability interface exposes
whether execution is live; a library can persist an invocation's response and
use that persisted response during replay instead of running the side effect.
([pinned Golem durability configuration](https://github.com/golemcloud/golem/blob/f93a5bd34128064c3159c6500ee808710f56ff11/docs/src/content/v1.5/how-to-guides/ts/golem-configure-durability-ts.mdx),
[pinned durability API](https://github.com/golemcloud/golem/blob/f93a5bd34128064c3159c6500ee808710f56ff11/docs/src/content/v1.5/develop/durability.mdx))

Golem's oplog is append-only and indexable, and its snapshot facility allows
recovery from a state image followed by only the later oplog suffix. This is
direct precedent for tying a checkpoint to a log position. The mismatch is that
Golem mediates Wasm component host calls and owns its runtime; Foldlab intends a
restricted generated Effect TypeScript language plus a separately owned model.
([pinned persistence description](https://github.com/golemcloud/golem/blob/f93a5bd34128064c3159c6500ee808710f56ff11/docs/src/content/v1.5/operate/persistence.mdx),
[pinned snapshot description](https://github.com/golemcloud/golem/blob/f93a5bd34128064c3159c6500ee808710f56ff11/docs/src/content/v1.5/develop/snapshotting.mdx))

### CID, DAG-CBOR, and CAR: identity and transport substrate

CIDv1 combines a version, content codec, and multihash into a self-describing
content identifier. DAG-CBOR constrains CBOR to IPLD kinds, CID links, and a
canonical encoding discipline. These are useful wire-substrate precedents for
versioned, typed links and deterministic bytes, but neither specifies an effect
history or replay relation. ([pinned CID specification](https://github.com/multiformats/cid/blob/9eca1c5ba064823a5ddbe13e9925f9b6c9d19c84/README.md),
[pinned DAG-CBOR specification](https://github.com/ipld/ipld/blob/f60f8dd643afae7cb0fdce885ff094b6c59490be/specs/codecs/dag-cbor/spec.md))

CARv1 transports length-prefixed IPLD blocks under root CIDs, but its
specification does not require a coherent complete DAG, does not define
deterministic archive creation, and warns that a CAR root alone must not be used
to identify the entire archive. A future export format could use CAR, but the
library would still need closure validation, block-to-CID validation, canonical
block ordering if archive-byte identity matters, and an independently defined
execution root. ([pinned CARv1 specification](https://github.com/ipld/ipld/blob/f60f8dd643afae7cb0fdce885ff094b6c59490be/specs/transport/car/carv1/index.md))

### Nix and Bazel: cache-key completeness

Nix derivations describe a builder, arguments/environment, system, outputs, and
explicit inputs. The serialized derivation has a canonical encoding, and the
common transitive closure can be content-addressed. This is precedent for
treating tools, platform, environment, and dependencies as key material rather
than hashing only user code. It is a build-step model, not a history model for
long-lived effects. ([Nix 2.28.8 derivation reference, provenance pending](https://nix.dev/manual/nix/2.28/store/derivation/),
[Nix 2.28.8 store-path reference, provenance pending](https://nix.dev/manual/nix/2.28/store/store-path/))

The Bazel Remote Execution v2 `Action` is addressed by the digest of its
serialized form and points to a `Command` and an input-root digest; it also
includes timeout, cache policy, salt, and platform fields. The cached
`ActionResult` is a separate object. The API explicitly leaves some worker
environment properties implementation-specific, which is a warning that a
syntactically complete action key may still rely on an external execution
contract. ([pinned Remote Execution API protobuf](https://github.com/bazelbuild/remote-apis/blob/becdd8f9ff811df88a22d3eadd6341753d51d167/build/bazel/remote/execution/v2/remote_execution.proto))

### rr: host-execution replay is a different layer

rr records and deterministically replays Linux process/thread executions for
debugging. It is a useful reminder that host replay may depend on executable,
OS, CPU, and trace-format conditions that are below an effect-level model. The
Foldlab history should not imply instruction replay; rr-like traces, if ever
used, would be host evidence attached to an execution. ([pinned rr README](https://github.com/rr-debugger/rr/blob/5c202cd8cb678b32107fa6aaf1c6108420bc53a8/README.md))

### Interaction Trees, Choice Trees, and Blaze: semantic precedents

The locally studied Interaction Trees revision represents potentially infinite
programs with return, silent-step, and visible-event nodes. Its interpreter is
derived from an event handler. This separation of event syntax from handler
interpretation is directly useful for a history-substitution semantics, but an
interaction tree is not a wire encoding, cache key, or execution journal.
([local pinned core](../../../.reference/clones/InteractionTrees/theories/Core/ITreeDefinition.v),
[local pinned interpreter](../../../.reference/clones/InteractionTrees/theories/Interp/Interp.v),
[paper-lock entry](../../../.reference/provenance/papers.lock.json))

Choice Trees separately represent internal and external nondeterminism and
provide transition-oriented reasoning infrastructure. That distinction is
important once a replay must separate a program's own choice from a scheduler
or environment choice. The estate has an exact arXiv v1 paper identity, but no
Foldlab model adopts its definitions in this report. ([paper-lock entry](../../../.reference/provenance/papers.lock.json),
[arXiv:2211.06863v1](https://arxiv.org/abs/2211.06863v1))

The local Blaze checkout and its paper distinguish effect labels, deep/shallow
handling, one-shot/multi-shot continuations, heap state, and primitive
concurrency. The paper also emphasizes that a captured continuation can retain
resources and that discarding or duplicating it can affect cleanup. This warns
against treating a serialized result history as a serialized continuation or
checkpoint. Blaze remains unadmitted study material here. ([local study note](BLAZE.md),
[local paper](../../../.reference/papers/relational_separation_logic_for_effect_handlers.pdf),
[DOI, provenance pending](https://doi.org/10.1145/3776676))

## Replay modes

The word “replay” should always be qualified by one of these modes. These are
design hypotheses, not final names.

| Mode | What executes | What history does | Minimum fail-closed condition | Main use |
| --- | --- | --- | --- | --- |
| Recomputation | The program and selected handlers execute again in a controlled environment | Prior history is absent or used only for comparison after execution | All inputs, dependencies, handlers, and relevant environment identities are available; live effects are permitted only by policy | Pure computation, sandboxed validation, cache rebuilding |
| History substitution | Program control code executes; matched effect outcomes are read from history and handlers do not execute | History supplies time, randomness, I/O results, failures, and decisions | Every emitted request matches the next permitted history entry, and the history is consumed exactly as policy declares | Recovery, debugging, deterministic inspection |
| Validation replay | Program control code executes and selected handlers execute against a sandbox, replica, or read-only target | Recorded and fresh normalized observations are compared | No destructive live action; comparison relation and tolerated differences are declared | Detect handler drift or model/runtime mismatch |
| Partial replay | Execution starts from a compatible checkpoint or retained history prefix and runs a suffix | Prefix is trusted only after content, closure, and compatibility checks | Checkpoint names its exact program/environment identity, decoder, and consumed history prefix; frontier dependencies are closed | Long histories, localized debugging, resume |
| Cross-version replay / migration | A new program or handler consumes old state/history through a declared adapter or relation | Old entries remain immutable; migrated views are new nodes | Version pair, migration function, accepted old forms, rejections, and observations are explicit | Code evolution and schema upgrades |

History substitution should be the default meaning of “replay” for external
effects. Recomputation against the live world is a new execution, even if it
uses the same program root. Validation replay is also a new execution and must
produce a new execution identity and witness.

## Program classes and the shape of history

### Sequential deterministic programs

For a closed, terminating program whose pure steps are deterministic, history
can be a sequence of effect interactions. Each request is matched by operation
kind, typed/canonical payload, handler contract, occurrence identity, and
position. A response can be a value, typed failure, defect, or interruption.
Final outcome alone is too weak: two executions can return the same value after
different external writes.

The initial library slice should start here. It aligns with the existing
[runtime extraction report](../../../docs/research/effect-runtime-ground-truth-extraction-scope.md),
which already recommends a serializable first-order descriptor and a
continuation machine before concurrency.

### Nondeterministic programs

Nondeterminism must be attributed:

- **program choice**: an explicit choice constructor or handler decision;
- **environment choice**: time, randomness, network response, signal arrival,
  allocation token, or mutable-service observation; or
- **implementation choice**: scheduler selection, batching, wake-up order, or
  an unspecified iteration order.

History substitution must consume the relevant choice token before the branch
is taken. If a choice is intentionally abstracted away, the model needs a set or
relation of permitted traces; replay may then accept more than one continuation
without pretending there was only one. Choice Trees are useful prior art for
keeping program and environment choice distinct, but the exact Foldlab relation
remains to be designed.

### Concurrent programs: total schedules versus causal DAGs

A total schedule records one linear order of steps. It is direct to reproduce
but overfits invisible implementation choices. A causal DAG records dependency
edges—spawn, request/response, signal delivery, join, resource conflict, and
parent/child scope—and permits independent events to be reordered.

The design hypothesis is:

- use a total order for any event whose relative order is observable under the
  declared policy;
- use causal edges for independent operations whose order is intentionally
  ignored;
- record race winners, cancellation delivery points, and external completion
  choices explicitly; and
- require an explicit conflict relation before accepting a different
  topological order.

A causal DAG is insufficient when hidden shared state can connect apparently
independent effects. A total schedule is insufficient to justify portability
across scheduler versions. Neither finite history establishes fairness or
liveness for unobserved futures.

## Candidate content-addressed graph — design hypothesis

The existing pre-grade [machine algebra](../../machine/MACHINE-ALGEBRA.md)
already explores versioned, kind-tagged canonical preimages, typed references,
closure, acyclicity, and roots. This report borrows that architectural shape as
house context only; it does not instantiate a machine kind or inherit any
theorem.

```text
ProgramRoot
  -> ProgramSyntax
  -> DependencyClosure
  -> GeneratorAndCompilerPolicy

EnvironmentRoot
  -> HandlerSet
  -> OperationSchemas
  -> RuntimePolicy
  -> NonSecretConfiguration
  -> SecretCommitmentSet (never public secret plaintext)

ExecutionRoot
  -> ProgramRoot
  -> EnvironmentRoot
  -> InputBundle
  -> HistoryRoot
  -> CheckpointSet
  -> TerminalObservation
  -> HostEvidenceSet

HistoryRoot
  -> ordered segments or causally linked event nodes
     -> Request
     -> Decision
     -> Response | TypedFailure | Defect | Interruption
     -> Scope/Finalizer events

Checkpoint
  -> ProgramRoot + EnvironmentRoot
  -> exact HistoryPrefixRoot
  -> state schema + canonical state bytes
  -> pending requests, fibers, scopes, and scheduler state if those exist

ReplayWitness
  -> source ExecutionRoot
  -> target ProgramRoot + EnvironmentRoot
  -> replay mode + observation policy
  -> consumed HistoryPrefixRoot
  -> produced observation/history root
  -> terminal status or first mismatch
  -> HostEvidenceSet
```

Every stored node should have a versioned kind, one canonical byte encoding,
typed outgoing references, a size bound, and a checked admission result.
Unknown versions, unknown kinds, non-canonical bytes, duplicate semantic slots,
dangling references, and invalid cross-kind references should be rejected.
Archive layout should not participate in semantic identity unless the archive
bytes themselves are the intended object.

### Candidate history-entry envelope

An effect interaction likely needs at least:

- execution identity and stable logical occurrence identity;
- event kind and schema revision;
- parent causal event(s) and optional total-order index;
- operation signature identity;
- handler/environment identity expected by the request;
- canonical request payload or its content reference;
- outcome discriminant: success, typed failure, defect, interruption, or
  pending;
- canonical outcome payload or its content reference;
- scope/fiber identity where relevant;
- replay policy: substitutable, validation-only, live-only, redacted, or
  forbidden;
- external receipt references and confidentiality label; and
- prior-segment/root link so truncation or reordering is detectable from the
  selected execution root.

The logical occurrence identity cannot be only “third HTTP call”: code changes
and concurrency make positional labels fragile. It also cannot be only the
request hash: two intentional identical requests must remain distinguishable.
A future contract must choose a structural address or generated stable request
identifier and test how it evolves.

## Placement matrix

Legend: **H** = content-address as canonical immutable data; **J** = record as an
execution event/outcome; **M** = represent in the project-owned semantic model;
**E** = retain as external host evidence or assumption. Several rows require
more than one placement.

| Concern | H | J | M | E | Notes |
| --- | :---: | :---: | :---: | :---: | --- |
| Accepted program syntax and named blocks | ✓ |  | ✓ |  | Never admit arbitrary closures as the program description |
| Transitive dependency closure | ✓ |  | ✓ |  | Typed references; closure checked before execution |
| Generator version, compiler config, Effect source pin | ✓ |  | ✓ | ✓ | Model the identity fields; compiler/runtime behavior remains a later bridge |
| Public input values | ✓ | start event | ✓ |  | Confidential inputs need encrypted/private storage policy |
| Operation signatures and schemas | ✓ | reference | ✓ |  | Request/result decoding is versioned and fail-closed |
| Handler implementation and non-secret configuration | ✓ | reference | ✓ | ✓ | Host deployment identity may need attestation |
| Secret plaintext | no by default | redacted reference only | abstract capability | ✓ | Hashing low-entropy secrets leaks guesses; rotation must change environment identity |
| Secret version/lease commitment | private/opaque | reference | ✓ | ✓ | Do not allow cache reuse across unknown secret contexts |
| Clock read / timer firing | result/instant encoding | ✓ | ✓ | ✓ | Distinguish logical time from host wall clock |
| Random draw / UUID | result | ✓ | ✓ | optional | Record value and generator/policy identity if validation matters |
| Network/filesystem request | request payload/reference | ✓ | ✓ | ✓ | Normalize paths, headers, redirects, metadata, and response policy explicitly |
| Network/filesystem response | response payload/reference | ✓ | ✓ | ✓ | A historical response is not a claim about current state |
| Mutable-service read/write | request/result/receipt refs | ✓ | ✓ | ✓ | Writes require idempotency/transaction policy; reads need consistency context |
| Typed failure | payload | ✓ | ✓ | optional | Must remain distinct from defect and interruption |
| Defect / unchecked host exception | normalized payload where permitted | ✓ | ✓ | ✓ | Stack strings and host objects are evidence, not portable model values |
| Cancellation / interruption | request and delivery event | ✓ | ✓ | ✓ | Record target, cause, masking state, and observed delivery point |
| Scope and finalizer lifecycle | resource token and event payloads | ✓ | ✓ | ✓ | Acquisition, registration, release attempt, release outcome, and ordering matter |
| Scheduler decision / race winner | decision token | ✓ | ✓ | optional | Needed whenever it changes an observation or continuation |
| Checkpoint state | ✓ | checkpoint event | ✓ | ✓ | Include decoder, history prefix, pending work, scopes, and scheduler state |
| Logs, metrics, traces | optional evidence blob | policy-dependent | only if observable | ✓ | Exclude by default from semantic equality |
| External receipt/signature | ✓ as bytes | reference | abstract evidence link | ✓ | Content identity is not authority; signer/trust policy remains external |
| JavaScript engine, OS, CPU, timezone, locale | manifest | start event | abstract host parameters | ✓ | Include only dimensions relevant to the declared observations |

## Fail-closed replay algorithm — design hypothesis

1. **Resolve the requested roots.** Load the program, environment, input,
   history, checkpoint, and replay-policy nodes by exact address.
2. **Check bytes before meaning.** Recompute addresses, reject unsupported hash
   or codec versions, require canonical decoding, and enforce node-size limits.
3. **Check graph admission.** Validate kinds, typed references, closure,
   duplicate slots, permitted cycles (ideally none in immutable description
   nodes), and reachability from the selected roots.
4. **Validate the program subset.** Convert the raw descriptor into the
   restricted typed program or return a clause-named rejection. Reject arbitrary
   JavaScript callbacks, custom `Effectable` implementations, reflection,
   identity-sensitive values, and unmanaged host calls.
5. **Check compatibility.** Match the program root, dependency closure,
   operation schemas, handler/environment root, observation policy, and replay
   mode. Cross-version use requires a declared migration path.
6. **Restore a state.** Start from the initial input or a checkpoint whose
   program/environment roots and exact history prefix match. Reject missing
   pending requests, scope state, fiber state, or scheduler state required by
   the selected subset.
7. **Step pure computation.** Execute only project-modeled pure transitions.
8. **At each effect request, match before consuming.** Compare operation kind,
   schema, canonical payload, handler identity, logical occurrence, and causal
   parents with the permitted next entry or frontier node.
9. **Apply the mode.** In history-substitution mode, return the recorded outcome
   without calling the handler. In validation mode, call only a policy-approved
   sandbox/read-only handler and compare normalized observations. In
   recomputation mode, create a new history and execution root.
10. **Consume explicit decisions.** Time, randomness, signals, race winners,
    cancellation delivery, and observable scheduling decisions must come from
    matched history or a newly executing handler; they may not fall through to
    ambient host behavior.
11. **Check resources and termination.** Ensure scope/finalizer events follow
    the accepted state machine. Keep success, typed failure, defect, and
    interruption distinct at the terminal observation.
12. **Check the suffix.** On complete replay, reject unconsumed history. On
    partial replay, require an explicit cut and a closed causal frontier rather
    than silently ignoring a suffix.
13. **Emit a new witness.** Record mode, all roots, consumed prefix, produced
    observations, host evidence, and either the terminal result or the first
    mismatch. The witness is immutable even when a later run uses the same
    inputs.

No mismatch should trigger a fallback to live execution. Missing history,
unknown operations, version skew, redacted required values, or unavailable
dependencies are terminal typed rejections for that replay attempt.

## Failure domains and design consequences

### Time and randomness

Wall-clock reads, monotonic timers, timer firings, random values, UUIDs, and
backoff jitter can change control flow. History substitution should return
recorded logical observations. Validation replay should not compare wall-clock
instants for equality unless the host contract defines that comparison. A
timer request and the event that wakes it are separate facts.

### Secrets and confidential inputs

Secret plaintext should not enter a public CAS by default. A handler can use an
opaque secret capability whose provider/version contributes to environment
identity, while history stores a redacted commitment or encrypted private blob.
If the secret affects an external response, substitution can replay the old
response without possessing the old secret; validation cannot. Rotation must
prevent accidental cache or witness reuse across an unknown secret context.

### Filesystems, networks, and mutable services

Paths, URLs, method, headers, body, redirect policy, consistency level,
transaction token, and response normalization are part of the effect contract,
not incidental strings. Reading a file by path without recording bytes and
metadata is not replayable after mutation. Reissuing a write after an
ambiguous timeout may duplicate the external action.

For writes, the library should require at least one of:

- a cooperating external idempotency key with an explicit retention window;
- a transaction/compare-and-set protocol whose receipt can be checked;
- a compensating protocol whose repeated behavior is modeled; or
- a policy that marks the operation live-only and forbids substitution as a
  claim about current state.

Temporal's guidance treats retried Activities as requiring idempotent external
behavior, and Golem exposes an idempotence mode plus durable idempotency keys.
Restate's request deduplication also has a configured retention period. These
are evidence that durable runtimes rely on scoped protocols, not on a history
hash alone. ([pinned Temporal deterministic-constraints page](https://github.com/temporalio/documentation/blob/4d6668766030e4ed17f197a9d9e93566ba3a77db/docs/encyclopedia/workflow/workflow-definition.mdx),
[pinned Golem durability controls](https://github.com/golemcloud/golem/blob/f93a5bd34128064c3159c6500ee808710f56ff11/docs/src/content/v1.5/develop/durability.mdx),
[Restate retention documentation, provenance pending](https://docs.restate.dev/services/configuration))

“Exactly once” must therefore be scoped to a named protocol and retention
window. A CAS can deduplicate identical bytes; it cannot prevent an external
server from applying the same payment twice after an acknowledgment is lost.

### Failures, defects, interruption, and cancellation

The pinned Effect source distinguishes typed failure, defect, and interruption
inside `Cause`, and the local runtime report records that finalization changes
how causes combine. Replay must not collapse these into one error string.
([pinned `Cause.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cause.ts),
[local runtime study](../../../docs/research/effect-runtime-ground-truth-extraction-scope.md))

Cancellation request, masking state, delivery point, child propagation, and
the outcome after cancellation are different events. A replay that delivers
cancellation at a new pure step is a different schedule unless the observation
policy intentionally hides that distinction.

### Finalizers and resources

Acquisition success, finalizer registration, body outcome, release attempt,
release outcome, and close order must be modeled separately. A checkpoint that
contains an open resource cannot serialize the live handle; it needs a durable
resource token and a resume/reacquire policy, or it must be rejected. Replaying
a release against the live world is unsafe unless the handler's idempotency
contract permits it. Blaze's continuation/resource warning reinforces that a
captured control state is not just a value snapshot. ([local Blaze paper](../../../.reference/papers/relational_separation_logic_for_effect_handlers.pdf))

### Cache-key completeness and version skew

At minimum, a cache or replay compatibility key should cover the accepted
program form, dependency closure, generator, Effect revision, TypeScript
compiler/configuration where emitted code matters, operation schemas, handler
set, non-secret configuration, host policy, input, and observation policy.
Omitting a locale, timezone, iteration-order rule, redirect policy, or mutable
service revision is acceptable only when the model excludes it from
observation.

Old histories are immutable. Cross-version replay creates a new witness that
names old and new identities and the adapter/relation used. A decoder that
silently accepts unknown fields, a handler that reinterprets an old operation
tag, or a checkpoint loaded under a different state schema must fail unless a
reviewed migration explicitly covers the case.

### History corruption, authenticity, and availability

Address verification detects bytes that do not match the selected root. It
does not identify who selected that root, whether a receipt is genuine, or
whether a complete history was ever published. Signed roots, trusted
checkpoint manifests, quorum receipts, and external service attestations are
host-evidence concerns.

Truncation is detected only when an expected terminal/root commitment is known.
A valid shorter history may simply be a different object. Semantic admission
must also reject impossible state transitions even when every block hash is
correct.

### Garbage collection and reachability

Immutable nodes can still become unreachable. Mutable root sets should pin
execution roots, legal/audit holds, active checkpoints, migration inputs, and
replay witnesses. Collection should follow typed references from these roots.
History chunking and skip indexes may improve access, but deleting a prefix
needed by a checkpoint invalidates replay unless the checkpoint is declared a
self-contained replacement under an explicit retention rule.

Secret leases and remote receipts may expire even while their byte references
remain. Availability status is therefore mutable metadata outside the immutable
execution graph.

## Scenarios

### Positive examples

1. **Pure invoice calculation.** A closed integer/record program with no
   effects is recomputed from a program root and input root. A cache result is
   reused only when the generator and dependency closure match.
2. **Recorded exchange-rate read.** The program emits a typed `Rate.get` request.
   History substitution matches currency pair, handler contract, occurrence,
   and recorded response, then continues without network access.
3. **Deterministic random workflow.** Each random draw is a distinct recorded
   decision. Replaying consumes the old draws; recomputation with a seed is a
   separate mode with a separately identified generator.
4. **Checkpointed sequential job.** A checkpoint names the program/environment
   roots and history prefix after step 1,000. Replay validates it and consumes
   only the suffix from 1,001 onward.
5. **Independent concurrent reads.** Two reads share a spawn parent and join
   child but no conflict edge. A causal replay may accept either completion
   order only if the declared observation ignores order and the join result is
   keyed by branch rather than completion position.

### Boundary cases

- The same HTTP request returns a changed body: substitution returns the old
  body; validation reports a mismatch; live recomputation creates a new history.
- A secret rotated but history has a recorded response: substitution may
  continue without the secret, while validation is unavailable.
- A race has the same final value under two winners: the winner still matters
  if cancellation or finalizers differ.
- A checkpoint restores values but omits an open scope: reject it.
- History contains a typed failure but new code catches a broader defect:
  cross-version replay requires an explicit relation rather than positional
  reuse.
- Two identical writes have the same request bytes: occurrence identity keeps
  them distinct.

### Forbidden cases for the initial library

- hashing or ingesting an arbitrary `Effect` value containing JavaScript
  closures and treating the hash as program identity;
- direct `Date.now`, `Math.random`, filesystem, network, environment-variable,
  or mutable-global access outside a modeled handler;
- replay that falls back to a live handler when an entry is missing;
- validation replay of payment, email, deletion, or other destructive actions
  without a sandbox or explicit external idempotency/transaction contract;
- public CAS storage of plaintext credentials or low-entropy secret hashes;
- checkpoint restore with unknown schema, program root, handler set, pending
  fibers, or scope state;
- concurrency replay that changes a race winner or conflict order without an
  explicitly permitted trace relation; and
- garbage collection based only on age while retained execution roots still
  reference the data.

## Counterexamples to tempting overclaims

| Tempting statement | Counterexample |
| --- | --- |
| “Same program CID means same result.” | The handler reads current time or a mutable database. |
| “Same effect names mean the same execution.” | Two identical `charge` requests occur intentionally; occurrence and outcome differ. |
| “Same final `Exit` means the replay matched.” | One execution sent an email and the other skipped it before returning the same value. |
| “A complete result history identifies the handler.” | Two handlers can return the same sampled results while differing elsewhere. |
| “Content-addressed history is authentic.” | An attacker can publish a self-consistent history under a new root. |
| “A CAR root identifies a complete replay bundle.” | CARv1 permits blocks unrelated to roots and does not require complete graph closure. |
| “A causal DAG allows every topological order.” | Two requests share hidden mutable state not represented by a conflict edge. |
| “A retry plus CAS gives exactly-once external behavior.” | The server commits a payment, the acknowledgment is lost, and the retry uses no cooperating idempotency key. |
| “A snapshot can replace all prior history.” | An audit or migration needs the original request that the state image erased. |
| “Old history can run under new code if decoding succeeds.” | New code changes command order or finalizer behavior while accepting the old payload shape. |
| “Hashing every declared input makes the cache key complete.” | The handler also depends on timezone or an unrecorded service deployment. |

## Candidate Lean obligation families

These are questions for a future formalization-strategy pass, not theorem
statements or approved names.

1. **Canonical bytes and addresses:** canonicalization idempotence; encoder
   injectivity on canonical forms; decoder rejection of non-canonical forms;
   kind/version separation; every address theorem states its hash premise.
2. **Graph admission:** typed-reference closure; no dangling dependencies;
   required acyclicity; root reachability; deterministic reporting of each
   rejection clause.
3. **Descriptor admission:** raw descriptions validate to well-typed programs;
   generated blocks reference only accepted operations and serializable values;
   unsupported source forms receive stable rejections.
4. **Pure machine:** configuration well-formedness across steps; progress or an
   explicit stuck result; termination only for the admitted finite fragment;
   deterministic terminal result for the sequential deterministic fragment.
5. **History formation:** append/prefix discipline; unique logical occurrences;
   request/outcome schema agreement; permitted state transition for every entry
   kind; terminal events exclude later ordinary entries.
6. **History substitution:** a matched request consumes exactly its permitted
   entry; substitution does not invoke a live handler; complete replay consumes
   exactly the declared history; mismatch produces a typed rejection.
7. **Replay observations:** the direct event semantics and replay machine expose
   a declared relation over traces, not merely final values; each replay mode
   has a separate judgment.
8. **Checkpoint restoration:** encoding/decoding round trip for modeled state;
   restored state corresponds to the named history prefix; pending requests,
   scopes, and scheduler state are complete for the admitted fragment.
9. **Partial replay:** the cut is prefix-closed or causal-frontier-closed; every
   suffix dependency is either in the checkpoint or retained graph.
10. **Nondeterminism:** internal and external choices have distinct labels;
    substitution consumes a recorded choice; permitted trace sets are explicit.
11. **Concurrency:** causal edges are acyclic; every accepted linearization
    respects dependencies and conflicts; branch identity survives completion
    reordering; races consume an explicit winner decision.
12. **Cancellation and resources:** interruption state transitions are legal;
    scope close is idempotent in the model; finalizer dispatch/order and cause
    combination match the selected contract; crash gaps remain explicit.
13. **Migration:** each accepted old/new version pair names a total adapter on
    its admitted old domain or a typed rejection; migrated replay creates a new
    witness and never mutates old nodes.
14. **Collection:** tracing from retained roots keeps every required typed
    reference; a collection decision cannot leave a retained checkpoint or
    replay witness dangling.
15. **Witness binding:** a replay witness commits to mode, policies, identities,
    consumed history, produced observation, and host evidence; no field can be
    changed without changing the witness address.

The first formal slice should avoid concurrency, divergence, arbitrary
callbacks, services with live state, and checkpoints. It should establish the
description/address/history seams on a small terminating request language
before adding more runtime behavior.

## Candidate TypeScript / Effect seams

The public TypeScript surface should be generated from a serializable,
first-order program description. The generator—not an extractor for arbitrary
closures—should emit public Effect combinators. The pinned Effect implementation
already distinguishes public constructors/combinators from its open internal
evaluator protocol, which is why arbitrary runtime `Effect` objects are the
wrong CAS boundary. ([pinned public `Effect.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts),
[pinned internal core](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts),
[local extraction report](../../../docs/research/effect-runtime-ground-truth-extraction-scope.md))

Candidate module seams, still unratified:

- **Descriptor and validator:** raw versioned data to accepted typed descriptor
  or clause-named rejection.
- **Canonical codec and address service:** pure canonical bytes, node kind,
  typed references, and address calculation; hash implementation remains an
  injected boundary.
- **Generator:** accepted descriptor to valid TypeScript using the pinned
  Effect API; emitted source and compiler configuration get their own identity.
- **Operation schema registry:** one request/result/failure schema per admitted
  effect operation, with explicit revision compatibility.
- **Handler registry:** operation implementation plus handler/environment
  identity; separate live, substitution, and validation implementations.
- **History store:** append-only logical interface with content-addressed
  segments/nodes, explicit execution roots, and typed corruption outcomes.
- **Replay controller:** phase and mode selection, request matching, history
  consumption, first-divergence reporting, and a hard prohibition on implicit
  live fallback.
- **Clock and randomness capabilities:** all time/random decisions cross an
  operation boundary rather than ambient JavaScript APIs.
- **Filesystem/network/mutable-service capabilities:** typed request/response
  envelopes, normalization policy, confidentiality, receipt, and idempotency
  metadata.
- **Cause bridge:** retain success, typed failure, defect, and interruption as
  distinct cases rather than stringifying Effect `Cause`.
- **Scope/resource bridge:** explicit resource tokens and lifecycle entries;
  `acquireRelease`-style generated programs only after the resource contract is
  modeled against the pinned public source.
- **Scheduler/fiber bridge:** absent from the first slice; later expose explicit
  decisions and traces rather than promising host task-order identity.
- **Checkpoint codec:** absent until all modeled live state has an owned
  serialization and restoration policy.
- **Host evidence adapter:** compiler, engine, OS, external receipt, signature,
  and validation-run metadata; never imported into the pure semantic core.

The runtime conformance path remains the existing layered one: model laws are
about project-owned definitions; source extraction, generated Effect behavior,
emitted JavaScript, and hosted execution are separate bridges and claim gates.

## Staged recommendation for `library/effects`

### Stage R0 — ratify the boundary before code

- Decide the exact replay observations and the accepted meaning of each replay
  mode.
- Choose the program-description equality, occurrence identity, and secret
  posture.
- Grill positive, negative, boundary, and counterexample scenarios.
- Add external pins only through the Source Provenance process.

Exit: an approved domain contract and declaration/obligation ledger; this
research draft remains an input, not the contract.

### Stage R1 — sequential closed CAS core

- Admit only finite values, named total blocks, `succeed`, typed `fail`, and
  sequential composition/recovery.
- Define versioned node kinds for program, dependency closure, input, and final
  observation.
- Generate Effect TypeScript; do not ingest arbitrary TypeScript.

Exit: canonical codec/address obligations and generated-code fixtures pass for
the closed no-external-effect subset.

### Stage R2 — sequential request/history substitution

- Add a small typed request language with deterministic control flow.
- Record request and success/typed-failure outcomes.
- Implement substitution replay with exact consumption and no live fallback.

Exit: model obligations cover request matching, prefix consumption, terminal
outcomes, and mismatches; runtime fixtures remain separately labeled evidence.

### Stage R3 — volatile reads and validation

- Add logical clock, randomness, and one read-only external service.
- Separate substitution from sandboxed validation replay.
- Add confidentiality labels, receipt references, and environment identity.

Exit: examples demonstrate changed-world mismatch, secret rotation, corrupted
history, and incomplete cache keys.

### Stage R4 — defects, interruption, and sequential resources

- Add defect/interruption causes, masking/delivery events, scopes, acquisition,
  and sequential finalizers.
- Reject checkpoints and live resource replay until durable tokens exist.

Exit: cause branches and resource lifecycle have explicit model obligations and
negative fixtures for duplicate/missing release.

### Stage R5 — checkpoints and retention

- Add canonical modeled-state snapshots tied to exact history prefixes.
- Add reachability roots, retention policy, collection reports, and partial
  replay frontier checks.

Exit: collection cannot strand a retained execution/checkpoint in the modeled
graph, and every incompatible checkpoint is rejected by a named clause.

### Stage R6 — nondeterminism and concurrency

- Add explicit choice tokens before fibers.
- Then add spawn/join, causal edges, conflicts, race winners, cancellation, and
  scheduler policy in bounded scenarios.
- Compare total-schedule and causal-DAG observations before selecting one public
  contract.

Exit: the declaration review fixes which reorderings are permitted; no host
scheduler conclusion is inferred from bounded tests.

Cross-version migration should begin only after two real schema/program
revisions exist. Exactly-once language should remain prohibited unless it names
the external protocol, key scope, retention window, and failure boundary.

## Source ledger

No row below was added to a Source Lock by this pass.

| Source | Stable revision/version | Claim supported here | Mismatch with Foldlab target | Provenance status |
| --- | --- | --- | --- | --- |
| [Effect-TS/effect](https://github.com/Effect-TS/effect/tree/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07) | commit `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, package `4.0.0-rc.111` | Public/internal seam; Cause distinctions; runtime is open to evaluator objects | Subject implementation, not the project-owned model or replay contract | Existing estate Source Lock; no new entry |
| [Unison repository](https://github.com/unisonweb/unison/tree/84b95a623711b57b9ff7163f124b214d626b81e4) | commit `84b95a623711b57b9ff7163f124b214d626b81e4` | Content-addressed code/AST and dependency-closure precedent | No Foldlab execution-history relation; web ability/distribution pages not pinned | Revision resolved during research; Source Lock pending |
| [Temporal documentation](https://github.com/temporalio/documentation/tree/4d6668766030e4ed17f197a9d9e93566ba3a77db) | commit `4d6668766030e4ed17f197a9d9e93566ba3a77db` | Event History, command matching, deterministic constraints, versioning | Ordered workflow service history, not CAS graph or Effect subset | Revision resolved during research; Source Lock pending |
| [Restate service protocol](https://github.com/restatedev/service-protocol/tree/eaebc104834cf3405267ec180912b0e295340501) | commit `eaebc104834cf3405267ec180912b0e295340501` | Invocation journal; replay/processing phase ownership; indexed completions | Runtime protocol, not program identity or formal Effect semantics | Revision resolved during research; Source Lock pending |
| [Golem](https://github.com/golemcloud/golem/tree/f93a5bd34128064c3159c6500ee808710f56ff11) | commit `f93a5bd34128064c3159c6500ee808710f56ff11`, v1.5 docs paths | Oplog replay, live/replay split, persistence, snapshots | Golem-owned Wasm runtime and host mediation | Revision resolved during research; Source Lock pending |
| [CID specification](https://github.com/multiformats/cid/tree/9eca1c5ba064823a5ddbe13e9925f9b6c9d19c84) | commit `9eca1c5ba064823a5ddbe13e9925f9b6c9d19c84`, CIDv1 | Versioned codec + multihash identifier precedent | Identifier format only; no graph admission or replay | Revision resolved during research; Source Lock pending |
| [IPLD specifications](https://github.com/ipld/ipld/tree/f60f8dd643afae7cb0fdce885ff094b6c59490be) | commit `f60f8dd643afae7cb0fdce885ff094b6c59490be`, DAG-CBOR draft, CARv1 final | Canonical linked data and archive transport boundaries | CAR does not require complete DAGs or deterministic archives | Revision resolved during research; Source Lock pending |
| [Nix reference manual](https://nix.dev/manual/nix/2.28/store/derivation/) | manual `2.28.8` as retrieved | Explicit derivation inputs/system and canonical derivation encoding | Build derivations, not effect histories; manual bytes not locked | Versioned URL; Source Lock pending |
| [Bazel Remote APIs](https://github.com/bazelbuild/remote-apis/tree/becdd8f9ff811df88a22d3eadd6341753d51d167) | commit `becdd8f9ff811df88a22d3eadd6341753d51d167`, REAPI v2 schema | Action digest, command/input root, platform, separate ActionResult | Remote build execution; some worker environment remains external | Revision resolved during research; Source Lock pending |
| [rr](https://github.com/rr-debugger/rr/tree/5c202cd8cb678b32107fa6aaf1c6108420bc53a8) | commit `5c202cd8cb678b32107fa6aaf1c6108420bc53a8` | Host process/thread record-replay as a distinct evidence layer | Linux debugger trace, not effect protocol or portable CAS history | Revision resolved during research; Source Lock pending |
| [Interaction Trees checkout](../../../.reference/clones/InteractionTrees) | commit `68b3568d3f0f48c057192c58c8db88ef4412747a`; papers `arXiv:1906.00046v2` and DOI `10.1145/3371119` | Event syntax, handlers/interpreters, recursive computations | Rocq semantic library, not serialization or Effect correspondence | Paper identities in paper lock; checkout is local study material |
| [Choice Trees paper](https://arxiv.org/abs/2211.06863v1) | `arXiv:2211.06863v1`, SHA-256 recorded in paper lock | Internal/external nondeterminism distinction | No adopted Lean model or CAS representation | Existing paper-lock identity |
| [Blaze checkout](../../../.reference/clones/blaze) | commit `76cf4cb0e7d68fc71f17eed539b411b194c9ca38` | Handler dimensions, continuations, resources, state, concurrency | Rocq/Iris language and logic, not Effect TypeScript | Local exact commit; Source Lock pending |
| [A Relational Separation Logic for Effect Handlers](../../../.reference/papers/relational_separation_logic_for_effect_handlers.pdf) | DOI `10.1145/3776676`; local 29-page PDF | Relational handler/resource/concurrency precedent | No adopted Foldlab judgment; paper admission unresolved | Local-only copy and extraction; paper-lock/catalog pending |

## Checks and deliberate omissions

- Local Markdown-link check: all 15 repository-relative link targets in this
  file exist as of the snapshot date.
- A direct trailing-whitespace scan reported no affected lines.
- The primary repositories above were resolved read-only to the full revisions
  in the source ledger; no repository was cloned and no dependency was
  installed or executed.
- Main-agent review revalidated the pinned Unison, Temporal, archived Restate,
  Golem, CID, CARv1, Bazel Remote API, and rr links through an independent
  network read. Live web documentation not tied to those revisions remains
  provenance pending; no estate receipt was created.
- No build or theorem check was run because this pass writes research prose
  only and makes no code or formal change.
- No research-index, context, claim-gate, source-lock, paper-lock, catalog,
  machine, or project file was changed.

## Open decisions for the next ratification pass

1. Is execution identity the address of an execution manifest, or a separate
   nonce plus a manifest address?
2. What is the smallest stable logical occurrence identity across generated
   code refactors?
3. Which observations are ordered sequences, which are causal graphs, and
   which are intentionally ignored?
4. Does a handler identity cover implementation bytes, deployment attestation,
   configuration, or all three as linked nodes?
5. Which secret-version commitments are safe to store and compare?
6. What external effect classes are substitution-safe, validation-safe,
   live-only, or forbidden?
7. What is the first checkpointable state, and what resource states make a
   checkpoint inadmissible?
8. Which hash/codec collision premises belong in the model, and which remain
   host assumptions?
9. What mutable roots and retention rules govern history collection?
10. Which cross-version changes require migration, and which must always start
    a fresh execution?

Until those decisions are grilled and ratified, this report licenses only the
staged research direction above. It does not license public claims about CAS
replay, generated Effect behavior, or the broader effects system.
