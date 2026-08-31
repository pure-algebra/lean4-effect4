# Effect services derived from content-addressed values

Status: conception-mode research draft

Snapshot: 2026-08-27

Claim posture: **G0/G1-unadmitted design hypotheses**

This report is forward-looking input for `library/effects`. It is not a domain
contract, vocabulary ratification, public API freeze, implementation claim, or
proof submission. Names in code blocks are illustrative. The ratified
[Effect Replay context](../../../docs/effect-replay/CONTEXT.md), the current
[implementation plan](../IMPLEMENTATION-PLAN.md), and the frozen M1 TypeScript
interfaces remain authoritative.

The exact Effect subject is the estate-pinned
[`effect@4.0.0-rc.111`](https://github.com/Effect-TS/effect/tree/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07)
at commit `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`. Additional file identities used
here are recorded in the
[research receipt](../../../.reference/provenance/receipts/effect-service-cas-derivation-sources.json).
Effect's `unstable/*` modules are studied only as version-sensitive prior art.

## Question

How can the Effect Replay library make it easy for a user to:

1. project an ordinary typed domain value into an admitted CAS graph and read
   it back;
2. construct an existing user-defined Effect service from an exact CAS root;
3. construct a service whose immutable configuration or indexes come from CAS
   while live authorities remain ordinary Effect dependencies; and
4. use the same programming model whether `CasStore` is in memory, on disk, or
   a remote authenticated service?

The central recommendation is a three-part seam:

```text
explicit value/graph descriptor
        A <-> typed CAS root
                  |
                  v
effectful hydration recipe
        typed CAS root -> Layer<UserService>
                  |
                  v
ordinary Effect composition
        LayerMap for dynamic roots, replayable for record/replay,
        HttpClient/Cache/RequestResolver inside remote adapters
```

The important negative recommendation is equally strong: do not attempt to
serialize a service implementation, JavaScript closure, `Context`, `Layer`,
HTTP client, credential, scope, or open resource. Persist the immutable data
and the explicit recipe identity; construct the service through Effect.

## Existing seam and the missing bridge

The current library already separates the right responsibilities:

- [`CasStore`](../src/CasStore.ts) is the minimal logical store service: `put`
  admits and stores one canonical node, while `load` returns a reverified node.
- [`OperationDescription`](../src/Operation.ts) explicitly describes each
  replayable method; reflection is insufficient.
- [`replayable`](../src/ServiceAdapter.ts) separates a public service tag from
  an internally minted live role. Record construction needs the live role and
  `Replay`; replay construction needs only `Replay`.
- [`session`](../src/Replay.ts) owns replay history and keeps CAS failures
  distinct from replay mismatch categories.

What is absent is a typed bridge above raw `CasNodeInput`:

```text
domain value --?--> admitted node graph --CasStore--> root ContentId
root ContentId --?--> domain value --?--> Context service implementation
```

The bridge should be explicit because the graph layout, child order, kind
versions, migration rules, and canonical payload codec participate in content
identity. Effect `Schema` can validate and encode domain components, but its
default JSON encoding remains excluded from the CAS digest pre-image by the
ratified contract.

## Five identities that must remain separate

| Identity | Example | Where it belongs |
| --- | --- | --- |
| Content identity | `ContentId` of a canonical node or graph root | CAS node scheme and store |
| Projection identity | descriptor id, revision, root kind, graph-layout rules | explicit data-to-graph descriptor |
| Service role identity | `Context.Service` string key and TypeScript service shape | Effect `Context` and `Layer` |
| Live deployment identity | endpoint, tenant, credentials, consistency policy, mutable head | Effect dependencies and host evidence |
| Replay occurrence/history identity | execution id, index, history root, decision trace | Replay session and witness |

Equal service shapes do not imply equal projection rules. Equal content roots
do not identify the service factory or live authorities. A service tag does not
identify its current implementation. A replay history does not imply the same
CAS-backed service configuration was used unless that root is explicitly
carried by a request or a future session dependency manifest.

Effect's `Context.Service` uses its string key as runtime identity, and reusing
the same string aliases slots
([pinned `Context.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Context.ts#L161-L204)).
That key is therefore a dependency-injection identity, not content identity.

## Proposed surface 1: an explicit value/graph descriptor

The first ergonomic object should describe how one domain value maps to one
typed root and its reachable nodes. For discussion, call it a **CAS projection
descriptor**; this is not minted vocabulary.

An illustrative user surface is:

```ts
const UserProfileCas = Cas.value({
  id: "acme/UserProfile",
  revision: 1,
  rootKind: { version: 1, tag: 32 },
  schema: UserProfile,
  canonicalCodec: UserProfileBytes
})

const ref = yield* UserProfileCas.put(profile)
const sameProfile = yield* UserProfileCas.get(ref)
```

The simple `Cas.value` constructor would cover a single node whose payload is a
canonical byte encoding. A graph constructor would make child boundaries and
their order explicit:

```ts
const ProjectCas = Cas.graph({
  id: "acme/Project",
  revision: 1,
  rootKind: ProjectRootKind,
  root: ProjectHeaderBytes,
  children: {
    owner: UserProfileCas,
    documents: Cas.ordered(DocumentCas)
  }
})
```

This is intentionally not automatic Schema-AST traversal. A Schema field edit
must not silently change graph partitioning or reference order. Defaults can
make leaf values easy; graph boundaries remain authored and versioned.

### Typed roots

A branded `ContentId` alone cannot express the expected root kind at compile
time. A lightweight phantom wrapper can improve ordinary TypeScript use:

```ts
type CasRef<P> = {
  readonly id: ContentId
  readonly projection: P
}
```

The runtime must still check the node's version and kind. The phantom type is
an ergonomic guard, not evidence. A serialized reference retains the full
address and declared expected kind according to the ratified node format.

IPLD Schema links are useful cautionary prior art: a destination type attached
to a link is a hint, while strict validation happens only after following and
decoding the link
([official link documentation](https://ipld.io/docs/schemas/features/links/),
live page; exact site bytes pending provenance). Foldlab's current admission
rule is stronger: the expected kind must be checked at the store boundary, not
trusted from the TypeScript type parameter.

### Effect Schema integration

Effect v4 transformations can be bidirectional, effectful, and service-requiring
([pinned `SchemaTransformation.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/SchemaTransformation.ts#L143-L296)),
and `Schema.decodeEffect`/`encodeEffect` expose those service requirements.
That makes Schema a good boundary component for leaf payload validation and
typed error reporting.

It should not, however, make remote graph traversal an invisible Schema decode
by default. Loading a graph has CAS-specific concerns that a value codec does
not expose: closure, kind-typing, total-node and byte budgets, duplicate
suppression, transport failures, authorization, and migration. The preferred
split is:

```text
Schema                    validates a node payload or domain component
CAS projection descriptor owns graph layout and descriptor revision
CasStore                  admits and loads canonical nodes
descriptor get/put        orchestrates graph traversal through CasStore
```

### Effect `Graph` as an internal materialized-closure tool

The newly added Effect v4 `Graph` module is a useful implementation candidate,
but at a narrower seam than `CasStore`. It provides immutable directed graphs,
cycle witnesses and checks, topological traversal, depth-first post-order
traversal, and validated snapshot import/export
([pinned `Graph.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L443-L555),
[cycle operations](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L4090-L4220),
[traversals](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L8021-L8290)).
For the natural CAS orientation `parent -> referenced child`,
`dfsPostOrder(root)` emits children before their parent and can therefore plan
root-last upload. `topo` emits predecessors before dependents, so with that
orientation it gives parent-first order; upload would need reversed topological
order or the post-order traversal. Neither traversal itself establishes the
CAS invariants. Where a materialized view is required to be a DAG, post-order
planning should follow an explicit acyclicity check.

That DAG condition is a prospective strengthening, not merely an
implementation choice hidden by `Graph`. The current Lean
[`Store.Closed`](../Effects/Cas/Store.lean) predicate says that every resident
reference resolves at its declared kind, and
[`checkRefs`](../Effects/Cas/Admission.lean) checks those same two clauses at
`put`; neither declaration contains an explicit acyclicity clause. A store
reached only by fresh, immutable, children-first insertion may have a DAG
construction argument, but that judgment and its preservation theorem have not
been frozen. If cycles are to be rejected for all admitted stores, Pass A must
name the judgment and the Lean/runtime obligations must state it directly.

This suggests an internal checked wrapper, provisionally called `CasDag` or a
**materialized closure**. Its constructor would accept only a fully loaded view
and establish all of the following before exposing traversal:

- the graph is directed and immutable, with one separately designated root;
- every node is reachable from the root and no unrelated node is included;
- each node has one reverified full `ContentId`, and those identities are
  unique in the view;
- every graph edge corresponds to exactly one ordered typed reference in its
  source node, with matching target address and kind;
- no declared reference or graph edge is missing or extra;
- the closure is acyclic when required; and
- node, byte, depth, fan-out, and traversal-work budgets hold.

Raw `Graph` does not establish any of these conditions. A directed Graph may
contain cycles. Its `NodeIndex` is a numeric allocation identifier rather than
a `ContentId`
([pinned definition](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L41-L49)).
It has no distinguished root, kind-typed edge rule, reachability rule,
canonical labeling, or address verification.

The pinned `Schema.Graph` codec faithfully encodes the graph snapshot's numeric
node and edge indexes and endpoint indexes
([pinned Schema block](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Schema.ts#L11245-L11512)).
Its decoder checks safe increasing indexes and valid endpoints, but deliberately
supports isolated nodes, self-loops, parallel edges, and cycles. Allocation and
index order therefore affect the snapshot bytes. A raw `Schema.Graph` snapshot
must not become CAS identity or durable graph transport without a separate
canonical relabeling rule. The safer initial design derives an internal Graph
view from already admitted CAS nodes and discards the numeric indexes at the
boundary.

`Map<ContentId, CasNodeInput>` remains the better point-lookup representation
for a store or admitted-node cache. The Graph view is useful only after a reachable
closure (or an explicitly partial subgraph) has been materialized. This matters
especially for a remote store: it normally exposes exact-address partial views,
not one authoritative in-memory graph. Consequently raw `Graph` should not be
the public service type, the `CasStore` representation, or a user-visible root
identity in the initial ergonomic API.

### `PrimaryKey` is not a content identifier

Effect's `PrimaryKey` protocol is only a method returning a string; its guard
checks the property but does not call it or verify the returned string
([pinned `PrimaryKey.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/PrimaryKey.ts#L27-L123)).
The unstable `Persistable` surface combines that key with success and failure
Schemas to persist request `Exit` values
([pinned `Persistable.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/persistence/Persistable.ts#L32-L159)).

That is useful API-shape prior art—identity plus explicit Schemas—but a
`PrimaryKey` must never be accepted as a `ContentId`. A content identifier is
recomputed from admitted canonical bytes under the hash-hypothesis lattice. A
`ContentId` returned by successful node admission or load reverification may be
used as a cache key string; the direction does not reverse.

## Proposed surface 2: exact root to user service `Layer`

The most Effect-idiomatic service constructor is a `Layer.effect` whose
acquisition loads and validates the immutable value, then returns the user's
ordinary service implementation. Effect's layer constructors retain typed
construction errors and required services while providing scope and sharing
([pinned `Layer.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Layer.ts#L807-L1077)).

An illustrative helper is:

```ts
const CatalogFromCas = Cas.service({
  service: Catalog,
  projection: CatalogSnapshotCas,
  make: (snapshot) => Catalog.of({
    find: (id) => Effect.succeed(snapshot.items.get(id))
  })
})

const CatalogLive = CatalogFromCas.layer(snapshotRef)
// Layer<Catalog, CasHydrationError, CasStore>
```

The helper does not serialize `Catalog`. It stores `CatalogSnapshot`, reads it
at layer acquisition, and invokes an authored factory.

### Why eager hydration should be the default

Eager hydration has an important type-level advantage for existing services.
Remote/CAS errors occur while the layer is built, so methods retain their
original caller-facing error unions. A lazy service must either:

- already include CAS/transport errors in each affected method;
- translate those errors into an existing truthful domain error; or
- hide them as defects, which is not an acceptable generic default.

Therefore the first ergonomic surface should load a bounded graph at layer
acquisition. A later explicit lazy constructor may provide a `CasHandle<A>` or
resolver to services whose declared methods admit storage failures.

### Lazy typed access for large remote graphs

Eager hydration is not appropriate when the root reaches a very large graph or
the service needs only a small, request-dependent portion. That case should use
an explicit typed repository/handle rather than make `Cas.service` silently
lazy:

```ts
const Documents = Cas.repository(DocumentCas)

const SearchFromCas = Cas.serviceLazy({
  service: SearchService,
  root: ProjectCas,
  make: (projectRoot, resolve) => SearchService.of({
    findDocument: (documentRef) => resolve.get(Documents, documentRef)
  })
})
```

The names are illustrative. The semantic point is that affected methods now
perform CAS reads, so their declared error channels must admit presence,
transport, integrity, and interruption-relevant failures or translate them to
truthful domain errors. The resolver can use the layer-owned admitted-node
cache and remote batching without changing the domain model. It should expose
typed roots and projection descriptors, not raw `ContentId -> unknown` lookup.

This gives three distinct ergonomic modes:

| Need | Surface | Failure time | Graph materialization |
| --- | --- | --- | --- |
| One bounded immutable service snapshot | eager `Cas.service(...).layer(ref)` | layer acquisition | complete checked closure |
| Request-dependent portions of a large remote graph | explicit typed repository/handle | service method | lazy verified subgraph |
| Many dynamically selected service roots | `LayerMap` around either recipe | keyed layer acquisition or method | per selected recipe |

Effect `Graph` is naturally available in the first mode and for explicit bulk
operations. A lazy resolver should not pretend that a partially observed remote
store is already one complete `Graph`.

### Effectful factories and hybrid services

The factory may itself be effectful and request ordinary Effect services:

```ts
const AccountFromCas = Cas.service({
  service: AccountService,
  projection: AccountRulesCas,
  make: (rules) => Effect.gen(function*() {
    const billing = yield* BillingClient
    const audit = yield* AuditLog

    return AccountService.of({
      quote: (input) => rules.quote(input),
      charge: (input) => billing.charge(rules.apply(input)),
      audit: (event) => audit.append(event)
    })
  })
})

const AccountLayer = AccountFromCas.layer(rulesRef)
// Layer<AccountService, CasHydrationError, CasStore | BillingClient | AuditLog>
```

The immutable `rules` value may participate in content identity. `BillingClient`,
credentials, clocks, open connections, mutable audit state, and their scopes do
not. They remain visible layer requirements.

### Dynamic resolution by root: use `LayerMap`

When the root is selected at runtime—for example one catalog per tenant,
dataset, model, or revision—the pinned Effect v4 `LayerMap` is a close fit. It
turns a key into a cached scoped service context, exposes a `Layer` or scoped
effect, supports idle TTL, and permits invalidation
([pinned `LayerMap.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/LayerMap.ts#L1-L175)).

```ts
class CatalogAt extends LayerMap.Service<CatalogAt>()(
  "acme/CatalogAt",
  {
    lookup: (root: ContentId) => CatalogFromCas.layer(root),
    idleTimeToLive: "10 minutes"
  }
) {}

const programAtRoot = program.pipe(
  Effect.provide(CatalogAt.get(root))
)
```

This should be a documented composition recipe before Foldlab wraps it in a
new abstraction. It is appropriate for a family of scoped services. It is not
needed for one fixed application root, where one named layer value obtains
ordinary Effect layer memoization.

Use a stable primitive `ContentId` string as the `LayerMap` key. If a compound
key includes endpoint or tenant, it needs deliberate equality and must not
contain secret material. Credential rotation should invalidate the affected
entry rather than change content identity.

## Alignment with `replayable`

### Compatible path under the current contract

A CAS-derived service can be the live implementation behind the existing
service kit:

```ts
const kit = replayable(Catalog, catalogOperations)

const liveRoleFromCas = CatalogFromCas.layerAs(kit.live, snapshotRef)

const CatalogRecord = kit.record.pipe(
  Layer.provide(liveRoleFromCas)
)

const CatalogReplay = kit.replay
```

`layerAs` is an illustrative ergonomic addition: the same hydration recipe can
target the public service key for ordinary use or the kit's private live-role
key for recording. This avoids constructing the public wrapper in terms of
itself. A corresponding `kit.recordFrom(liveLayer)` helper could be considered,
but only if it safely relabels the implementation to the internal live role.

In record mode, the CAS-derived service runs and its described operation
outcomes are recorded. In replay mode, the live role—including its remote CAS
dependency—is absent, and the current no-live-fallback construction remains
structural.

### Fixed service data is not currently a replay identity

The current slice deliberately has no program identity or environment-root
comparison. If `snapshotRef` is captured by the live implementation but not
present in the operation request, replay compatibility does not establish that
the same snapshot was selected. It only establishes compatibility of the
emitted described requests with history under the ratified protocol.

There are two honest future choices:

1. If the root varies per operation, put a typed CAS reference in that
   operation's request Schema. Existing positional request matching then sees
   it.
2. If the root is fixed for a session, add a future versioned dependency
   manifest to session setup and the replay witness. This is a contract
   extension requiring Pass A, not a field to add opportunistically.

The second choice avoids repeating one root in every history entry and creates
a natural home for projection id/revision, Effect pin, and non-secret handler
configuration. It must not be described as program identity.

### CAS reads during replay

There are also two distinct modes:

- **Outcome substitution, current contract:** the CAS-derived service is a
  live leaf, so replay does not load its domain graph at all.
- **Rehydrated immutable dependency, future extension:** replay loads an exact
  admitted root and allows pure orchestration to consult the hydrated value.

The second mode could reduce histories for large read-only tables, but it adds
new obligations. Prefer resolving the complete bounded closure before program
execution so network availability, authorization, and transport failures are
session-setup/store failures rather than new mid-program observations. Lazy
remote reads inside replay would otherwise introduce unrecorded failure and
interruption points.

## Remote `CasStore`: Effect-idiomatic adapter design

The logical `CasStore` interface should remain backend-independent. Remote
behavior belongs in a layer that provides the same service:

```ts
const RemoteCas = CasStoreRemote.layer({
  baseUrl,
  namespace,
  token,
  limits
})
// Layer<CasStore, RemoteCasConfigError, HttpClient>

const RemoteCasFromConfig = CasStoreRemote.layerConfig({
  baseUrl: Config.string("CAS_BASE_URL"),
  namespace: Config.string("CAS_NAMESPACE"),
  token: Config.redacted("CAS_TOKEN")
})
```

The adapter should acquire/configure its client, cache, request resolver, and
any scoped resources once in the owning layer—not once per `load`. Runtime
configuration comes through `Config`; credentials remain redacted and outside
content identity.

Effect's unstable HTTP client is itself a `Context.Service`, supports request
transforms for base URL/auth, typed request execution, transient retry, byte
bodies, and streaming request/response bodies
([pinned `HttpClient.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpClient.ts#L150-L248),
[`HttpClientRequest.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpClientRequest.ts#L396-L473),
[`HttpBody.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpBody.ts#L239-L267),
[`HttpIncomingMessage.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpIncomingMessage.ts#L57-L65)).
Because these modules are unstable, the public Foldlab contract should expose
`CasStore`, not Effect HTTP types.

### Remote load path

The load boundary must treat the network as untrusted:

```text
ContentId
  -> authenticated request in a declared namespace
  -> bounded bytes or byte stream
  -> decode exact node framing
  -> recompute address
  -> canonicality and known-kind checks
  -> typed-reference checks available at this boundary
  -> admitted CasNodeInput
  -> success cache
```

Cache raw HTTP bytes only as an adapter-private optimization. The public lookup
cache should contain nodes that have passed admission. Never renormalize a
remote response into a different node.

### Cache and concurrent lookup deduplication

`Cache.makeWith` accepts an exit-aware TTL, and concurrent `get` calls for one
missing key share one lookup
([pinned `Cache.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cache.ts#L111-L224),
[concurrent-get contract](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cache.ts#L331-L338)).
This fits immutable admitted nodes well:

- cache successful admitted loads for the adapter/layer lifetime or a bounded
  operational TTL;
- do not cache transport, authorization, integrity, or decode failures;
- do not negatively cache not-found by default, because an append-only store
  may acquire that address later;
- bound capacity even though values are immutable; and
- share the cache at layer scope.

An on-disk admitted-node mirror can replace or complement the memory cache for
large graphs, but its load path remains the same admission boundary.

### Batching with `RequestResolver`

When the remote protocol has a genuine multi-key read endpoint, implement
remote `load` through `Effect.request` plus `RequestResolver`. The resolver can
collect concurrent logical `load(id)` calls into one wire request; `batchN`
bounds backend limits. Effect also exposes resolver-to-cache composition
([pinned `RequestResolver.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/RequestResolver.ts#L184-L306),
[cache integration](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/RequestResolver.ts#L1042-L1150)).

If the backend has only per-node GET, `RequestResolver` does not create a batch
endpoint. Use `Cache` for duplicate suppression and bounded `Effect.forEach`
for distinct nodes.

The pinned Bazel Remote Execution API is useful remote-CAS precedent: it
separates `FindMissingBlobs`, `BatchUpdateBlobs`, `BatchReadBlobs`, and streaming
large transfers; batch entries may succeed or fail independently and digest
mismatch is an explicit error
([pinned REAPI service](https://github.com/bazelbuild/remote-apis/blob/becdd8f9ff811df88a22d3eadd6341753d51d167/build/bazel/remote/execution/v2/remote_execution.proto#L2833-L2999),
Source Lock pending as already recorded by the earlier replay survey).

### Graph upload

The high-level projection writer should construct the graph locally, compute
every address, and upload in dependency order:

1. encode and locally admit all nodes;
2. deduplicate by full `ContentId`;
3. optionally query missing addresses in batches;
4. upload missing leaves and then parent levels;
5. upload the root only after its referenced closure is available; and
6. publish any mutable name/head only after root upload succeeds.

This matches the current `put` rule that references already resolve. It also
matches XET's child-data-before-reconstruction-metadata pattern, while retaining
the previously recorded limitation that crashes can leave harmless orphans
([pinned XET disposition](xet-prior-art.md)).

For a remote adapter with a batch write endpoint, calls at one topological
level may be coalesced. A batch response must report per-node status; one
success does not imply whole-graph publication. Large payload kinds should use
framed streams and declared limits rather than collecting unbounded arrays.

### Retry boundary

Retry only operations whose protocol establishes idempotency:

- exact-address `load`, presence checks, and immutable batch reads;
- upload of canonical bytes to an expected full address when the server
  recomputes the address and treats an existing identical object as success;
- a resumable byte-stream upload under its declared offset/idempotency rules.

Do not generically retry mutable head updates, authorization changes, garbage
collection, or a future destructive operation. A head update needs
compare-and-set, an ETag/version precondition, or a scoped idempotency key.
Bound retries, use backoff and jitter, honor server retry information, and keep
exhausted failure visible.

### Error classification

The current `StoreFailure { reason: string }` is sufficient for the M1
interface freeze but too coarse for an ergonomic remote adapter. A future
Pass-A error review should distinguish at least:

| Family | Examples | Retry posture |
| --- | --- | --- |
| Admission/integrity | address mismatch, non-canonical bytes, unknown kind, wrong-kind ref | never retry unchanged bytes |
| Presence | node not found, referenced closure missing | no default negative cache; retry only by explicit consistency policy |
| Authorization | unauthenticated, forbidden, namespace violation | refresh/re-authenticate only under explicit policy |
| Transport | timeout, connection reset, transient 5xx, rate limit | bounded retry for idempotent operations |
| Protocol | malformed frame, wrong content type, oversized body, incomplete batch result | do not retry unchanged response path |
| Capacity | quota exceeded, object too large, batch too large | split only when protocol permits; otherwise surface |
| Configuration | invalid URL, unsupported scheme/version, missing credentials | layer construction failure |

CAS admission errors remain separate from transport errors and from replay
mismatch categories. Secrets and private payloads must be redacted from error
fields, logs, and traces.

The current union also has no clause specifically for a direct
`load(rootId)` miss. `DanglingReference` names a failed reference during node
admission and should not be overloaded for a caller-requested absent root. A
future remote-capable surface needs a clause such as `ContentNotFound`, with its
cache and consistency posture stated separately from transport unavailability.

### Scoped acquisition and authentication

Remote clients, connection pools, refresh workers, and subscriptions belong to
the layer scope. The adapter should expose completed methods, not `start`/`stop`
control. Any long-lived stream consumer is forked into that scope and uses
backpressure.

Effect's unstable `EventLogRemote` provides nearby idioms, not a contract: it
models the remote as a service, acquires it through a layer, caches
authentication, chunks writes, registers it for the scope, exposes change
queues, and maps failures to a remote error
([pinned `EventLogRemote.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/eventlog/EventLogRemote.ts#L59-L173)).
Its event replication and encryption semantics do not transfer automatically
to immutable CAS.

### Multiple remote stores or tenants

Use one remote layer for one fixed endpoint/namespace. Use `LayerMap` when a
process selects scoped remote stores dynamically by a non-secret tenant or
endpoint key. The lookup can build `RemoteCas.layer(optionsFor(key))`; idle TTL
releases clients, and explicit invalidation handles credential or routing
changes.

Do not let one global presence check reveal content across authorization
boundaries. XET's remote-deduplication analysis already records the
content-existence and cross-access privacy risk
([pinned XET prior-art note](xet-prior-art.md#concrete-lessons-for-foldlab)).

## Local, remote, and offline composition

Immutable admitted nodes permit a useful tiered adapter, but the policy must be
named rather than hidden behind fallback:

```text
load(id): local admitted-node hit
       or remote load and reverification -> local admitted put -> return

put(node): local-only authority
        or remote-authoritative upload then optional local mirror
        or explicit replication mode with separately observable pending state
```

Recommended initial policies:

- **Remote authoritative:** writes succeed only after the remote accepts the
  node; local storage is a read-through admitted-node mirror.
- **Local authoritative:** writes commit locally; remote replication is a
  separate workflow and no remote-durability wording is used.
- **Offline read:** exact roots already in the admitted local store are
  available; a missing node returns an explicit offline/unavailable error.

Avoid an automatic `catch remote -> use anything local` policy for mutable
heads. An exact immutable node cannot become stale, but a name-to-root mapping
can. Resolve a mutable name before a replay session and freeze the exact root,
or mediate head resolution as a described replayable operation.

## Mutable names and heads are a separate service

Users will want `"latest"`, project names, branches, aliases, and deployment
channels. Those are not CAS nodes. Model them through a separate ordinary
Effect service, provisionally:

```ts
interface CasHeads {
  readonly resolve: (name: HeadName) => Effect.Effect<ContentId, HeadError>
  readonly compareAndSet: (
    name: HeadName,
    expected: ContentId | undefined,
    next: ContentId
  ) => Effect.Effect<void, HeadError>
}
```

This is the same separation visible in Git: logical object identity is over
the uncompressed `type + size + NUL + data`, while loose and packed storage are
physical layouts and refs are a separate naming plane
([official Git loose-object format](https://git-scm.com/docs/gitformat-loose/2.55.0),
Git 2.55.0 documentation; byte receipt pending). LLVM similarly separates its
immutable object store from `ActionCache`, a key/value association between two
CAS identifiers
([LLVM CAS guide](https://llvm.org/docs/ContentAddressableStorage.html), live
documentation; exact LLVM source pin remains pending).

A mutable head change is a live effect. It must never silently change the
content identifier or be inferred from `CasStore.load`.

## Prior-art disposition

| Source | Useful pattern | Boundary for this design | Provenance |
| --- | --- | --- | --- |
| Pinned Effect `Context`/`Layer` | service identity, effectful/scoped construction, dependency visibility | subject implementation, not Foldlab semantics | existing Source Lock |
| Pinned Effect `LayerMap` | keyed cached scoped service families with invalidation | optional composition recipe; not content identity | exact research receipt; Source Lock file promotion pending |
| Pinned Effect `Schema` transformations | typed bidirectional effectful value boundaries | default JSON is not CAS canonical bytes; graph traversal remains explicit | exact research receipt |
| Pinned Effect `Graph` and `Schema.Graph` | checked cycle/traversal primitives and snapshot import for a materialized view | raw graph permits cycles and numeric allocation indexes are not content identity | exact research receipt |
| Pinned Effect `Cache`/`RequestResolver` | lookup dedupe, TTL, genuine backend batching | operational adapter behavior, not store laws | exact research receipt |
| Effect unstable persistence/eventlog/http | layered backends, schemas, scoped remote/auth idioms | version-sensitive; must not dictate public Foldlab contract | exact research receipt |
| IPLD Schema links and CAR | explicit block boundaries, typed-link hint, transport roots | link hint is not cross-block proof; CAR closure is not guaranteed | exact commits in earlier replay survey; Source Lock pending |
| Unison | content-addressed definitions plus separate names/effect handlers | not service-instance serialization or Effect replay | exact commit in earlier replay survey; Source Lock pending |
| Git | identity separate from loose/pack storage and refs | repository object model, not typed CAS admission | Git 2.55.0 docs; byte receipt pending |
| XET | bottom-up upload, range/stream transfer, dedup privacy, storage envelopes outside identity | no typed Effect service or replay semantics | existing Source Lock and receipt |
| LLVM CAS | interchangeable stores, data plus refs, loaded object versus portable id, separate action cache | implementation contracts are not Foldlab proof obligations | live page; source pin pending |
| Bazel REAPI | find-missing, batch read/write, streaming large blobs, per-item errors | remote build blob API, not typed graph admission | exact commit in earlier replay survey; Source Lock pending |

## Candidate public ergonomics

The smallest coherent future surface is:

```ts
// 1. Explicit durable-data description
const RulesCas = Cas.value(...)
const ProjectCas = Cas.graph(...)

// 2. Direct value use
const ref = yield* ProjectCas.put(project)
const restored = yield* ProjectCas.get(ref)

// 3. One fixed service
const ProjectServiceFromCas = Cas.service({
  service: ProjectService,
  projection: ProjectCas,
  make: ...
})
const ProjectLayer = ProjectServiceFromCas.layer(ref)

// 4. Replay integration without a public-tag recursion
const kit = replayable(ProjectService, descriptions)
const RecordedProject = kit.record.pipe(
  Layer.provide(ProjectServiceFromCas.layerAs(kit.live, ref))
)

// 5. Dynamic family selected by root
class ProjectsAt extends LayerMap.Service<ProjectsAt>()(...)

// 6. Store placement is ordinary layer wiring
program.pipe(Effect.provide(ProjectLayer), Effect.provide(RemoteCas))
```

This makes the common case one descriptor, one root, one layer. It keeps the
advanced machinery—batching, remote clients, caches, scopes, and graph
traversal—inside the appropriate implementation layers.

## Design choices to reject

Reject a proposal if it:

- hashes a service tag, closure, `Layer`, `Context`, live client, credential,
  or open resource as though it were the service's semantic identity;
- derives graph partitioning silently from arbitrary Schema AST shape;
- exposes raw Effect `Graph` or a `Schema.Graph` snapshot as CAS identity,
  `CasStore`, or an authoritative remote graph;
- relies on numeric `NodeIndex` allocation order as canonical graph labeling;
- accepts `PrimaryKey` as a content identifier;
- permits a phantom typed reference to bypass runtime kind validation;
- hides remote acquisition inside every service method when eager layer
  hydration could keep method error types unchanged;
- constructs a replay wrapper by resolving its own public service tag;
- gives replay construction a captured live/CAS-derived implementation;
- treats a fixed hidden service root as though current replay compatibility
  checked it;
- uses `LayerMap` for one fixed root or puts secret tokens in its key;
- performs per-node network calls when a real batch endpoint exists and a
  resolver can coalesce them;
- uses `RequestResolver` when the backend has no batch operation and calls the
  result batching;
- caches raw or unverified remote bytes as admitted nodes;
- caches not-found indefinitely in a store that can later grow;
- retries a mutable head update without a compare-and-set or idempotency
  contract;
- makes local fallback silently redefine remote authority or freshness;
- publishes a root before its referenced remote closure exists; or
- buffers remote record-history appends while retaining the current truthful-
  prefix/session-abort wording.

## Obligations created by this direction

These are pending design/proof obligations, not current claims. Their exact
judgment forms and theorem names remain to be frozen in Pass A.

### Value and graph projection

- descriptor revision and root kind are explicit;
- encoding produces locally admitted nodes with ordered typed references;
- any internal materialized-closure Graph is derived from reverified nodes,
  has a distinguished root, contains exactly its reachable closure, and has
  one edge per ordered typed reference;
- if DAG admission is selected in Pass A, acyclicity is established and
  preserved before child-first traversal; regardless, Effect Graph numeric
  indexes do not enter content identity;
- graph upload is closed and root-last;
- reading checks the expected root kind and every followed node;
- `get(put(value))` returns the declared domain canonicalization of `value`;
- migration is selected by explicit old/new descriptor identities;
- traversal has declared node, byte, depth, and fan-out bounds; and
- equal roots do not imply a stronger value equality than the hash lattice
  permits.

### Service hydration

- a fixed-root layer constructs the same user-facing service shape as a
  by-value factory;
- layer construction errors remain visible and do not widen method errors;
- live authorities stay visible in `R` and outside the content root;
- `layerAs(kit.live, root)` cannot resolve the public wrapper recursively;
- double wrapping remains rejected; and
- any recorded service-provenance root has an explicit observation role.

### Remote adapter

- define a refinement judgment under which successful remote `load` implements
  the logical admitted-node `load`, then prove it;
- define the cache-observation judgment under which a local admitted-node hit
  matches successful remote load for immutable nodes, then prove it;
- define and prove that request batching returns each key's corresponding
  result or error without cross-key substitution;
- incomplete/misaligned batch responses fail closed;
- upload retries are admitted only under an exact-address idempotency protocol;
- authentication and authorization do not participate in node identity;
- namespace-scoped presence does not become a cross-tenant oracle;
- interruption closes streams/resources without returning partial nodes; and
- offline and replication modes have distinct, truthful authority statements.

### Replay integration

- record mode still aborts structurally on any remote history append failure;
- replay construction still has no live role;
- a CAS-derived live service cannot become a fallback after mismatch;
- fixed service roots are not claimed to be compared until the session
  dependency-manifest extension exists; and
- any future rehydrated-dependency mode resolves its declared closure before
  execution or explicitly models lazy-load failures as observations.

## Suggested sequence

1. **Pass A for value projection.** Freeze leaf versus graph descriptor roles,
   descriptor identity/revision, typed root shape, migration boundary, and
   error families. Decide explicitly whether DAG acyclicity is a store
   admission judgment or only a property of selected projections.
2. **In-memory ergonomic slice.** Implement `Cas.value`, explicit graph
   projection, typed `put/get`, and property/round-trip fixtures over the
   current in-memory store.
3. **Service hydration slice.** Add fixed-root eager `Cas.service(...).layer`
   and the private-live-role targeting seam; test with an existing service
   whose method error types do not contain CAS errors.
4. **Remote baseline.** Provide one HttpClient-backed `CasStore` layer with
   bounded single-node load/put, strict verification, typed errors, Config,
   auth, and no retry beyond proven idempotent reads.
5. **Remote performance.** Add layer-owned success cache, genuine batch reads
   through `RequestResolver`, topological graph upload, optional find-missing,
   and streaming for declared large objects.
6. **Dynamic and offline composition.** Document `LayerMap` root/tenant
   recipes and add an explicit admitted-node local-mirror policy.
7. **Replay dependency extension, only if earned.** Decide whether fixed CAS
   roots belong in a session dependency manifest and whether immutable
   rehydration is a distinct admitted replay mode.

The first three steps can improve user ergonomics without changing the
ratified replay semantics. The last step changes what replay observes and must
not be smuggled in as a convenience overload.

## Source standing

- Effect repository commit and the current core service/runtime surfaces are
  in the estate Source Lock. The additional Effect file identities used here
  are resolved by the accompanying research receipt; Source Lock promotion is
  pending.
- XET `draft-denis-xet-05` is pinned in the Source Lock with a resolution
  receipt.
- Unison, IPLD, Bazel REAPI, Temporal, Restate, Golem, CID, and rr exact commits
  are recorded in the earlier
  [content-addressed replay survey](cas-effect-program-replay.md); their Source
  Lock promotion remains pending there.
- The Git 2.55.0 and current LLVM documentation links above are live primary
  references. Exact artifact-byte/source pins remain pending, so no gated
  claim should depend on them.

No source code or Lean declaration is changed by this report, and no build or
test result supports any proposal above.
