# Layer semantics and type design for the remote CAS services

Status: design review (G0), 2026-08-27. This report reviews the pinned
Effect v4 sources (`effect@4.0.0-rc.111`, the package's own `node_modules`
copy) for the layer-construction, scope, stream, and HTTP-client semantics
that the ratified four-service streaming architecture will stand on, and
proposes the service shapes, layer graph, and type-design decisions for the
R2 implementation slice. Nothing here is ratified; the closing decision
docket lists every choice with a recommendation. File citations are
`module.ts:line` at the pin.

The four services under design are the R1-acceptance ruling's separation:
`CasStore` (whole admitted nodes), `CasTransfer` (streamed upload and
download mechanics), `CasEvents` (advisory notifications), and
`RemoteCasTransport` (raw untrusted protocol streams, adapter-internal).
The review's charge is that the implementation stay ergonomic and
Effect-native with careful attention to type design — which here means:
every ruled semantic rule should be either unrepresentable to violate in
the types, or enforced at exactly one named boundary.

## 1. Pinned v4 semantics that bear on the design

### 1.1 Layer construction and memoization

- `Layer.effect(Key, effect)` runs the construction effect **with the
  layer's own `Scope` provided** — the signature removes `Scope` from the
  requirements (`Layer.ts:1386-1439`). Version 3's separate `Layer.scoped`
  constructor is gone; `Effect.acquireRelease` inside `Layer.effect` is the
  idiom for a service that owns resources, and the resources die when the
  layer's scope closes. Adapter layers therefore need no special casing to
  own connection pools or spool directories.
- Layers are memoized **by reference identity** through the build
  `MemoMap` (`Layer.ts:222,584,645`). One `const` layer value provided to
  several consumers builds once; `Layer.fresh` (`Layer.ts:3850`) opts out.
  Consequence: if `CasStore`, `CasTransfer`, and `CasEvents` layers are
  built from one shared transport-pool layer *value*, they share the pool;
  if each constructs its own, they silently triple it. The design must
  export the sharing structure, not ask users to arrange it.
- `Layer.unwrap` (`Layer.ts:1580`) builds a layer from an effect returning
  a layer — the idiom for config-driven construction. `Layer.mock`
  (`Layer.ts:3994`) builds partial test doubles.

### 1.2 Scope

`Scope` is a lifetime boundary with sequential or parallel finalization
(`Scope.ts:45-49`). Interruption of the owning fiber closes the scope and
runs finalizers with the terminating `Exit`. The HTTP client exposes the
canonical pattern: `HttpClient.withScope` registers an `AbortController`
abort as a scope finalizer, so cancelling the scope aborts the in-flight
request (`HttpClient.ts:1936-1949`). Every ruled ownership item —
connections, response bodies, temporary spools, subscriptions,
cancellation — has a direct home in this model, including
`FileSystem.makeTempFileScoped` / `makeTempDirectoryScoped` for the
whole-object verification spool (`FileSystem.ts:188-210`).

### 1.3 Streams are re-run descriptions; chunk boundaries are artifacts

- A `Stream<A, E, R>` is a description; each run re-executes acquisition
  (`Stream.ts:96-104`). But a stream *value* can close over a one-shot
  external resource — most relevantly, a web-fetch response body: the
  `HttpClientResponse` from `fromWeb` wraps a `Response` whose body reads
  once (`HttpClientResponse.ts:80`, `HttpIncomingMessage.ts:57-66`).
  Re-running such a stream does not replay the bytes. The type system
  cannot distinguish a replayable description from a captured one-shot,
  so upload restartability must be made explicit in the API (decision D4).
- Streams emit in chunks to amortize evaluation; `Stream.chunks` and
  `Stream.rechunk` expose and rearrange boundaries as a stated
  performance artifact (`Stream.ts:11504,11537`). This is the runtime
  mirror of the fragmentation-invariance obligation: no adapter parse may
  branch on chunk boundaries, and rechunk-equivalence is a directly
  testable property.
- `Sink<A, In, L, E, R>` consumes a stream to one result with leftovers
  (`Sink.ts:63`) — the correct carrier for incremental digest-and-count
  consumption during transfers.
- `Pull<A, E, Done, R>` is an effect that emits one value, fails with
  `E`, or terminates with `Cause.Done<Done>` (`Pull.ts:40-42`), and
  `Channel<OutElem, OutErr, OutDone>` carries the same typed terminal
  (`Channel.ts:140-148`). **A typed end-of-stream value that cannot be
  forged by a mid-stream element is exactly the shape of the
  protocol-completion witness**: the transport-standards survey requires
  completion evidence (byte counts, terminal framing) distinct from both
  data and failure, and the substrate already distinguishes those three
  by construction at the `Pull`/`Channel` layer (decision D6).

### 1.4 HttpClient at the pin — and why the two combinators stay prohibited

`HttpClient` is an ordinary `Context.Service` whose `execute` returns an
`HttpClientResponse` effect (`HttpClient.ts:62,150`). The two combinators
the R1 architecture prohibits at the seam are present and now precisely
characterized:

- `followRedirects` (`HttpClient.ts:1957-2011`) loops on any 3xx with a
  `location` up to a count, rewrites `POST` to `GET` on 301/302/303
  (legacy semantics — for an upload this silently changes the operation),
  strips `authorization`/`proxy-authorization`/`cookie` only on an
  origin change, and emits **no observable decision**: no policy event,
  no per-hop record, no cross-namespace check. The remote machine's
  redirect handling is a semantic transition with policy authority; this
  combinator would make it invisible. Prohibited at the seam, as ruled.
- `retryTransient` (`HttpClient.ts:1111`) retries on error tags or
  status classes with a schedule. It has no concept of application
  idempotency, retry commitment, or processing evidence — the exact
  properties RFC 9110 §9.2.2 and the gRPC commitment boundary make
  load-bearing. Retry is the machine's decision; the shell executes one
  declared command per attempt. Prohibited, as ruled.
- `HttpClient.withScope` and `HttpBody.stream(stream, contentType?,
  contentLength?)` (`HttpBody.ts:445-485`) are the sanctioned resource
  and upload primitives. `HttpIncomingMessage.MaxBodySize` is a
  `Context.Reference` bounding body reads (`HttpIncomingMessage.ts:133`)
  — useful as a backstop, but it is one bound, not the ruled four-stage
  budget, and being fiber-ambient it is not where semantic budget policy
  should live (decision D3).

### 1.5 Keyed resources

`RcMap` shares scoped resources by key with reference counting, idle
time-to-live, and capacity (`RcMap.ts:1-13`) — the connection-pool
substrate inside a transport. `LayerMap` lifts the same discipline to
keyed service families (`LayerMap.ts:1-11`) — the idiom for
per-authority or per-tenant store instances, matching the survey's
"Layer provides one configured endpoint; LayerMap provides a keyed
family." Secrets stay layer dependencies and never become keys.

## 2. Proposed architecture

### 2.1 Service keys and visibility

| Service | Key | Visibility | Provides |
| --- | --- | --- | --- |
| `CasStore` | `foldlab/effect-replay/CasStore` (existing, frozen shape) | public | whole admitted nodes: `put`, `load` |
| `CasTransfer` | `foldlab/effect-replay/CasTransfer` | public | `putStream`, `loadStream`; streamed mechanics with budgets |
| `CasEvents` | `foldlab/effect-replay/CasEvents` | public | advisory notification streams |
| `RemoteCasTransport` | none — **not a service key** | internal | one-command-at-a-time raw exchange |

`RemoteCasTransport` deliberately never enters `Context`: it is a plain
interface handed to the semantic adapter's constructor, exactly as
`CasAddress` is handed to `makeMemoryCasStore` today. Keeping it out of
the environment makes "raw chunks stay untrusted" structural — user code
cannot resolve the transport by key and read unverified streams. Its
implementations are themselves built by effects that *do* use context
(`Effect<RemoteCasTransport, never, HttpClient | Scope>`), so platform
clients arrive through ordinary layers without the transport becoming
reachable as a service.

### 2.2 Shapes (proposed, R2 freeze review applies)

```ts
// src/cas/Transfer.ts
export interface CasTransferShape {
  /** Stream an upload. The address is computed (or, when `expected` is
   * given, checked) incrementally while the source is consumed. The
   * effect succeeds only after the source is fully consumed AND the
   * remote acknowledges commitment; the acknowledgement is re-verified
   * per the unconditional caching law. */
  readonly putStream: (
    source: UploadSource,
    options: {
      readonly kind: CasKind
      readonly refs: ReadonlyArray<CasRef>
      readonly expected?: ContentId
    },
  ) => Effect.Effect<ContentId, CasRemoteError | CasError>

  /** Stream a download. Every emitted byte is verified: an adapter with
   * per-chunk content addressing or Merkle proofs emits as chunks
   * authenticate; a whole-object-hash adapter verifies through a scoped
   * temporary spool before the first byte is emitted. The stream's
   * lifetime (connection, spool) belongs to the given Scope. */
  readonly loadStream: (
    id: ContentId,
  ) => Effect.Effect<
    Stream.Stream<Uint8Array, CasRemoteError | CasError>,
    CasRemoteError | CasError,
    Scope.Scope
  >
}
export class CasTransfer extends Context.Service<CasTransfer, CasTransferShape>()(
  "foldlab/effect-replay/CasTransfer",
) {}

/** Restartability made explicit: retries re-run only replayable sources. */
export type UploadSource = ReplayableSource | OneShotSource
// constructors: Transfer.replayable(stream), Transfer.oneShot(stream)
```

The `UploadSource` split makes the ruled retry rule unrepresentable to
violate: a `oneShot` source gets exactly one attempt and any retryable
failure surfaces as an error carrying `knownUnprocessed | possiblyProcessed`
evidence instead of a silent replay. A `replayable` source promises that
each run yields the same bytes — and an unfaithful replay is still caught,
because the incremental address computation re-checks every attempt; the
type prevents the silent retry, the address check catches the broken
promise. Defense in depth, both halves already obligations.

The download type keeps **one uniform guarantee** — no unverified byte is
ever emitted — rather than splitting the public type by backend
capability. Early emission under per-chunk proofs versus spool-then-emit
under a whole-object hash is a latency property of the adapter, not a
semantic property the caller should branch on.

```ts
// src/cas/Events.ts
export interface CasEventsShape {
  /** Advisory notifications. Delivery is never admission; payloads carry
   * identifiers and cursors, never node bytes. Duplicates and gaps are
   * permitted unless a stronger protocol is layered above. The
   * subscription's lifetime belongs to the given Scope. */
  readonly notifications: (
    selector: CasEventSelector,
  ) => Effect.Effect<
    Stream.Stream<CasNotification, CasEventsError>,
    CasEventsError,
    Scope.Scope
  >
}
```

`CasNotification` is a `Schema.Class` union (available, invalidated,
progress, custom) whose fields are identifiers, counts, and an optional
cursor — structurally incapable of carrying admitted values, which makes
"notification is not admission" a type fact, not a discipline.

```ts
// internal — passed to the adapter, never in Context
export interface RemoteCasTransport {
  /** Execute exactly one machine command for one operation attempt.
   * Wire events are untrusted observations; the terminal value is the
   * protocol-completion witness (actual byte counts, terminal framing).
   * Interrupting the scope aborts the exchange. */
  readonly issue: (
    op: OpId,
    attempt: AttemptId,
    command: RemoteCommand,
  ) => Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness>
}
```

Using `Channel`/`Pull` here puts the completion witness in `OutDone`,
where no mid-stream event can forge it and where failure and completion
are disjoint by construction — the R4 roadmap's witness lands as a type,
and "terminal completion before admission" becomes: the adapter admits
only after the channel *returns*, never from within its element stream.

### 2.3 Layer graph

```ts
// src/cas/Remote.ts (public entry)
Cas.layerRemote(config: CasRemoteConfig):
  Layer.Layer<CasStore | CasTransfer, CasRemoteInitError, HttpClient>

Cas.layerRemoteEvents(config: CasEventsConfig):
  Layer.Layer<CasEvents, CasRemoteInitError, HttpClient>
```

- One layer provides **both** `CasStore` and `CasTransfer`: they are two
  views of one semantic adapter (shared machine state, shared in-flight
  map, shared admitted-only cache), and providing them from one build is
  what guarantees `load` and `loadStream` agree. Splitting them into two
  layer values would let users compose two independent adapters over one
  endpoint with divergent caches.
- `CasEvents` is a separate layer: an advisory plane with its own
  lifecycle, possibly its own endpoint; nothing in the data plane may
  depend on it.
- The transport pool (an `RcMap` of connections keyed by authority) lives
  inside the adapter's layer scope. Multi-authority families come later
  as a `LayerMap` wrapper without changing the single-authority shapes.
- Requirements stay visible: the HTTP realization demands `HttpClient` in
  `RIn` rather than defaulting a fetch client, so tests provide fakes and
  hosts choose transports explicitly. A convenience
  `layerRemoteFetch(config)` may pre-apply `FetchHttpClient` — visible
  composition, not a hidden default.

### 2.4 Configuration and budgets

`CasRemoteConfig` is a `Schema.Class` validated at layer construction —
**explicit layer input, not a `Context.Reference`**. Budgets produce
budget-rejection events in the machine (`RMT-002` family); values that
change model behavior are machine parameters and must not be
fiber-ambient, per the estate's ambient-tripwire posture and the survey's
"explicit machine data" rule. The config carries:

- authority (origin; userinfo structurally excluded by the schema),
  authority mode (`remote-authoritative | local-authoritative | offline`,
  no silent fallback),
- the four ruled byte budgets — encoded, decoded, decompressed, queued —
  plus attempt count and per-operation deadline,
- redirect policy (bound, cross-origin/cross-namespace stance),
- credentials as `Redacted` values, which keeps them out of every
  rendered error and transcript by construction.

The adapter additionally sets `HttpIncomingMessage.MaxBodySize` from the
decoded-byte budget as a substrate backstop; the authoritative counters
remain the adapter's own incremental sinks, which produce the typed
budget errors.

### 2.5 Error taxonomy

`Schema.TaggedError` classes forming a `CasRemoteError` union, each
carrying operation identity, attempt identity, stage, redacted authority,
byte counts where meaningful, and a processing classification:

- `RemoteIntegrityError` — address or canonicality failure attributed to
  remote bytes; terminal for that `(id, bytes)` pair (RMT-003).
- `RemoteBudgetError` — `stage: "encoded" | "decoded" | "decompressed" |
  "queued"`, observed amount, configured bound.
- `RemoteProtocolError` — framing/protocol failure with `completion:
  "knownUnprocessed" | "possiblyProcessed"`.
- `RemoteUnavailableError` — connectivity/service failure, same
  completion evidence.
- `RemotePolicyError` — refusals by configured policy (redirect crossing,
  authority mode, oneShot retry refusal).

Redaction is constructional: error fields are typed so secrets cannot
enter (authority as origin string, credentials only as `Redacted`), not
filtered at render time. Because the errors are Schema classes they
serialize into differential transcripts unchanged.

`CasStore` methods keep their frozen `CasError` channel. The remote-backed
instance surfaces remote failure through **one additive member**
(`RemoteFailure` wrapping the typed `CasRemoteError`) so the logical store
shape stays stable while full detail lives on `CasTransfer`'s own
methods — an interface re-freeze event for the R2 review (decision D2).

### 2.6 Correspondence and file placement

Mirroring the ratified layout and the Lean tree: `src/cas/Transfer.ts`,
`src/cas/Events.ts`, `src/cas/Remote.ts` (config, errors, layer entry);
`src/internal/remoteMachine.ts` as the rule-for-rule mirror of
`Effects/Remote/Machine.lean` (the reducer-correspondence discipline that
held for `Reducer.ts`); `src/internal/remote.ts` as the semantic adapter
driving the machine over per-operation scopes; transport realizations in
`src/internal/remoteHttp.ts` (and later peers). Per-operation stream
isolation gets its mechanism from per-operation child scopes: each
operation's transport channel, spool, and finalizers hang from its own
fork, so interrupting or failing one operation cannot release or leak
another's resources.

### 2.7 The differential-peer abstraction (test-side)

The ratified LeanServer peer binds through an abstract interface so
suites stay isolated from any single peer:

```ts
export interface ConformancePeer {
  readonly name: string
  readonly capabilities: ReadonlyArray<PeerCapability>
  /** Enact one scenario realization; the endpoint dies with the Scope. */
  readonly serve: (realization: ScenarioRealization) =>
    Effect.Effect<PeerEndpoint, PeerError, Scope.Scope>
}
```

Bindings: the in-memory hostile server (first), LeanServer (ratified
peer; its audited gaps — gRPC trailers in headers, HTTP/2 early request
construction, WebSocket masking/fragmentation — are named detection
targets the suite must catch), and reference servers later. This lives in
the test tree at R2; packaging it as a public testing module is deferred
until the differential lane needs distribution.

## 3. What this design refuses

- No transport service key; no raw stream reachable through `Context`.
- No ambient semantic state: budgets, authority, retry entitlement, and
  admission state are machine/config data, never fiber-local.
- No `followRedirects` / `retryTransient` at the seam; the shell executes
  single declared commands.
- No public API that returns bytes before verification, and no download
  type that asks callers to branch on backend verification capability.
- No notification type that can carry node bytes.
- No silent one-shot retry; no retry without idempotency or
  known-unprocessed evidence once R4 lands the evidence carrier.
- `Stream.share`/`broadcast` of download streams stays out of the public
  surface: sharing verified streams is a consumer concern with its own
  scope semantics, and offering it would blur per-operation isolation.

## 4. Decision docket

| # | Decision | Recommendation |
| --- | --- | --- |
| D1 | Layer packaging | One `layerRemote` providing `CasStore \| CasTransfer` from one shared adapter build; `CasEvents` a separate layer; transport never a service. |
| D2 | Remote failure on the frozen `CasStore` shape | Add one additive `CasError` member wrapping `CasRemoteError` at the R2 interface re-freeze; full taxonomy on `CasTransfer` methods. |
| D3 | Budget/policy carrier | Explicit Schema-validated `CasRemoteConfig` at layer construction; no `Context.Reference` for semantic policy; `MaxBodySize` set only as backstop. |
| D4 | Upload restartability | Tagged `UploadSource` (`replayable` / `oneShot`) constructors; retries only for `replayable`; address recheck every attempt. |
| D5 | Download verification surface | One uniform verified-bytes `Stream` in a caller `Scope`; early emission is adapter capability, not API shape; spool via `makeTempFileScoped`. |
| D6 | Completion witness carrier | Internal transport is `Channel`/`Pull` with the completion witness in `OutDone`; admission only after terminal value; public surfaces stay `Stream`/`Effect`. |
| D7 | Concurrency mechanism | Per-operation child scopes + shared machine state behind `SynchronizedRef`, keyed by `OpId`; fiber identity never semantic. |
| D8 | Peer abstraction placement | `ConformancePeer` interface in the test tree at R2; LeanServer one binding; promotion to a shipped testing module deferred. |

Each recommendation follows from a pinned semantic fact cited above;
adopting them as a block is coherent, and any single reversal names its
own cost (D2 reversal, for example, forces remote errors through
`StoreFailure` strings, violating the typed-error ruling).
