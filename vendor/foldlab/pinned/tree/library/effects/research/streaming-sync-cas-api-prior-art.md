# Streaming and sync CAS APIs — prior art and design implications

Status: conception-mode research, 2026-08-27. **G0 only.** This report does
not ratify an interface, amend the Effect Replay contract, promote a claim,
or establish correspondence between the TypeScript implementation and any
external protocol. Candidate names and shapes below are deliberately
unratified.

Provenance posture: every external source used for a material observation is
linked at an immutable Git commit, tag/edition, or archived specification
edition. The source ledger records the selected Git blob or content digest.
The exact bytes are reproducible from those pins, and their research
resolution is recorded in
[`streaming-sync-cas-api-prior-art.json`](../../../.reference/provenance/receipts/streaming-sync-cas-api-prior-art.json).
Admission into Source Lock remains a separate pending estate action.

## Executive finding

The present R2 API has the right *service separation* but only a stream-shaped
baseline. `CasStore` owns whole admitted nodes; `CasTransfer` names streamed
mechanics; `CasEvents` is advisory; and raw transport stays internal. That
boundary should remain. The current HTTP implementation, however, collects an
upload before issuing it and implements download streaming by loading and
encoding a whole node into one stream element. This is within R2's stated
baseline; it is not progressive wire transfer yet.
([Transfer surface](../src/cas/Transfer.ts),
[remote implementation](../src/internal/remote.ts),
[ratified R2 boundary](../CONFORMANCE-WORKFLOW.md))

The primary-source survey points to two distinct additions rather than one
large "streaming CAS" service:

1. **progressive object transfer** — restartable byte sources, real
   outstanding-capacity control, range reads, optional upload sessions,
   operation progress, and terminal commit receipts; and
2. **graph/root synchronization** — capability negotiation, explicit
   selectors or closure plans, mutable-head policy kept outside the immutable
   store, and a result report that accounts for every requested/discovered
   object.

These should be deep modules: a small ordinary `put`/`load` surface for most
users, with session, range, and sync machinery behind explicit advanced
entry points. REAPI/ByteStream, OCI, tus, and `object_store` independently
separate a convenient one-shot operation from resumable/session mechanics;
GraphSync, Hypercore, and Automerge independently show that synchronization
needs state and control beyond a stream of bytes.
([ByteStream API](https://github.com/googleapis/googleapis/blob/de3c0d362adbaafc7a0cd1254a8cd49a528505ee/google/bytestream/bytestream.proto#L42-L91),
[OCI v1.1.1 upload protocol](https://github.com/opencontainers/distribution-spec/blob/a139cc423184af6078077b9b7ee336eddbd03f8f/spec.md#L317-L424),
[tus 1.0.0](https://github.com/tus/tus-resumable-upload-protocol/blob/c6a11fa3d7b6198e00e4aa5289ccb71314162b84/protocol.md),
[`object_store` multipart API](https://github.com/apache/arrow-rs-object-store/blob/b07471e2bc341278f86e30cf80a850d56cbe2c67/src/upload.rs),
[GraphSync interface](https://github.com/ipfs/go-graphsync/blob/12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0/graphsync.go),
[Hypercore API](https://github.com/holepunchto/hypercore/blob/affec09a56d5f164292c9a3305fbfcde7a40bb85/README.md),
[Automerge sync state](https://github.com/automerge/automerge/blob/47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e/rust/automerge/src/sync/state.rs))

## 1. Current Foldlab baseline

The current public shape has `putStream(source, options) -> ContentId` and
`loadStream(id) -> Effect<Stream<Uint8Array>, ..., Scope>`. `UploadSource`
tags `Replayable` and `OneShot`, but both variants contain the same already-
constructed `Stream` value. The tag is therefore a caller assertion; it does
not provide a fresh opener or a seek/reopen operation as evidence that a retry
can reproduce bytes. ([Transfer](../src/cas/Transfer.ts),
[Remote types](../src/cas/Remote.ts))

At the implementation pin in this repository:

- upload copies chunks into an array and joins them before the transport call;
- download calls whole-node `load`, re-encodes the admitted node, and returns
  one whole canonical-node byte array through `Stream.succeed`; and
- `maxQueuedBytes` rejects an individual input chunk over the limit, but does
  not measure an actual queue of outstanding bytes.

Those observations describe the present mechanics, not a violation of R2's
scope. R2 explicitly selected a spooled whole-object baseline with first-class
stream-shaped interfaces and budgets.
([implementation](../src/internal/remote.ts),
[R2 plan](../IMPLEMENTATION-PLAN.md))

Three surface ambiguities should be resolved before further API freeze:

- **byte domain:** `loadStream` returns the canonical encoded *node*, not the
  node payload; names and receipts should distinguish canonical-node bytes,
  payload bytes, decoded bytes, and wire bytes;
- **scope shape:** `Effect<Stream<...>, ..., Scope>` makes callers acquire an
  effect to obtain a stream; Effect already supports direct scoped streams,
  so a direct `Stream` can own its acquisition/finalization when no separate
  handle is required; and
- **restartability:** a discriminator is weaker than an `open()`/`openAt()`
  capability that constructs a fresh source for each attempt.

Effect's pinned sources define `Stream` as a channel-backed source,
`Stream.unwrap` for an effect producing a stream, and `Stream.scoped` for
placing resource acquisition inside the stream's lifetime.
([Stream type and operators](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Stream.ts#L122-L126),
[`unwrap`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Stream.ts#L1633-L1673))

## 2. Survey of developer-facing patterns

### 2.1 Bazel REAPI and Google ByteStream

REAPI deliberately splits batch CAS operations from large-object ByteStream
operations. It exposes `FindMissingBlobs`, independently-accounted batch
reads/writes, a streaming `GetTree`, and discoverable limits and compressor /
chunking capabilities. ByteStream adds ranged reads and an upload resource
whose server-authoritative `committed_size` can be queried after failure; that
offset may be less than bytes the client previously sent. Completion is an
explicit `finish_write` transition, and the response/query status distinguishes
committed length from completeness.
([REAPI CAS service](https://github.com/bazelbuild/remote-apis/blob/becdd8f9ff811df88a22d3eadd6341753d51d167/build/bazel/remote/execution/v2/remote_execution.proto#L347-L560),
[REAPI capabilities](https://github.com/bazelbuild/remote-apis/blob/becdd8f9ff811df88a22d3eadd6341753d51d167/build/bazel/remote/execution/v2/remote_execution.proto#L2284-L2342),
[ByteStream offsets and completion](https://github.com/googleapis/googleapis/blob/de3c0d362adbaafc7a0cd1254a8cd49a528505ee/google/bytestream/bytestream.proto#L50-L91),
[ranged read fields](https://github.com/googleapis/googleapis/blob/de3c0d362adbaafc7a0cd1254a8cd49a528505ee/google/bytestream/bytestream.proto#L95-L114))

DX lesson: batch, whole-value, and stream APIs are complementary. Resume must
use remote status, not a locally remembered sent count. Capability discovery
belongs in the client boundary, and terminal completion needs a distinct
receipt/status rather than an in-band progress element.

### 2.2 OCI Distribution chunked uploads

OCI Distribution v1.1.1 starts a blob upload with `POST`, returns a session
`Location`, accepts ordered `PATCH` chunks, reports the accepted range, and
rejects out-of-order input with `416`. A status request recovers the current
range. A final `PUT` carrying the *whole-blob* digest publishes the blob.
Downloads may use HTTP ranges and clients are advised to check the requested
digest. Cross-repository mount returns either a completed `201` or a `202`
upload session fallback.
([download and range](https://github.com/opencontainers/distribution-spec/blob/a139cc423184af6078077b9b7ee336eddbd03f8f/spec.md#L188-L204),
[chunk/status/finalize](https://github.com/opencontainers/distribution-spec/blob/a139cc423184af6078077b9b7ee336eddbd03f8f/spec.md#L317-L424),
[mount](https://github.com/opencontainers/distribution-spec/blob/a139cc423184af6078077b9b7ee336eddbd03f8f/spec.md#L426-L461))

DX lesson: an upload location is a scoped operation resource, not the content
address. The client needs begin/status/append/commit/abort semantics even when
the convenience API hides them. Bulk content and mutable manifest/tag
publication remain distinct planes.

### 2.3 tus resumable upload 1.0.0

tus makes the session lifecycle unusually explicit. `OPTIONS` advertises
versions, extensions, and maximum size; `POST` creates an upload resource;
`HEAD` returns the authoritative offset; `PATCH` succeeds only at that offset.
Optional extensions add expiry, termination, per-chunk checksum, deferred
length, and concatenation of partial uploads for parallel transfer. A checksum
mismatch leaves the server offset unchanged. Expired uploads return `404` or
`410`, requiring a new session. Metadata handling includes a header-smuggling
warning.
([tus protocol 1.0.0](https://github.com/tus/tus-resumable-upload-protocol/blob/c6a11fa3d7b6198e00e4aa5289ccb71314162b84/protocol.md))

DX lesson: if Foldlab exposes resumability, `UploadSession` needs an identity,
authoritative status, expiry, abort, and commit. Resume support is not a
boolean capability; it is a state machine with recovery and cleanup.

### 2.4 Rust `object_store`

The Rust `object_store` crate separates atomic whole-object `put` from
`MultipartUpload`. The multipart handle accepts independently-polled parts and
has explicit `complete` and `abort`; its documentation warns that dropping a
handle does not guarantee remote cleanup. `WriteMultipart` adds bounded
concurrency through `wait_for_capacity`, finishes all parts, and attempts an
abort after failure. Reads expose metadata and the actual returned range beside
either a file or byte stream; the store also supports vectored ranges,
conditional writes, and `PutResult` metadata such as ETag/version.
([store interface and read result](https://github.com/apache/arrow-rs-object-store/blob/b07471e2bc341278f86e30cf80a850d56cbe2c67/src/lib.rs),
[multipart and capacity control](https://github.com/apache/arrow-rs-object-store/blob/b07471e2bc341278f86e30cf80a850d56cbe2c67/src/upload.rs))

DX lesson: source/sink symmetry is useful, but the advanced write API should
return a terminal result and own cleanup. Backpressure is a bound on in-flight
work, not just a maximum element size. Range responses should report the range
actually supplied, and remote commit metadata should be retained in a typed
receipt.

### 2.5 Git LFS custom transfers

Git LFS custom transfer adapters negotiate upload/download direction and
concurrency ownership during initialization, then exchange line-delimited JSON
control messages. Bulk content travels through paths outside the control
channel. Each operation is correlated by object ID; adapters emit explicit
progress (`bytesSoFar`, `bytesSinceLast`) and a terminal complete/error event.
On download, Git LFS itself rechecks the object's SHA-256 before moving the
temporary file into its store, making verification ownership explicit.
([custom transfer protocol](https://github.com/git-lfs/git-lfs/blob/09705b99b15cff34b4afb64e468d29f6a77b8b21/docs/custom-transfers.md))

DX lesson: progress and control are operation-local, not global notifications;
the library should state whether it or the adapter checks the address and owns
temporary-file promotion. Concurrency can be adapter-managed or orchestrator-
managed, but the choice must not be implicit.

### 2.6 IPFS blockstore, IPLD selectors, and GraphSync

Boxo's basic blockstore is intentionally small (`Has`, `Get`, `GetSize`,
`Put`, `PutMany`, enumeration). Its optional validating wrapper recomputes the
requested CID on `Get`. The current enumeration API also illustrates an API
hazard: a value channel alone cannot report a late iteration error, so a newer
optional interface supplies a terminal error function after the channel is
drained.
([blockstore interface](https://github.com/ipfs/boxo/blob/63cae36adc96260c55d1e3b8bf5b9f4b78fd7080/blockstore/blockstore.go#L35-L110),
[validating wrapper](https://github.com/ipfs/boxo/blob/63cae36adc96260c55d1e3b8bf5b9f4b78fd7080/blockstore/validating_blockstore.go))

IPLD selectors encode sparse graph traversal as data: field/index/range
selection, recursive exploration with a limit, union, conditional traversal,
and separate notions of blocks covered versus nodes matched. The selected
selector text is explicitly a prescriptive draft, so it is pattern evidence,
not a stable standard. GraphSync's shipped Go interface couples a root CID and
selector with a request ID, priority, extensions, progress and error channels;
it provides cancel, pause/unpause, update, per-request limits, and hooks for
validated blocks. Progress carries logical path/link information and both
logical and on-wire sizes.
([IPLD selector draft](https://github.com/ipld/specs/blob/a7b9376ebd43aeabba7d78487db3d9df456b7714/selectors/selectors.md),
[GraphSync interface](https://github.com/ipfs/go-graphsync/blob/12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0/graphsync.go))

DX lesson: graph selection should be a bounded data type, not a callback run
by an untrusted peer. A selector yields a fetch plan, not evidence of closure.
Every received block still crosses Foldlab admission. Cancellation, progress,
per-request resource limits, and traversal reports belong to the sync
operation. Server-side selection creates an authorization and denial-of-
service boundary.

### 2.7 Nix binary substitution

Nix's binary cache interface accepts a restartable source for upload and a
sink for read. During upload it tees the uncompressed NAR through compression
and hashing, writes the NAR data first, verifies referenced paths, signs the
metadata, and then publishes `.narinfo`; the source is explicitly restarted
before the compressed file is uploaded. On substitution, Nix checks metadata /
signatures, realizes references before the parent, tries another substituter
on absence, and treats a NAR that disappeared after metadata lookup as a
separate `SubstituteGone` case.
([restartable source and publish split](https://github.com/NixOS/nix/blob/2c73b59da29606068c0c98db015dd3a66955525d/src/libstore/include/nix/store/binary-cache-store.hh#L130-L205),
[tee/hash/data-first implementation](https://github.com/NixOS/nix/blob/2c73b59da29606068c0c98db015dd3a66955525d/src/libstore/binary-cache-store.cc#L145-L300),
[substitution closure and fallback](https://github.com/NixOS/nix/blob/2c73b59da29606068c0c98db015dd3a66955525d/src/libstore/build/substitution-goal.cc#L42-L142),
[`.narinfo` fields](https://github.com/NixOS/nix/blob/2c73b59da29606068c0c98db015dd3a66955525d/doc/manual/source/protocols/binary-cache/narinfo.md))

DX lesson: restartability is an operation, not a label; root/metadata
publication is a named boundary after content and references; and absence,
vanished content, integrity rejection, and transport failure should remain
different client outcomes.

### 2.8 XET

XET revision 05 models large files as chunks packed into xorbs plus shards that
describe ordered range reconstruction. Upload is bottom-up (xorbs before their
shard); download uses xorb ranges; operational lookup/index metadata remains
outside logical content identity. Its deduplication design also calls out
cross-access-boundary content-existence leakage. XET is an active individual
Internet-Draft, not an RFC or semantic authority for Foldlab.
([archived revision 05](https://www.ietf.org/archive/id/draft-denis-xet-05.txt),
[§§8–12](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-8),
[security considerations](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-14))

DX lesson: range reconstruction can be first-class data, while physical
offsets, compression, and lookup accelerators remain below identity. Global
dedup discovery must be scoped by authorization/tenant policy.

### 2.9 Hypercore

Hypercore is a signed append-only Merkle log rather than a general immutable
CAS, but its API is valuable sync prior art. It exposes read and byte streams
with snapshot/live and range options, sparse `download` handles with
completion and cancellation, sessions/checkouts/atoms that must be closed,
replication streams, availability/contiguous-length status, fork/truncate
state, and operation events.
([Hypercore API](https://github.com/holepunchto/hypercore/blob/affec09a56d5f164292c9a3305fbfcde7a40bb85/README.md))

DX lesson: a data stream and an operation handle answer different needs. Sync
clients need snapshot versus live intent, a sparse selection, cancellation,
observable availability, and explicit fork/head state. Those semantics should
not be smuggled into immutable `CasStore` reads.

### 2.10 Automerge sync

Automerge's sync protocol separates document semantics from transport and
maintains per-peer `State`. The state tracks shared/local/remote heads,
need/have summaries, sent hashes, in-flight messages, capabilities, and
directionality. Generation may return no message while awaiting acknowledgement
or when the peer is current; message receipt advances session state. Only a
small shared-head subset is persisted for reuse across sessions. The protocol
assumes a reliable in-order byte stream.
([sync protocol implementation](https://github.com/automerge/automerge/blob/47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e/rust/automerge/src/sync.rs),
[peer state](https://github.com/automerge/automerge/blob/47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e/rust/automerge/src/sync/state.rs))

DX lesson: bidirectional sync is a stateful conversation, not a pair of bulk
copies. Foldlab can reuse the explicit-session/capability/head patterns without
importing CRDT conflict semantics. Immutable CAS closure transfer and mutable
root/head reconciliation should remain separate services and policies.

### 2.11 Representative API shapes

These are compact paraphrases of the cited primary interfaces, included to
make their developer experience concrete. They are not compatibility targets.

```text
OCI:       POST uploads/ -> Location
           PATCH Location @ accepted-range -> new accepted Range
           GET Location -> authoritative Range
           PUT Location?digest=<whole> -> published blob

tus:       OPTIONS -> versions/extensions/max-size
           POST -> upload URL
           HEAD upload URL -> Upload-Offset / expiry
           PATCH upload URL @ Upload-Offset -> new offset
           DELETE upload URL -> terminated session       [extension]

object_store:
           put(path, payload) -> PutResult
           put_multipart(path) -> MultipartUpload
           MultipartUpload.{put_part, complete, abort}
           get_opts(path, range/conditions) -> GetResult{payload, meta, range}

Git LFS:   init{operation, concurrent, remote} -> init response
           upload/download{oid, size, action}
           progress{oid, bytesSoFar, bytesSinceLast}
           complete{oid, path?} | error{oid, code, message}

GraphSync: Request(ctx, peer, root, selector, extensions)
             -> (progress channel, error channel)
           Pause / Unpause / Cancel / Update(requestId, ...)

Automerge: generate_sync_message(doc, peerState) -> Message | none
           receive_sync_message(doc, peerState, message)

Hypercore: createReadStream({start, end, live, snapshot})
           download(range) -> { done(), destroy() }
           session() / snapshot() / replicate(...)

Effect:    Stream<A,E,R>                 // values over time
           Sink<A,In,L,E,R>              // consume to a result
           Channel<Out,OutErr,OutDone,...>// values + typed terminal
           HttpBody.stream(stream) / HttpIncomingMessage.stream
           RPC streaming method -> Stream or scoped Queue
```

The source shapes are documented in the
[OCI upload section](https://github.com/opencontainers/distribution-spec/blob/a139cc423184af6078077b9b7ee336eddbd03f8f/spec.md#L317-L424),
[tus 1.0.0 protocol](https://github.com/tus/tus-resumable-upload-protocol/blob/c6a11fa3d7b6198e00e4aa5289ccb71314162b84/protocol.md),
[`object_store` interfaces](https://github.com/apache/arrow-rs-object-store/blob/b07471e2bc341278f86e30cf80a850d56cbe2c67/src/lib.rs),
[Git LFS custom-transfer messages](https://github.com/git-lfs/git-lfs/blob/09705b99b15cff34b4afb64e468d29f6a77b8b21/docs/custom-transfers.md),
[GraphSync public interface](https://github.com/ipfs/go-graphsync/blob/12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0/graphsync.go),
[Automerge sync API](https://github.com/automerge/automerge/blob/47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e/rust/automerge/src/sync.rs),
[Hypercore API](https://github.com/holepunchto/hypercore/blob/affec09a56d5f164292c9a3305fbfcde7a40bb85/README.md), and
[Effect stream/channel APIs](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Channel.ts#L140-L153).

## 3. What Effect v4 already provides at the project pin

The pinned Effect source offers most of the runtime carriers needed; Foldlab
does not need a bespoke stream runtime.

| Requirement | Pinned Effect carrier | Design implication |
| --- | --- | --- |
| Direct byte source | `Stream<A,E,R>` is channel-backed; `HttpIncomingMessage.stream` is a direct byte stream. ([Stream](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Stream.ts#L122-L126), [HTTP incoming](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpIncomingMessage.ts#L57-L69)) | A normal download can return `Stream` directly; acquisition/finalizers can live in the stream. |
| Incremental consumer | `Sink` consumes an input stream to a result and can retain leftovers. ([Sink](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Sink.ts#L63-L71)) | Hash/count/admit and a single upload attempt fit a sink. Retry still needs a fresh source factory. |
| Typed terminal receipt | `Channel` distinguishes output elements, output failure, and output done. ([Channel](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Channel.ts#L140-L153)) | Use `OutDone` internally/advanced API for a completion receipt; `Stream` erases this to `void`. |
| Lifetime and cancellation | `Scope` owns finalizers; sockets expose a scoped writer and channel adapters. ([Scope](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Scope.ts#L45-L49), [Socket](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/socket/Socket.ts#L61-L94)) | Upload sessions, response bodies, temporary spools, and subscriptions belong to operation scopes. |
| Streaming HTTP body | `HttpBody.stream` accepts a `Stream`; `HttpBody.file` supports offset/length/chunk size. ([HTTP body](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/http/HttpBody.ts#L481-L541)) | Progressive HTTP upload and seekable file sources can use existing platform primitives. |
| Streaming RPC | `RpcClient` derives a direct stream result and optionally a scoped bounded queue with `streamBufferSize`. ([RPC client](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/rpc/RpcClient.ts#L80-L121), [queue construction](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/rpc/RpcClient.ts#L436-L470)) | An RPC adapter can share the semantic transfer service while keeping transport framing internal. |
| Nearby remote log sync | `EventLogRemote` authenticates, writes chunked encoded entries, streams changes from a sequence into a scoped queue, and reauthenticates after forbidden responses. ([EventLogRemote](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/eventlog/EventLogRemote.ts#L48-L71), [implementation](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/unstable/eventlog/EventLogRemote.ts#L140-L273)) | Reuse its scoped remote/auth/queue idioms, but do not treat chunked encoded messages as progressive CAS admission or an immutable-store contract. |
| In-memory graph algorithms | `Graph` provides immutable/scoped-mutable directed graphs, snapshots, acyclicity checks, and topological traversal. It does not expose an intrinsically acyclic graph type. ([Graph model](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L1-L184), [`isAcyclic`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L4172-L4298), [`topo`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Graph.ts#L8025-L8120)) | Use it as an internal planning/projection carrier for admitted nodes and dependency edges. Keep CAS identities as node payloads, re-check acyclicity/closure at the owning boundary, and do not serialize `NodeIndex` as a content identity. |

The decisive Effect-specific point is that `Stream` is ideal for values but
not sufficient for a typed terminal result. `Channel` or a small operation
handle should carry completion/commit evidence. Conversely, returning
`Effect<Stream>` is only justified when obtaining the stream also yields a
separate handle or metadata; otherwise `Stream.unwrap`/`Stream.scoped` gives a
cleaner ordinary-user surface.

Effect `Graph` is therefore a clean integration point for a validated
*runtime view* of the CAS DAG and for topological sync planning, but it should
not become the CAS representation or validation authority by itself. Its
numeric node indexes are graph-local identifiers, and `Graph<N,E,"directed">`
can still be cyclic; an adapter must build it from admitted `ContentId` values
and retain the project-owned closure/acyclicity checks.

## 4. Gap map against the current surface

| Concern | Current R2 baseline | Candidate direction (unratified) |
| --- | --- | --- |
| Whole value vs stream | Whole `CasStore`; stream-shaped `CasTransfer`; HTTP collects/emits one whole node | Keep both. Make progressive transfer an implementation/property exercised by conformance tests, not implied merely by a `Stream` type. |
| Byte meaning | `loadStream` says bytes, implementation returns canonical encoded node | Name `canonicalNodeBytes` versus `payloadBytes`; receipts count canonical, payload, decoded, and wire domains separately. |
| Download shape | Nested `Effect<Stream, ..., Scope>` | Ordinary path returns direct scoped `Stream`; advanced path returns a handle/channel only when metadata, progress, cancellation, or terminal receipt is needed. |
| Retry evidence | `Replayable`/`OneShot` tags over identical stream values | `ReopenableSource.open(at?)` constructs each attempt; `OneShotSource.take` can be consumed once. Address is recomputed on every attempt. |
| Backpressure | Maximum per-chunk check | Bound actual queued/in-flight bytes and operations; expose policy/configuration and report observed high-water marks. |
| Resume | No public session/status/expiry/abort | Optional `UploadSession` with remote-authoritative offset, expiry, append, commit, abort, and cleanup result. |
| Range | None | Add only with explicit semantics for the byte domain and verification. Whole-hash CAS cannot promise an admitted arbitrary range without a proof/chunk layout or a full-object spool. |
| Progress | Advisory `CasEvents` plane | Keep global store notifications advisory; add operation-local progress attached to transfer/sync handles and correlated by operation/attempt. |
| Capability discovery | Config assumes a backend shape | Typed `CasCapabilities`: sizes, batch, range/proof mode, resume, compression, selectors, concurrency, publication/receipt classes, protocol revision. |
| Completion | Upload returns `ContentId` | `TransferReceipt` includes ID, committed counts, attempts, dedup/already-present result, completion class, and safe remote metadata. A receipt is observation, not a durability theorem. |
| Graph transfer | Whole-node methods only | `SyncPlan` + `run` + `SyncReport`; selectors and limits are data; every fetched node still uses existing admission. |
| Mutable roots / conflicts | Outside CAS | Keep a separate `CasHeads`/root-publication capability with compare-and-swap and user-selected conflict policy. Do not add mutability to `CasStore`. |

## 5. Candidate deep-module decomposition

The following is a design sketch for grilling, not a declaration freeze.

### 5.1 Layer composition from transport to semantics

The useful seam is three layers deep. Base transport adapters enact bytes and
framing; protocol drivers enact ByteStream/OCI/tus-style sessions; public CAS
services own project identity, admission, graph planning, and user-facing
policy. The internal tags in this illustrative sketch are module-private, so
raw wire bytes never become a user-resolvable CAS service.

```ts
// Illustrative and unratified.

// Layer 1: one transport exchange. Module-private tag / plain value.
interface WireTransport {
  readonly issue: (
    request: WireRequest,
  ) => Channel.Channel<WireEvent, WireFailure, WireCompletion>
}
declare class HttpWire extends Context.Service<HttpWire, WireTransport>()(
  "foldlab/internal/HttpWire",
) {} // layer requires HttpClient
declare class RpcWire extends Context.Service<RpcWire, WireTransport>()(
  "foldlab/internal/RpcWire",
) {} // layer requires RpcClient
declare class SocketWire extends Context.Service<SocketWire, WireTransport>()(
  "foldlab/internal/SocketWire",
) {} // layer requires Socket

// Layer 2: remote protocol mechanics, still module-private.
interface CasTransferDriver {
  readonly capabilities: Effect.Effect<DriverCapabilities, DriverError>
  readonly openRead: (
    id: ContentId,
    range?: ByteRange,
  ) => Channel.Channel<Uint8Array, DriverError, ReadReceipt>
  readonly beginUpload: (
    metadata: UploadMetadata,
  ) => Effect.Effect<DriverUploadSession, DriverError, Scope.Scope>
  readonly findMissing?: (
    ids: ReadonlyArray<ContentId>,
  ) => Effect.Effect<ReadonlyArray<PresenceResult>, DriverError>
}
declare class Driver extends Context.Service<Driver, CasTransferDriver>()(
  "foldlab/internal/CasTransferDriver",
) {}

const byteStreamDriver: Layer.Layer<Driver, InitError, HttpWire> = /* ... */
const ociDriver: Layer.Layer<Driver, InitError, HttpWire> = /* ... */
const tusDriver: Layer.Layer<Driver, InitError, HttpWire> = /* ... */

// Layer 3: exported deep modules. One build shares driver, pools, budgets,
// admitted cache, and operation registry.
declare const casServices: Layer.Layer<
  CasStore | CasBlob | CasTransfer | CasQuery | CasSync | CasEvents,
  CasRemoteInitError,
  Driver
>

const casOverOciHttp = casServices.pipe(
  Layer.provide(ociDriver),
  Layer.provide(httpWireLayer)
)
```

The concrete package may prefer plain factories for `WireTransport` and
`CasTransferDriver` instead of private context tags; the semantic point is the
same. HTTP, RPC, and sockets should be replaceable realizations below one
driver contract. An OCI/tus/ByteStream driver handles remote locations,
offsets, expiry, protocol completion, and capability decoding. Only the public
service layer interprets canonical node bytes, recomputes a `ContentId`, admits
nodes, builds a graph view, or publishes a root.

The proposed public roles are:

| Deep module | Narrow responsibility |
| --- | --- |
| `CasStore` | Existing whole admitted structured nodes. No transport/session vocabulary. |
| `CasBlob` | Optional future large opaque-payload convenience over an approved blob node kind; it must reuse, not redefine, project identity/admission. |
| `CasTransfer` | Progressive canonical-byte movement, retry/source policy, ranges, operation handle, and transfer receipt. |
| `CasQuery` | Shared exact selection semantics, adaptive Merkle planning, local result checking, and lowering to backend primitives. |
| `CasSync` | Compile sync intent into `CasQuery`, account reconciliation, and coordinate with separate root publication. |
| `CasEvents` | Advisory store-level notifications only; operation-local progress remains on transfer/sync handles. |

This composition makes an in-memory driver, hostile conformance driver, HTTP
OCI driver, RPC ByteStream driver, or socket-based experimental driver
substitutable below the same semantic services without presenting them as
interchangeable protocols.

### 5.2 Preserve the simple front door

`CasStore` should remain the backend-independent whole-node service. A normal
user should still be able to put a domain-derived node and load an admitted
node without learning upload offsets, queue capacities, or transport receipts.
`CasTransfer.put`/`loadBytes` can be the progressive convenience surface and
hide single-session orchestration.

```ts
// Candidate vocabulary only.
interface ReopenableByteSource<E = SourceError, R = never> {
  readonly length?: bigint
  readonly open: (range?: ByteRange) =>
    Stream.Stream<Uint8Array, E, R>
}

interface CasTransferShape {
  readonly put: <E, R>(
    source: OneShotByteSource<E, R> | ReopenableByteSource<E, R>,
    options: PutOptions,
  ) => Effect.Effect<TransferReceipt, CasTransferError | E, R>

  readonly loadCanonicalBytes: (
    id: ContentId,
    options?: LoadOptions,
  ) => Stream.Stream<Uint8Array, CasTransferError>
}
```

An opener is operational evidence for a new attempt; it does not assert that
two openings are equal. The existing incremental address check remains the
guard against a source that changes between attempts. The direct download
stream uses `Stream.unwrap` / `Stream.scoped` internally so its resources live
for the stream lifetime without placing `Scope` in the ordinary caller's
environment.

### 5.3 Put sessions behind an advanced interface

```ts
interface CasUploadSession {
  readonly id: UploadSessionId
  readonly status: Effect.Effect<UploadStatus, CasTransferError>
  readonly append: (
    offset: bigint,
    bytes: Stream.Stream<Uint8Array, SourceError>,
  ) => Effect.Effect<UploadStatus, CasTransferError>
  readonly commit: (
    expected: ContentId,
  ) => Effect.Effect<TransferReceipt, CasTransferError>
  readonly abort: Effect.Effect<AbortReceipt, CasTransferError>
}
```

The high-level `put` owns this scope and retries only when the source can be
reopened and the remote processing classification permits it. Direct session
access is for checkpointing, large uploads, or transport-specific tooling.
Session IDs and offsets must never be confused with content identities.

### 5.4 Use a typed terminal internally

The transport/adapter seam can expose a
`Channel<WireOrProgress, Failure, CompletionReceipt>` so data, failure, and
normal completion cannot be confused in-band. The ordinary public `Stream`
can be derived from that channel when the terminal receipt is not needed; an
advanced `TransferHandle` can expose `bytes`, operation-local progress, and a
single terminal `result` while one scope owns all three views.

```ts
interface TransferOperation<A> {
  readonly id: TransferId
  readonly progress: Stream.Stream<TransferProgress>
  readonly result: Effect.Effect<A, CasTransferError>
}

interface CasTransferAdvancedShape {
  readonly startPut: <E, R>(
    source: ReopenableByteSource<E, R>,
    options: PutOptions,
  ) => Effect.Effect<
    TransferOperation<TransferReceipt>,
    CasTransferError | E,
    R | Scope.Scope
  >
}
```

`progress` is advisory state attached to one operation; it should be backed by
a dropping/sliding observation mechanism so an unobserved progress consumer
cannot stall the byte path. `result` is the one authoritative terminal
outcome. Closing the owning scope interrupts local fibers, closes the wire
body, and attempts any protocol cleanup.

This is also the natural place to enforce actual outstanding-byte and
concurrency budgets. A chunk size limit remains a separate parser/input rule.

### 5.5 Give large byte sequences a blob-level module

A progressive canonical-node transfer and a progressive large-file read are
not the same contract. With only one whole-node digest, a client cannot treat
an arbitrary prefix as authenticated until the whole canonical node has been
received and checked. An approved chunk/manifest node kind can instead make
each emitted chunk independently admissible and make range reconstruction a
property of the manifest.

```ts
interface CasBlobShape {
  readonly put: <E, R>(
    source: OneShotByteSource<E, R> | ReopenableByteSource<E, R>,
    options?: BlobPutOptions,
  ) => Effect.Effect<BlobReceipt, CasBlobError | E, R>

  readonly read: (
    root: ContentId,
    options?: { readonly range?: ByteRange },
  ) => Stream.Stream<Uint8Array, CasBlobError>

  readonly stat: (root: ContentId) => Effect.Effect<BlobInfo, CasBlobError>
}
```

`CasBlob` depends on `CasStore` admission, the approved blob descriptor, and
`CasTransfer`; it does not mint a second identity scheme. `CasQuery` can use
Effect `Graph` as a validated in-memory projection of the chunk DAG for
planning and explain output, but a thin public `CasGraph` wrapper would add
interface surface without hiding a substantial new responsibility. Keep the
runtime graph projection behind `CasQuery` unless a later use case establishes
an independent graph capability.

### 5.6 Make sync a separate service

```ts
interface CasSync {
  readonly plan: (
    roots: ReadonlyArray<ContentId>,
    target: SyncTarget,
    selection: BoundedSelection,
  ) => Effect.Effect<SyncPlan, CasSyncError>

  readonly run: (
    plan: SyncPlan,
  ) => Effect.Effect<SyncReport, CasSyncError, Scope.Scope>
}
```

`SyncPlan` should embed or reference a checked shared `MerkleQuery` plan plus
sync-only conflict and publication policy; it must not implement a second
selector evaluator. Its advisory scheduling data includes presence
observations, estimated bytes, and a capability snapshot. `SyncReport`
accounts for requested, discovered, already-present,
transferred, admitted, rejected, missing, and unattempted identifiers plus the
final root/head publication outcome. Neither object is proof of closure merely
because a peer produced it.

For bidirectional operation, session state should name local/remote root sets,
shared observations, in-flight requests, negotiated capabilities, and the
conflict/publication policy. Automerge motivates this explicit carrier, but its
CRDT merge rules do not transfer to an immutable CAS.

### 5.7 Keep mutable publication explicit

OCI manifests/tags, Nix `.narinfo`, Hypercore heads/forks, and Automerge heads
all reinforce one boundary: bulk immutable content transfer and publication of
a mutable or discoverable root are different operations. A future `CasHeads`
or `CasRoots` service can supply compare-and-swap and retention/pinning policy.
It should not be folded into content admission.

## 6. Security ownership

Security is shared, but the ownership line can be crisp.

The library/adapter should own mechanisms that no application can safely
reimplement per call:

- recompute the project address and perform canonical admission before bytes
  become a readable node;
- account encoded, decoded, decompressed, queued/in-flight, and selected-graph
  budgets at the stage where each amount is observable;
- verify remote-authoritative offsets, terminal framing, requested ID, and
  response range; distinguish absence, integrity, protocol, auth, capacity,
  and transport failures;
- scope credentials to authority/tenant, redact them from receipts/events, and
  prohibit credential forwarding across an unapproved redirect;
- bound selector recursion/link count/result bytes and treat remote selection
  as untrusted scheduling input;
- cancel transport work and attempt session abort/temporary cleanup when an
  operation scope closes; and
- make progress/receipts operation-correlated so concurrent operations cannot
  be substituted for one another.

The user or deployment layer should choose policy:

- endpoints, credentials/trust roots, tenant/dedup namespace, allowed
  redirects, and whether discovery may cross an authorization boundary;
- byte/concurrency/deadline/retry limits, resume-state persistence, cleanup and
  retention expectations, and required commit/durability class;
- allowed selectors/roots, sparse versus full closure, and mutable-head
  conflict/publication policy; and
- whether wire compression, ranges, or server-side graph selection are enabled
  for a particular backend.

Capability discovery never overrides user policy. A server saying that it can
execute selectors or retain multipart state is not authorization to use that
feature. XET's content-existence discussion, tus's metadata warning, and
GraphSync's remote selector execution make these boundaries concrete.
([XET §14](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-14),
[tus security considerations](https://github.com/tus/tus-resumable-upload-protocol/blob/c6a11fa3d7b6198e00e4aa5289ccb71314162b84/protocol.md),
[GraphSync responder/request hooks](https://github.com/ipfs/go-graphsync/blob/12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0/graphsync.go))

## 7. Suggested sequencing for later ratification

1. Clarify byte-domain names and replace replayability-as-assertion with a
   source opener, while keeping the current whole-node contract.
2. Make the existing HTTP adapter genuinely progressive and measure actual
   outstanding bytes; retain whole-object spool-before-emission where the
   address scheme cannot authenticate partial content.
3. Add operation-local progress and a terminal `TransferReceipt`, carried by a
   handle or internal `Channel` rather than by ordinary data elements.
4. Add capability discovery and range/vectored reads with an explicit partial-
   verification policy.
5. Introduce resumable upload sessions only after their state/error/expiry /
   cleanup contract and conformance scenarios are frozen.
6. Introduce `CasSync` as a distinct slice with bounded selections,
   plan/run/report accounting, and separate mutable-root publication.

Each step needs its own contract/grilling pass. In particular, "range accepted
for emission", "durable commit", and "sync complete" cannot be public claims until
their exact observations and obligations are named and discharged.

## 8. Lean 4 proof and conformance direction

Status: **Pass-A design, G0 only.** Nothing in this section is a frozen Lean
declaration, a new obligation in the ratified inventory, or evidence that the
TypeScript implementation refines the model. Candidate identifiers beginning
with `CAND-` are discussion handles only. They must not enter
`IMPLEMENTATION-PLAN.md`, `Effects.Conformance.inventory`, or the instance
registry without a separate contract and grilling pass.

This section applies the project's formalization-strategy, invariant-modeling,
and algebraic-systems procedures to the preceding API proposal. The literature
and standards crosswalk in the next section records the evidence class for
each technical decision: normative standard, peer-reviewed or original
literature, shipped-protocol prior art, or explicitly project-owned choice.
Those sources motivate questions and designs; none proves a Foldlab theorem.

### 8.1 Reuse the current proof spine

The future work should extend the present model rather than create a parallel
CAS theory:

- [`Effects.Cas.Node`](../Effects/Cas/Node.lean) already separates full-width
  addresses, typed references, raw nodes, `Node.WF`, and `AdmittedNode`;
- [`Effects.Cas.Codec`](../Effects/Cas/Codec.lean) supplies closed parsing,
  exact decode, round trip, and injectivity over the well-formed domain;
- [`Effects.Cas.Store`](../Effects/Cas/Store.lean) defines the logical partial
  map and `Store.Closed`;
- [`Effects.Cas.Admission`](../Effects/Cas/Admission.lean) gives an executable
  reference checker, clause witnesses, an explicit collision outcome, and
  closure preservation for fresh admission;
- [`Effects.Remote.Machine`](../Effects/Remote/Machine.lean) is the existing
  identifier-correlated sans-I/O client transition system;
- [`Effects.Conformance`](../Effects/Conformance.lean) already provides typed
  schema bundles, model-derived manifests, a registry/ledger projection, and
  quarantined mutants.

The important missing objects are not stronger versions of `Node` or `Store`.
They are chunk recipes, blob/table meanings, checked manifests, server-side
staging and publication state, physical-layout refinement, leases/GC,
selection, and synchronization. Hash assumptions stay on the existing
Level-0/Level-1 lattice: general theorems characterize collisions explicitly,
and injectivity-dependent corollaries carry an `hInj` premise. A standardized
hash implementation does not turn collision resistance into a theorem of the
pure model. This is decision **L01**.

### 8.2 Provisional domain contract

The model should distinguish these objects and observations before selecting
representations.

| Plane | Candidate objects | Client-visible observations | Deliberately excluded facts |
| --- | --- | --- | --- |
| Logical bytes | blob value, byte range, chunk recipe, ordered chunk sequence | reconstructed bytes, logical length, content identifier | pack offset, compression, replica, disk block |
| Logical table | schema, checked row/batch, sequence table or keyed table, selection | rows/keys, projection and predicate result, table root | Parquet writer choices, host object identity, physical file name |
| CAS graph | chunk node, manifest node, typed edges, roots, reachable closure | admitted root, missing/rejected addresses, verified range | server assertion of closure without local checking |
| Transfer | source fragments, attempts, remote offset, completion class | operation progress, terminal receipt, typed failure | durability inferred from an ordinary acknowledgment |
| Server protocol | staged sessions, logical store, published roots, leases, operation IDs | accepted offset, admission, publication, abort, expiry | ambient fiber identity or uncontrolled wall-clock as semantics |
| Physical store | packs, index, compression, replicas, compaction generation | logical lookup result and failure class | physical layout as logical identity |
| Sync | roots, bounded selection, presence observations, plan, report | requested/discovered/transferred/admitted/missing sets | peer-produced plan as proof of closure or convergence |
| Environment | transport delivery, failures, authorization, time, crash, durable media | normalized events and monitored deployment receipts | liveness without fairness/availability assumptions |

The units are bytes, chunk counts, logical rows, offsets, operation/session
identifiers, and graph addresses. Byte ranges should be half-open
`[start, stop)` throughout the owned model; adapters convert protocol-specific
inclusive ranges at one checked boundary. Numeric limits should be named
constants or checked parameters, never unexplained literals in theorem
statements.

The equality choices are semantic:

- blobs use exact byte equality;
- sequence tables preserve row order;
- keyed tables compare the partial map induced by a declared key projection;
- physical layouts compare only through a logical observation relation;
- transfer and server implementations compare by normalized observable traces,
  allowing silent internal steps;
- synchronization compares the admitted selected closure and accounting
  report, not message-for-message traffic.

Bag/multiset table semantics should remain pending rather than be smuggled
into the sequence or keyed carrier. Floating-point NaNs, signed zero,
timestamps, decimal scale, nullability, map-key order, Unicode normalization,
and schema evolution must be decided by the table contract before a canonical
row encoding is frozen. A Parquet or Arrow decoder supplies an external value;
its raw bytes are not automatically the project's canonical table identity.
This is decision **L10**.

Positive witnesses should include an empty blob, a multi-chunk blob with a
range crossing a chunk edge, a sequence table with nulls, a keyed update that
reuses an unaffected subtree, an interrupted upload that resumes from a
regressed server offset, and a sync that discovers an already-present child.

Forbidden examples should include a zero-length interior chunk, a manifest
whose declared length disagrees with its chunks, overlapping/gapped spans, a
wrong-kind chunk reference, an unauthenticated range released early, a table
row violating its schema, a false-negative statistics prune, a published root
with a missing descendant, GC of a leased node, and a report that silently
drops a requested key.

The strongest tempting overclaims must remain falsifiable:

1. `reconstruct (segment bytes) = bytes` does not show that segment boundaries
   are canonical, bounded, or independent of input fragmentation;
2. a valid Merkle path authenticates inclusion relative to a stated root, not
   authorization, freshness, availability, or persistence;
3. a server's accepted parent does not establish that the server retains its
   children;
4. equal addresses imply equal values only under the declared hash premise;
5. a terminal receipt records an observation, not media durability;
6. safety of every reachable state does not prove eventual completion; and
7. synchronization of one bounded selection does not establish full-store or
   future convergence.

### 8.3 Technical decisions to freeze later

| ID | Candidate decision | Reason for the Lean design |
| --- | --- | --- |
| **L01** | Retain the abstract address function and explicit collision branch. | Separates functional store reasoning from external cryptographic assumptions. |
| **L02** | Prove blob chunk/manifest semantics before table semantics. | Tables can reuse admitted blob leaves, ranges, publication, and physical refinement. |
| **L03** | Use `Raw → validate → Checked → semantic projection` at every wire/file boundary. | Invalid manifests, schemas, ranges, checkpoints, and protocol documents require executable diagnostics. |
| **L04** | Give every optimized algorithm a small list-based reference semantics and a named refinement relation. | Functional meaning stays stable while arrays, rolling hashes, parallelism, packs, and indexes change. |
| **L05** | Model durable plans and protocol commands as first-order data, not host continuations or a bare `Monad`. | Plans must be inspected, serialized, replayed, rendered, and interpreted by multiple consumers. |
| **L06** | Keep logical CAS identity separate from compression, packing, replicas, and locations. | Compaction or storage-tier changes should preserve logical observations. |
| **L07** | Version and canonically encode the chunk recipe; include the recipe or its identifier in the manifest identity. | Different segmentation algorithms must not be silently interpreted as the same layout. |
| **L08** | Emit a range early only from independently verified chunks or a checked proof rooted in the requested identity. | A whole-object digest cannot authenticate an arbitrary prefix before whole-object verification. |
| **L09** | Admit content bottom-up and publish the root last through an explicit transition. | Partial uploads remain unreachable and publication has a named linearization point. |
| **L10** | Define table meaning independently of Arrow/Parquet/Iceberg/Delta physical encodings. | Those formats permit representation choices that are not a unique semantic canonical form. |
| **L11** | Model sequence and keyed tables separately; add bag semantics only if required. | Their equality, update, ordering, and scan laws differ materially. |
| **L12** | Specify synchronization first as exact set/closure difference; prove Merkle or probabilistic reconciliation refines it. | An optimization should not define which objects are semantically required. |
| **L13** | Use a transition relation for the open server/environment and total functions for deterministic local algorithms. | Delivery, crashes, concurrency, time, and remote behavior are not controlled by the executor. |
| **L14** | Separate safety theorems from liveness theorems and name fairness, delivery, retention, and availability assumptions. | Reachability induction alone cannot establish progress. |
| **L15** | Reuse existing conformance schemas and model-generated manifests before minting a new family. | Keeps the interface and evidence surface small; new schemas require a demonstrated expressive gap. |
| **L16** | Treat progress, protocol completion, publication, and durability as distinct observations. | One success value must not silently strengthen the server guarantee. |
| **L17** | Make a transport-neutral, first-order Merkle query machine a core module; require optimized planners and transport lowerings to refine its exact selection semantics. | Blob ranges, table scans, graph fetch, synchronization, retention inspection, and remote execution can share one checked planning seam without sharing protocol details. |

The literature and standards crosswalk below assigns evidence to L01–L17 and
marks decisions that remain project-owned despite related prior art.

### 8.4 Representation plan

Use extrinsic invariants by default. Intrinsic indices are appropriate only
when a stable phase changes which operation is legal; they should not carry
tenant policy, retry counts, clocks, scheduler state, or contested remote
facts.

| Subject | Raw carrier | Checked/semantic carrier | Validation and retained data |
| --- | --- | --- | --- |
| Chunk recipe | version/algorithm/parameter bytes | `CheckedRecipe` or subtype satisfying parameter bounds | validator retains version and parameters; proof is erased |
| Byte range | two natural offsets from wire/protocol | half-open `CheckedRange` with `start ≤ stop` and optional total bound | retain offsets; convert inclusive transports explicitly |
| Chunk sequence | list of bytes or incremental chunker state | ordered nonempty chunks whose concatenation is the input | stream state retains rolling window and absolute offset |
| Blob manifest | raw recipe, total length, chunk references/spans | manifest with contiguous coverage, length sum, typed references, and admitted children | retain lengths/offsets for range planning; do not retain proof terms |
| Table schema | raw field/type/default/evolution data | checked schema with unique field IDs and explicit value semantics | retain field IDs, logical types, nullability, revision |
| Record batch | external Arrow/Parquet values or raw cells | rows proven/validated against one checked schema | diagnostic path names field/row and failed clause |
| Table manifest | partition/row-group/column descriptors and stats | manifest whose children agree on schema/layout and whose stats are conservative | retain row counts, ranges, and stats used by execution |
| Upload checkpoint | session token, offset, expiry/capability snapshot | checked checkpoint scoped to authority, protocol, object, and source recipe | all operational witnesses live in `Type`; secrets remain redacted outside Lean JSON fixtures |
| Server state | maps/sets and environment events | state satisfying phase, admission, publication, lease, and accounting invariants | changing policy stays an explicit parameter, not a typeclass |
| Sync report | peer messages and local events | checked accounting partition over the requested/discovered domain | retain each identifier and disposition; summaries are derived |

For algorithm work, the semantic byte carrier may remain the current
`List UInt8`. An optimized executable chunker may use `ByteArray`/`Array
UInt8`; it needs a projection to the list model and operation-refinement
theorems. The optimized representation must not leak into the stable blob
meaning merely because it is faster.

The chunk manifest should initially use an extrinsic `WF` predicate. Checked
construction is common, but decoders and negative fixtures must still
represent malformed manifests. A subtype is appropriate at the admitted
consumer seam after validation. A fully indexed manifest whose length is in
its type would impose dependent arithmetic on every parser and table layer
without eliminating wire validation.

Session phases may later justify a small indexed builder such as
`Upload phase α`, but the server model itself should use raw phase data plus a
reachable-state relation. That lets the model express stale, duplicated,
reordered, expired, or malicious environment inputs rather than making every
invalid scenario unrepresentable.

### 8.5 Semantic layers and refinement chain

Keep six separately reviewable judgments:

```text
bytes
  --segment/reconstruct--> chunk semantics
  --manifest meaning-----> blob semantics
  --schema/layout--------> table semantics
  --server transitions---> admitted/published logical store
  --physical relation----> packs, compression, replicas, durable media
  --transport bridge-----> TypeScript and real protocol observations
```

1. **Reference algorithms.** Pure functions over lists: reconstruction,
   simple fixed segmentation, range slicing, row validation, partition
   concatenation, exact closure, and exact missing-set calculation.
2. **Checked representation.** Raw codecs/validators and `WF` predicates for
   recipes, spans, manifests, schemas, selections, checkpoints, and reports.
3. **Logical CAS adapter.** Project-owned constructors turn verified chunk and
   manifest values into typed `Node`s, reuse `admitNode`/`put`, and prove that
   node-store materialization agrees with the reference semantics.
4. **Open server.** A transition relation separates ephemeral attempt state,
   committed logical state, append-only evidence events, and external
   observations.
5. **Optimized implementation.** Streaming/array chunkers, physical packs,
   indexes, parallel ingestion, and reconciliation algorithms refine their
   simple specifications.
6. **Runtime/transport bridge.** TypeScript normalized decisions and real
   HTTP/RPC/socket traces refine the open-system alphabet on an explicitly
   bounded domain. Deployment durability remains monitored evidence unless a
   storage-system refinement is separately established.

Do not jump directly from a FastCDC implementation, a Parquet writer, or an
HTTP handler to `Store.Closed`. Each crossing needs its own abstraction
relation, preserved observations, and failure mapping.

### 8.6 Candidate declaration DAG

The following dependency order is a skeleton, not a file-creation request.

```text
Effects.Cas.Value / Node / Codec / Store / Admission        [existing]
  ├─ Chunk.Range and Chunk.Recipe
  │    ├─ batch segmentation/reconstruction specification
  │    └─ streaming chunker state and batch-refinement theorem
  ├─ Blob.Manifest
  │    ├─ raw codec + validator + WF
  │    ├─ materialization and range selection
  │    └─ chunk/blob Node adapters + admission refinement
  ├─ Table.Schema / Row / Meaning
  │    ├─ external-value validation and canonical row projection
  │    ├─ sequence-table layout
  │    └─ keyed-tree layout and update semantics
  ├─ Query
  │    ├─ selection syntax and exact selected/support-set semantics
  │    ├─ first-order planner state, observations, and commands
  │    ├─ local result/report checker
  │    └─ optimized-planner and backend-lowering refinements
  ├─ Physical.Layout
  │    ├─ packs/index/compaction relation
  │    └─ logical lookup refinement
  ├─ Server.Ingest
  │    ├─ commands/events/state/step relation/reachability
  │    ├─ staging, resume, admission, publication
  │    └─ operation isolation and receipt observations
  ├─ Server.Retention
  │    ├─ roots/leases/mark/sweep snapshots
  │    └─ protected-reachability preservation
  └─ Sync
       ├─ bounded query compilation and exact closure difference
       ├─ plan/report accounting
       └─ reconciliation through the shared query machine

Effects.Conformance                                      [existing]
  ├─ candidate chunk/blob/table semantic instances
  ├─ candidate server/sync schedule manifests
  ├─ TypeScript bridge runners
  └─ quarantined implementation mutants
```

The first Pass-B freeze should stop after chunk and blob declarations. Table,
server, retention, and sync signatures should each have separate freezes;
otherwise a representation change in one area invalidates an unnecessarily
large proof surface.

### 8.7 Illustrative declaration shapes

These signatures show the intended decomposition, not approved names or
imports.

```lean
namespace Effects.Cas.Chunk

structure RawRecipe where
  algorithm : String
  revision : Nat
  parameters : Bytes

def RawRecipe.WF (r : RawRecipe) : Prop := ...
abbrev Recipe := { r : RawRecipe // r.WF }

structure ByteRange where
  start : Nat
  stop : Nat

def ByteRange.WF (r : ByteRange) : Prop := r.start ≤ r.stop

def reconstruct (chunks : List Bytes) : Bytes := chunks.flatten
def segmentSpec (recipe : Recipe) (input : Bytes) : List Bytes := ...

theorem reconstruct_segmentSpec (recipe : Recipe) (input : Bytes) :
    reconstruct (segmentSpec recipe input) = input := ...

structure StreamState where
  recipe : Recipe
  buffered : Bytes
  offset : Nat
  emittedRev : List Bytes

def feed (s : StreamState) (fragment : Bytes) : StreamState × List Bytes := ...
def finish (s : StreamState) : List Bytes := ...

def runFragments (recipe : Recipe) (fragments : List Bytes) : List Bytes := ...

theorem fragmentation_invariant
    (recipe : Recipe) (fragments : List Bytes) :
    runFragments recipe fragments = segmentSpec recipe fragments.flatten := ...

end Effects.Cas.Chunk
```

`fragmentation_invariant` is stronger and more useful than merely showing that
both paths reconstruct the same input: it states that fragment delivery does
not alter the content-addressed chunk layout.

```lean
namespace Effects.Cas.Blob

abbrev ChunkStore := Addr32 → Option Bytes

structure ChunkRef where
  id : Addr32
  length : Nat

structure RawManifest where
  recipe : Chunk.RawRecipe
  totalLength : Nat
  chunks : List ChunkRef

def RawManifest.WF (H : Bytes → Addr32) (σ : ChunkStore)
    (m : RawManifest) : Prop := ...

abbrev Manifest (H : Bytes → Addr32) (σ : ChunkStore) :=
  { m : RawManifest // m.WF H σ }

def materialize (σ : ChunkStore) (m : RawManifest) : Option Bytes := ...
def readRange (σ : ChunkStore) (m : RawManifest)
    (r : Chunk.ByteRange) : Option Bytes := ...

theorem materialize_manifest_of_segment ... :
    materialize σ manifest = some input := ...

theorem readRange_refines_slice ... :
    readRange σ manifest range = some (slice input range) := ...

def chunkNode (bytes : Bytes) : Node := ...
def manifestNode (m : RawManifest) : Node := ...

theorem admitted_blob_refines_chunkStore ... : ... := ...

end Effects.Cas.Blob
```

The simple `ChunkStore` isolates reconstruction proofs from node framing.
`admitted_blob_refines_chunkStore` is then the explicit adapter back to the
existing typed-node store. Packing is not mentioned in either logical type.

For tables, avoid one carrier that pretends ordered sequences and keyed maps
have the same laws:

```lean
namespace Effects.Cas.Table

structure RawSchema where ...
def RawSchema.WF (s : RawSchema) : Prop := ...
abbrev Schema := { s : RawSchema // s.WF }

structure RawRow where
  cells : List Cell

def RowWF (schema : Schema) (row : RawRow) : Prop := ...
abbrev Row (schema : Schema) := { r : RawRow // RowWF schema r }

structure SequenceMeaning where
  schema : Schema
  rows : List (Row schema)

structure KeyedMeaning where
  schema : Schema
  keySpec : KeySpec schema
  entries : List (Key keySpec × Row schema)
  uniqueSorted : EntriesWF keySpec entries

def scanSequence (q : Selection) : SequenceMeaning → List RawRow := ...
def lookupKeyed (k : Key keySpec) : KeyedMeaning → Option RawRow := ...

def denoteSequence (σ : Store) (root : Addr32) : Option SequenceMeaning := ...
def denoteKeyed (σ : Store) (root : Addr32) : Option KeyedMeaning := ...

theorem sequence_scan_layout_refines ... : ... := ...
theorem keyed_update_refines ... : ... := ...
theorem unchanged_subtree_reused ... : ... := ...

end Effects.Cas.Table
```

`unchanged_subtree_reused` must state the exact algorithm and stability
hypotheses. Reconstruction correctness alone does not imply edit locality;
fixed chunks can shift after insertion, and content-defined/tree split rules
can propagate changes outside a simplistic claimed bound.

### 8.8 Server-side transition model

The client machine cannot establish server staging, publication, retention, or
GC behavior. Add a separate open-system model rather than extending
`Effects.Remote.MachineState` until it contains both endpoints.

Candidate state partitions:

```lean
structure ServerState where
  logical : Store
  staged : SessionId → Option StagedUpload
  published : Std.HashSet Addr32
  leases : LeaseId → Option Lease
  physical : PhysicalState
  evidence : List ServerEvent

structure StagedUpload where
  object : ExpectedObject
  committedOffset : Nat
  chunksRev : List Bytes
  phase : UploadPhase
  capabilitySnapshot : CapabilitySnapshot

inductive ServerInput where
  | beginUpload ...
  | append ...
  | queryCommitted ...
  | commit ...
  | abort ...
  | publishRoot ...
  | acquireLease ...
  | releaseLease ...
  | beginGc ...
  | gcStep ...
  | environmentFailure ...

inductive ServerObservation where
  | sessionCreated ...
  | offsetAccepted ...
  | contentAdmitted ...
  | rootPublished ...
  | aborted ...
  | expired ...
  | rejected ...

inductive Step (P : ServerParams) :
    ServerState → ServerInput → ServerObservation → ServerState → Prop
```

Use a relation because concurrent writers, crashes, expiry, external media,
and delivery are environment choices. Deterministic subroutines—manifest
validation, hashing, exact closure, selection, and one atomic logical update—
remain total functions and can be tested independently.

Model separate linearization points for chunk admission, immutable root
admission, mutable-root compare-and-set, and publication visibility. An upload
session ID, logical operation ID, transport stream, Effect fiber, and content
identifier are five different identities. Fiber-local context may carry the
operation/session correlation at runtime, but the Lean transition relation
should quantify over explicit logical IDs.

The core reachable-state invariants are:

- every resident logical node remains immutable and the logical store remains
  closed;
- staged bytes are not observable through logical load or published roots;
- a published root was admitted and its declared selected closure was present
  at the publication transition;
- each server acknowledgment reports an offset no greater than the bytes the
  server retained for that session;
- terminal admission happens at most once per operation/object even when wire
  messages duplicate;
- unrelated operation IDs cannot alter one another's attempt state;
- physical compaction preserves logical lookup observations; and
- every object protected by the GC snapshot's roots or leases survives that
  collection cycle under the declared write barrier.

The last statement needs a precise collector protocol. A naive theorem saying
"all currently reachable objects survive concurrent GC" is false if roots can
change without a barrier, leases expire nondeterministically, or marking and
sweeping observe different snapshots. The model must choose snapshot-at-start,
incremental-update/write-barrier, epoch, or stop-the-world semantics before
freezing the theorem.

Durability needs its own observation algebra, for example `accepted`,
`verified`, `published`, and `durable class`. The transition model can prove
that a returned receipt corresponds to the event it records. Media durability
requires an implementation/storage assumption or external monitor and must not
be derived from an ordinary transport completion.

### 8.9 Synchronization semantics

Define the exact meaning before the optimized protocol:

```lean
def Reachable (σ : Store) (roots : List Addr32) : Addr32 → Prop := ...

def Selected (σ : Store) (roots : List Addr32)
    (selection : BoundedSelection) : Addr32 → Prop := ...

def Missing (source target : Store) (roots : List Addr32)
    (selection : BoundedSelection) : Addr32 → Prop :=
  fun a => Selected source roots selection a ∧ target a = none

structure SyncReport where
  requested : List Addr32
  discovered : List Addr32
  alreadyPresent : List Addr32
  transferred : List Addr32
  admitted : List Addr32
  rejected : List Addr32
  missing : List Addr32
  unattempted : List Addr32
```

`SyncReport.WF` should say that these dispositions form the declared
accounting partition, with any permitted overlaps explicitly named rather than
inferred. `SyncComplete` should mean that every selected address either was
already admitted or was transferred and admitted, and that the target can
materialize the selected roots. A peer's report is only raw input until local
checking establishes this predicate.

The first reconciliation implementation should be exact enumeration. Merkle
subtree comparison, Bloom filters, invertible Bloom lookup tables, or
protocol-specific presence batches are optimizations with false-positive,
failure, or ordering behavior. Each receives an adequacy/refinement theorem to
the exact `Missing` judgment under named assumptions. No probabilistic data
structure should be placed beneath a theorem that silently assumes exact set
membership.

Bidirectional convergence is a trace property over two server states and a
session carrier. It requires fixed root/conflict policy, reliable or retried
delivery, admission success, bounded mutation during the session, and fairness
or an explicit quiescence premise. The safe early theorem is selected-closure
materialization for a frozen source root, not universal live convergence.

### 8.10 A shared, rigorous Merkle query planner

A core Merkle query planner is warranted, but "planner" should mean a shared
semantic machine rather than one remote-store optimization. Blob range reads,
table scans, selected graph fetches, synchronization, retention inspection,
and repair all ask the same question: from these authenticated roots, which
logical nodes are required, which additional nodes support traversal or
authentication, what is already admitted, and what remains unresolved? This
is decision **L17**.

The deep seam has five parts:

1. **Selector syntax and meaning.** A first-order, canonically encodable
   selector describes root set, node/edge tests, bounded recursion, projection,
   and resource limits. Its denotation over a logical store defines the exact
   selected set. Domain modules compile blob ranges, table predicates, or sync
   selections into this core syntax; they do not add cases to the executor.
2. **Knowledge and presence.** Locally admitted nodes, verified remote
   observations, and untrusted peer hints are different constructors. A remote
   `has` response may guide scheduling, but it cannot discharge local
   materialization or closure unless an explicit backend contract and checker
   justify that implication.
3. **Planner machine.** Because children become known only after a parent is
   loaded, a useful plan is adaptive. Use durable first-order state with a pure
   `start`/`step` function that consumes observations and emits primitive
   commands, rather than a static request list or captured Effect
   continuation.
4. **Execution and lowering.** One backend algebra realizes load, batched
   presence, and optional authenticated-subtree/range primitives. Capability
   negotiation chooses a lowering; HTTP, RPC, SSE, WebSocket, local packs, and
   in-memory stores remain Layers below it. An optimized lowering must refine
   the same abstract command observations.
5. **Local checking.** The terminal report is raw evidence until a checker
   recomputes addresses, validates node codecs and typed edges, accounts for
   the requested domain, and establishes the query's result predicate. The
   peer never gets to certify its own completeness.

The semantic result must distinguish at least `selected`, `support`,
`alreadyPresent`, `transferred`, `admitted`, `rejected`, `unresolved`, and
`unattempted`. `support` is important: an ancestor, index node, or Merkle proof
sibling may be needed to authenticate or locate a result without belonging to
the caller's emitted value set. Conflating support with selection causes both
over-fetch accounting errors and incorrect user-visible results.

An illustrative Lean decomposition is:

```lean
namespace Effects.Cas.Query

inductive RefTest where
  | any
  | ordinal (index : Nat)
  | expectedTag (tag : UInt8)
  | both (left right : RefTest)

inductive Selector where
  | match
  | explore (edge : RefTest) (next : Selector)
  | union (branches : List Selector)
  | recursive (fuel : Nat) (step : Selector)

structure Query where
  roots : List Addr32
  selector : Selector
  budgets : QueryBudgets

def Selected (store : Store) (query : Query) : Addr32 → Prop := ...
def Support (store : Store) (query : Query) : Addr32 → Prop := ...

inductive Command where
  | load (addr : Addr32)
  | findMissing (addresses : List Addr32)
  | loadAuthenticatedRange (root : Addr32) (range : ByteRange)

inductive Observation where
  | loaded (addr : Addr32) (node : Node)
  | presence (present absent : List Addr32)
  | authenticatedRange (root : Addr32) (evidence : RawRangeEvidence)
  | failed (command : Command) (failure : QueryFailure)

structure PlannerState where
  query : Query
  frontier : List Addr32
  seen : List Addr32
  knowledge : Knowledge
  accounting : Accounting

def start (query : Query) : PlannerState := ...
def step (state : PlannerState) (observation : Observation) :
    PlannerDecision := ...

def checkReport (store : Store) (query : Query) (raw : RawReport) :
    Except QueryError CheckedReport := ...

end Effects.Cas.Query
```

This is only a signature sketch. In particular, the recursive-selector
carrier must receive a termination and canonical-encoding review, and an
authenticated range needs a format-specific verifier before it can become a
core observation. The minimum backend can implement only `load` and
`findMissing`; richer commands are optional capabilities with a verified
fallback to the minimum algebra.

The Effect-side boundary should keep planning reusable and execution
ergonomic:

```ts
interface MerkleQueryPlanner {
  readonly start: (query: MerkleQuery) => PlannerState
  readonly step: (
    state: PlannerState,
    observation: QueryObservation,
  ) => PlannerDecision
}

interface MerkleQueryBackend {
  readonly capabilities: Effect.Effect<QueryCapabilities, QueryError>
  readonly execute: (
    commands: ReadonlyArray<QueryCommand>,
  ) => Stream.Stream<QueryObservation, QueryError>
}

interface CasQueryShape {
  readonly run: (
    query: MerkleQuery,
  ) => Effect.Effect<QueryRun, QueryError, Scope.Scope>
}

interface QueryRun {
  readonly events: Stream.Stream<VerifiedQueryEvent, QueryError>
  readonly report: Effect.Effect<CheckedQueryReport, QueryError>
}
```

The exact Effect carrier needs a lifecycle prototype: `events` and `report`
must share one scoped execution and neither may accidentally run it twice. A
single `Channel` with a typed terminal report is the strongest internal
carrier; `CasQuery.run` can expose a guarded scoped projection if that is more
pleasant for ordinary consumers. Cancellation, backpressure, bounded
parallelism, retry, tracing, and fiber-local correlation belong to the
interpreter. Logical operation IDs, planner state, offsets, and correctness do
not depend on fiber identity.

Effect's `Graph` is a useful validated in-process projection after nodes have
been admitted: its traversals and post-order/topological operations can help
schedule loads, uploads, or publication and can render an explain plan. It is
not the durable query carrier. `Graph.NodeIndex` is process-local and mutable
across snapshots, whereas `ContentId` is the CAS identity; the adapter must
retain an explicit `ContentId ↔ NodeIndex` map and never digest or persist a
runtime graph index.

The shared API should therefore be layered as `Query.Semantics` →
`Query.Planner` → `Query.Checker` → `Query.Backend`, with
`Query.GraphProjection` and domain compilers (`Blob.Query`, `Table.Query`,
`Sync.Query`) above or beside the core. This gives users one front door while
keeping exact meaning, optimization, transport, and visualization independently
replaceable and independently testable.

### 8.11 Candidate obligation ledger

These rows are the proposed proof worklist shape. They remain outside the
ratified obligation inventory.

| Candidate | Intended judgment | Primary proof route | Existing conformance fit |
| --- | --- | --- | --- |
| `CAND-CHK-001` | reconstructing batch segmentation yields the original bytes | structural induction / algorithm invariant | `AGREEMENT` |
| `CAND-CHK-002` | streaming segmentation equals batch segmentation for every fragmentation | induction over fragments with buffered-prefix invariant | `AGREEMENT` over fragment lists |
| `CAND-CHK-003` | emitted chunks satisfy nonempty/min/max/final-chunk rules | loop invariant and termination measure | `WF-PRESERVE`, boundary vectors |
| `CAND-CHK-004` | optimized `ByteArray` chunker refines list specification | representation relation and forward simulation | `AGREEMENT` plus differential runner |
| `CAND-BLB-001` | recipe and blob-manifest codecs are closed and exact | parser/encoder induction | `CODEC` |
| `CAND-BLB-002` | manifest validator success implies contiguous coverage, correct total, and resolving typed refs | validator soundness; optional completeness | `REJECTION-CLAUSE` / `FAIL-CLOSED` |
| `CAND-BLB-003` | bottom-up chunk then manifest admission yields a closed store and reconstructable root | induction over admitted chunk list plus existing `put_fresh_closed` | `WF-PRESERVE` |
| `CAND-BLB-004` | verified range read equals slicing the materialized blob | selected-span arithmetic and reconstruction lemmas | `AGREEMENT` |
| `CAND-BLB-005` | interruption emits no unverified byte and admits no partial manifest | reachable-state/trace induction | `TRACE-EXCLUDES`, `FAIL-CLOSED` |
| `CAND-TAB-001` | schema/row canonical projection round-trips on the checked domain | codec and validator soundness | `CODEC` |
| `CAND-TAB-002` | batch fragmentation does not change logical sequence-table meaning | fold/concatenation homomorphism | `HOMOMORPHISM`, `AGREEMENT` |
| `CAND-TAB-003` | column/row-group materialization reconstructs the declared rows | nested induction over groups, columns, rows | `AGREEMENT` |
| `CAND-TAB-004` | layout scan/projection/filter agrees with semantic query | algorithm refinement; conservative-statistics lemma | `AGREEMENT` with false-negative mutants |
| `CAND-TAB-005` | keyed update denotes the specified map update and preserves unaffected subtrees under explicit stability hypotheses | tree invariant and path induction | `WF-PRESERVE`, differential roots |
| `CAND-PHY-001` | pack lookup/compaction returns exactly the logical bytes or a typed failure | abstraction relation and operation simulation | `AGREEMENT` |
| `CAND-ING-001` | staged content is invisible until verified admission | reachable-state trace exclusion | `TRACE-EXCLUDES` |
| `CAND-ING-002` | root publication occurs only after admitted selected closure | reachability induction and publication guard | `TRACE-EXCLUDES` |
| `CAND-ING-003` | resume continues only from a re-queried server offset, including regression | protocol transition induction | `EXACT-STEP`, `FAIL-CLOSED` |
| `CAND-ING-004` | cancellation closes local resources and attempts remote abort without claiming cleanup succeeded | trace property split between required local and best-effort remote observations | `TRACE-EXCLUDES` plus TS fixture |
| `CAND-SRV-001` | interleaved operations remain correlated and cannot substitute bytes, progress, or receipts | invariant over operation map and event IDs | remote schedule manifests |
| `CAND-SRV-002` | receipt class matches the exact completed transition and never implies a stronger class | constructor/step cases | `DISTINCTNESS`, `AGREEMENT` |
| `CAND-GC-001` | roots/leases protected by one collector snapshot survive its sweep under the chosen barrier protocol | mark reachability plus transition induction | hostile GC schedule family |
| `CAND-GC-002` | compaction and collection preserve logical observations of retained addresses | simulation from physical to logical state | `AGREEMENT` |
| `CAND-PLN-001` | exact selector evaluation returns precisely the bounded selected set and separately accounts for authentication/traversal support | induction over selector evaluation and graph reachability | `AGREEMENT`, `FAIL-CLOSED` |
| `CAND-PLN-002` | every planner step preserves frontier/seen/accounting invariants and never emits a command outside its checked budget | reachable-state induction | `WF-PRESERVE`, `TRACE-EXCLUDES` |
| `CAND-PLN-003` | a checked successful report is selection-sound, complete for its declared domain, and locally materializable | checker soundness plus admitted-store closure | `AGREEMENT`, `FAIL-CLOSED` |
| `CAND-PLN-004` | optimized subtree pruning and batched/range planning refine exact selector semantics under explicit knowledge/authentication premises | forward simulation / result refinement | differential runner, hostile presence/proof mutants |
| `CAND-PLN-005` | each backend capability lowering preserves abstract command observations, accounting, failures, cancellation, and terminal class | weak-trace refinement | real-transport conformance lane |
| `CAND-SYN-001` | sync report accounts for every address in its declared domain | finite-set/list partition lemmas | `FAIL-CLOSED` |
| `CAND-SYN-002` | successful frozen-root sync makes the selected closure materializable in the target | induction over dependency order and admission | `AGREEMENT` |
| `CAND-SYN-003` | optimized reconciliation identifies the exact missing set or returns its declared uncertainty/failure | algorithm-specific refinement | differential runner |
| `CAND-SYN-004` | bidirectional convergence under frozen policy, quiescence, delivery, and fairness assumptions | trace/refinement theorem, not finite-step equality | new schema only if `AGREEMENT` cannot express the observation |
| `CAND-BRG-001` | TypeScript chunk/blob/table results agree with Lean-generated vectors on the enumerated domain | manifest bridge | existing bridge lane |
| `CAND-BRG-002` | normalized HTTP/RPC/socket adapter traces refine server/client abstract events | weak-trace simulation plus real protocol suite | transport conformance lane |

Proof completion of a candidate theorem establishes only its stated judgment.
Mutation kills, finite vectors, or interoperability runs test sensitivity and
bridge behavior; they do not upgrade a theorem or establish the unbounded
implementation relation.

### 8.12 Conformance-test design

Prefer the current schema bundles:

- `CODEC` for recipe, manifest, schema, checkpoint, and report encodings;
- `REJECTION-CLAUSE` and `FAIL-CLOSED` for malformed structure and budget
  rejection;
- `WF-PRESERVE` for chunker, manifest builder, server, and GC invariants;
- `AGREEMENT` for batch/stream, reference/optimized, logical/physical, and
  model/runtime relations;
- `HOMOMORPHISM` for batch concatenation or independent partition folds;
- `EXACT-STEP` for offsets, phase transitions, and publication points;
- `TRACE-EXCLUDES` for no early release, no partial admission, no premature
  publication, no credential forwarding, and no cross-operation substitution;
- `DISTINCTNESS` where progress, publication, and durability classes must not
  collapse.

A new `TRACE-REFINES` or liveness family should be considered only after a
real obligation cannot be expressed as `AGREEMENT` over a whole-run observer.
Adding a family merely to match domain terminology would create a shallow
schema.

Lean should generate expectations from executable reference functions, never
hand-maintained JSON. Candidate fixture groups:

1. **Chunk boundaries:** empty/single-byte, cut exactly at minimum/normal/
   maximum, forced maximum, repeated data, every partition of small inputs,
   and large fragments crossing several boundaries.
2. **Manifest validation:** zero interior chunk, wrong sum, overflow/bounds,
   gap/overlap, duplicate refs where disallowed, wrong kind, missing child,
   trailing bytes, unknown recipe/version, and noncanonical ordering.
3. **Range reads:** empty, full, prefix/suffix, one chunk, multi-chunk, exact
   boundary, beyond total, overflow, corrupt selected chunk, corrupt
   unselected chunk under the declared verification policy, and cancellation
   before verification.
4. **Tables:** nulls, empty batch, duplicate field IDs, UTF-8 failure, decimal
   scale, timestamp zone policy, NaN/signed-zero policy, row-group and column
   fragmentation, reordered sequence rows, duplicate keys, schema evolution,
   statistics boundary equality, and malicious false-negative statistics.
5. **Server schedules:** duplicate/reordered append, offset regression,
   truncated final request, commit without finish, cancel during hash/admit,
   publish before child, repeated completion, capability change, two
   operations sharing bytes, stale session, lease expiry, publish concurrent
   with GC, and crash between admission and publication.
6. **Sync:** empty selection, cycle/repeated edge, depth/link/byte budget,
   already-present closure, missing child, peer over-send, peer omission,
   duplicate result, cancellation, conflicting head, and quiescent two-way
   exchange.

The model-derived scenario should carry all scheduled inputs and an explicit
interleaving, following `ManifestRemote.Scenario`; the checker should reject
unreferenced or multiply referenced schedule entries. Expectations should
include results, commands, normalized decisions, terminal receipt/report, and
the observable logical state—not internal `HashMap` iteration order.

Domain-specific mutants should attack one semantic decision each:

- reset the rolling fingerprint at every source fragment;
- allow an empty interior chunk or ignore the final buffered suffix;
- hash compressed/packed bytes instead of canonical logical bytes;
- emit a range before verifying its selected chunk;
- trust a manifest's declared total or a peer's digest without recomputation;
- publish the root before its final child is admitted;
- resume from locally sent bytes instead of the queried offset;
- correlate progress/completion by fiber rather than operation ID;
- prune a table partition on non-conservative statistics;
- let GC ignore a lease or a root published during the protected epoch;
- omit one requested address from sync accounting; or
- treat `published` as `durable`.

Mutants remain implementation/testing artifacts outside the model import
graph. Killing one demonstrates that the enumerated test surface distinguishes
that injected fault; it is not proof of the general theorem.

The end-to-end evidence ladder should stay explicit:

```text
Lean general theorem about owned semantics
  + Lean-generated finite manifest
  + TypeScript runner agreement on that manifest
  + mutation sensitivity for declared faults
  + real-adapter protocol/interop results
  + deployment observations for durability/performance
```

No later lane silently promotes an earlier one. In particular, a protocol
suite can establish observed wire conformance while the semantic adapter
proof remains pending, and a Lean theorem can hold while the TypeScript bridge
is wrong.

### 8.13 Proof engineering and performance

The reference model should optimize for theorem clarity; the executable
bridge should optimize for bounded generation. The existing
[`fp-lean-cas-proof-obligations.md`](fp-lean-cas-proof-obligations.md) guidance
applies directly:

- prove simple functional equivalence before array/loop refinements;
- use strengthened accumulator invariants for streaming chunking, manifest
  building, prefix sums, and topological scheduling;
- state array index bounds explicitly and keep proof-only bounds out of the
  digest preimage;
- use a named decreasing measure for worklists, graph traversals, and
  chunkers whose recursion is not structurally visible;
- split exact parsers and reconstruction lemmas into local helper theorems
  rather than asking the kernel to normalize a whole pipeline;
- keep simp sets local and prefer theorem-driven rewriting over raising
  `maxRecDepth` as a default response;
- separate termination and functional correctness from asymptotic or
  wall-clock performance claims; and
- use `decide`/`bv_decide` only for explicitly finite witnesses or arithmetic
  subgoals under the project's declared trust posture, not as a replacement
  for the general invariant.

Likely proof routes:

| Shape | Route |
| --- | --- |
| list segmentation/reconstruction | structural induction, append/flatten lemmas |
| streaming chunker | induction over fragments and an invariant relating buffer + emitted prefix to the batch input |
| array implementation | loop invariant, index bounds, and refinement to list specification |
| manifest validator | soundness by checker cases; completeness only if required by the interface |
| range planner | prefix-sum/span arithmetic plus selected-chunk reconstruction |
| tree/table update | path/tree induction with ordering and split invariants |
| open server, resume, GC, sync | induction over reachable transitions/traces |
| logical/physical or model/runtime bridge | forward simulation or observation refinement |
| finite protocol vectors | executable reference model and generated manifests |

Avoid a single indexed monad spanning source parsing, chunking, admission,
publication, transfer, GC, and sync. Their phases and failure ownership differ,
and time/remote facts would make legal programs expensive to construct. Use
first-order command data plus pure interpreters; add a small indexed interface
only where it makes an illegal stable local sequence unrepresentable at useful
leverage.

### 8.14 Sequencing and freeze gates

1. **Blob Pass A:** ratify byte equality, range convention, recipe identity,
   chunk/manifest kinds, and the collision posture.
2. **Blob representations:** implement only raw/checked recipe, batch
   segmentation specification, manifest semantics, and node adapters.
3. **Blob Pass B:** elaborate the declaration snapshot and prove
   `CAND-CHK-001`, `CAND-BLB-001`–`004` before an optimized chunker.
4. **Streaming refinement:** add incremental/array state and fragmentation
   invariance, then generate chunk/range vectors.
5. **Query Pass A/B:** freeze first-order selector semantics, selected versus
   support accounting, planner observations, minimum backend algebra, and the
   local success checker before adding subtree/range optimizations.
6. **Server Pass A/B:** freeze staging, offset, publication, receipt, and
   operation-correlation semantics; extend the remote vector architecture.
7. **Physical/retention:** choose pack lookup and one precise collector/barrier
   protocol before stating compaction or GC preservation.
8. **Table Pass A:** separately ratify cell/schema semantics, ordered versus
   keyed meaning, and external-format import boundaries.
9. **Sync Pass A:** freeze domain compilation into the core query, exact
   missing-set semantics, report
   accounting, root publication, and convergence assumptions before choosing a
   reconciliation optimization.
10. **Bridge and assurance review:** only after declarations and proofs compile,
   audit specification intent, proof trust, TypeScript refinement, transport
   evidence, and deployment exclusions as separate claim layers.

At each Pass B, record exact imports, toolchain, declarations, theorem
signatures, allowed axioms/options, positive/negative witnesses, and the
approved edit region. Do not let a proof repair silently change a codec,
recipe, table equality, or server observation.

### 8.15 Trust and falsification boundary

The intended Lean theorems can cover owned pure functions, validators,
logical store transitions, selected protocol traces, and explicit refinement
relations. They do not automatically cover:

- collision resistance or implementation correctness of SHA-256/another
  external hash;
- a foreign Parquet/Arrow/compression/crypto implementation;
- TypeScript `Uint8Array`, HTTP, RPC, sockets, TLS, clocks, filesystems, or
  object stores without a bridge;
- server authorization, availability, or truthful capability statements;
- media persistence, replication, erasure coding, or disaster recovery;
- scheduler fairness and crash recovery outside the modeled transition
  assumptions; or
- production performance and denial-of-service resistance beyond declared
  resource semantics and measured tests.

Every claimed property needs a falsification route. General Lean laws need a
counterexample to the stronger claim; validators need malformed fixtures;
refinements need a diverging mutant; protocols need hostile schedules;
transport adapters need standards/interop cases; durability and performance
need deployment observations. This keeps "correct," "conformant," and
"durable" from collapsing into one unsupported label.

## 9. Literature and standards crosswalk for the Lean design

Status: **G0 evidence map only.** Every Lean name and obligation in this
section is a candidate discussion handle. A standard can define an external
format or protocol, and a paper can establish a result for its own model; neither
proves a Foldlab declaration, implementation, refinement, or deployment claim.
Fixed RFC numbers, publication DOIs/editions, and standards editions are the
bibliographic pins below. Mutable project specifications are linked at exact Git
commits or release tags.

The evidence classes are deliberately distinct:

| Mark | Evidence class | Authority in this report |
| --- | --- | --- |
| **N** | normative standard | Defines requirements only for an implementation claiming that standard. |
| **P** | peer-reviewed or original literature | Establishes the paper's stated algorithm, model, proof, or empirical result under its assumptions. |
| **R** | shipped protocol or project-format specification | Demonstrates an interoperable or deployed design, without making it a general standard. |
| **C** | Foldlab-owned choice | Has related evidence, but its exact semantics and proof obligation must be ratified here. |

This classification prevents a common category error: using a standard hash,
columnar format, or resumable protocol does not standardize the CAS pre-image,
logical table equality, closure judgment, publication guarantee, or
implementation-refinement relation.

### 9.1 Content identity and canonical representation

| Decisions | Evidence and source-owned result | Candidate Lean direction and limit |
| --- | --- | --- |
| **L01** address construction and collision posture | **N:** [RFC 6920](https://www.rfc-editor.org/rfc/rfc6920.html) standardizes names containing a hash-algorithm identifier and digest and discusses checking the name/data binding. [FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4) specifies SHA-2 algorithms. | Retain the current abstract `H : Bytes → Addr`, Level-0 collision characterization, and an explicit Level-1 injectivity premise. RFC 6920 explicitly leaves the hash input to the adopting specification, and a standardized algorithm is not an injectivity or collision-resistance theorem. Candidate adapters must name the algorithm, exact pre-image, verification step, and collision outcome. |
| **L03**, **L07** deterministic manifest/recipe codecs | **N:** [RFC 8949 §4.2](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2) gives core deterministic CBOR restrictions; [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html) fixes an I-JSON canonicalization profile. **P:** [EverParse](https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud) separates parse/serialize round trip, accepted-image exactness, and non-malleability for its generated formats. | These are patterns, not format selections. Candidate codecs still need `decode_encode`, successful-decode exactness, closed-input rejection, and encoding injectivity on the checked carrier. A recipe version and every parameter affecting boundaries belong in the canonical manifest meaning. Merely choosing JSON or CBOR does not supply canonical table semantics; JCS also deliberately preserves rather than normalizes Unicode strings. |
| **L01**, **L07** domain separation | **N:** [RFC 9162 §2.1](https://www.rfc-editor.org/rfc/rfc9162.html#section-2.1) prefixes leaf and interior-node pre-images differently and states why that separation is required in its Merkle construction. | Preserve explicit version/kind/role framing in every new chunk, manifest, table, and proof pre-image. The exact Foldlab tags and upgrade rules remain **C**; RFC 9162 defines a Certificate Transparency tree, not the general CAS DAG. |

The candidate proof stack should therefore remain:

```text
value/manifest WF
  -> codec round trip and exact accepted image              [Level 0]
  -> address is H(canonical framed bytes)                   [Level 0]
  -> equal addresses mean equal bytes or collision witness  [Level 0]
  -> address reflection under a named injectivity premise   [Level 1]
```

No deployment security claim should replace the final two lines with an
unqualified assertion that a concrete digest is collision-free.

### 9.2 Blob chunking, Merkle structure, and authenticated ranges

| Decisions | Evidence and source-owned result | Candidate Lean direction and limit |
| --- | --- | --- |
| **L02**, **L04**, **L07** fixed versus content-defined chunking | **P:** [LBFS](https://doi.org/10.1145/502059.502052) uses content-defined boundaries so shifted files can reuse unchanged regions and confirms candidates with a strong digest. [FastCDC](https://www.usenix.org/conference/atc16/technical-sessions/presentation/xia) supplies an efficient content-defined chunking algorithm and measured chunk-distribution/deduplication behavior. | Start with a simple list semantics and prove candidate reconstruction, determinism, coverage, nonempty/min/max/final-chunk rules, and termination. Then prove the streaming/array/FastCDC-like implementation refines it. Fixed-size chunking remains the cheapest reference baseline. There is no CDC interoperability standard: min/target/max sizes, masks, Gear table or seed, normalization, revision, and end-of-input behavior are **C** recipe data. |
| **L04** fragmentation invariance | The CDC papers define algorithms over a logical byte sequence; they do not prove equality across Foldlab's Effect stream fragmentations. | Candidate `stream_chunker_agrees_batch` must quantify over every fragmentation whose concatenation is the same bytes. Its invariant relates emitted chunks plus buffered suffix to the consumed logical prefix. Resetting rolling state at an Effect element boundary is a required negative mutant. This obligation is wholly **C**, though the algorithm choice is literature-informed. |
| **L02**, **L08** blob manifests and Merkle proofs | **P:** Merkle's original [CRYPTO '87 paper](https://doi.org/10.1007/3-540-48184-2_32) establishes the hash-tree pattern. **N:** RFC 9162 specifies concrete inclusion and append-only consistency proof algorithms for its ordered log. | Candidate manifest laws must separately prove reconstruction, total length, contiguous spans, typed child resolution, and admitted closure. A candidate proof checker needs a theorem from successful verification to membership relative to the stated root. RFC 9162 does not prove general DAG closure, a blob byte range, freshness, authorization, or persistence. |
| **L08** HTTP and cryptographically checked ranges | **N:** [RFC 9110 §§13–14](https://www.rfc-editor.org/rfc/rfc9110.html#section-14) defines conditional and byte-range transfer semantics; [RFC 9530](https://www.rfc-editor.org/rfc/rfc9530.html) distinguishes representation and transferred-content digests. **R:** the pinned [Bao specification](https://github.com/oconnor663/bao/blob/3466bb34287f10f746d29d899d92429b81cf4302/docs/spec.md) demonstrates independently verifiable BLAKE3-tree slices. | `206`, `Content-Range`, and a digest field do not by themselves show that bytes occupy a range of a requested CAS root. Candidate `verified_range_origin` should imply equality with `slice (materialize root)` under the chosen tree/hash premise. Early release requires independently addressed chunks or a checked range proof. Bao is concrete prior art, not a selected Foldlab proof format. |
| **L06** logical chunks versus packs/compression | Existing XET, Nix, OCI, and Git-family formats demonstrate that logical objects may be transferred or stored in aggregate physical forms. No general standard fixes the logical-to-physical refinement. | Candidate `PhysicalRefinesLogical` must make lookup, compaction, repacking, compression changes, and collection preserve logical bytes or return a typed failure. Pack offsets, codec choice, replica, and storage tier must not enter logical identity unless the ratified pre-image explicitly says so. This is **C**. |

Fixed chunking and CDC should therefore be two implementations of one candidate
recipe interface, not two meanings of “blob.” Their roots may differ because
the recipe/layout differs, while both must reconstruct the same logical bytes.
Performance and expected deduplication remain measured properties rather than
Lean functional theorems.

### 9.3 Tables, ordered indexes, and immutable snapshots

| Decisions | Evidence and source-owned result | Candidate Lean direction and limit |
| --- | --- | --- |
| **L10**, **L11** external columnar ingestion | **R:** [Apache Arrow Columnar Format 1.5](https://github.com/apache/arrow/blob/beccec0d0c451b7aa3e4530416ac431b3c035c69/docs/source/format/Columnar.rst) specifies schema/array/buffer/record-batch interchange. [Apache Parquet 2.13.0](https://github.com/apache/parquet-format/blob/c47e2a66e88943fc46fde1b028a9432f14fdf5c0/README.md) specifies the row-group, column-chunk, and page hierarchy. | Use these as checked ingress/egress dialects and execution-layout vocabulary. Neither fixes a unique byte representation of one logical table: batch/page sizing, dictionaries, compression, metadata, and writer choices vary. Candidate `external_decode_sound` relates accepted input to a project-owned `TableMeaning`; candidate canonicalization then addresses that meaning. Raw Parquet-byte identity is a different, narrower contract. |
| **L10**, **L11** table equality and canonicalization | Arrow and Parquet provide type/layout rules, but do not choose Foldlab's equality for row order, keys, nulls, NaNs, signed zero, Unicode, decimal scale, time zones, maps, or schema metadata. | Freeze sequence-table and keyed-table meanings separately. Candidate `table_normalize_deterministic`, `table_codec_exact`, batch-fragmentation invariance, and scan/projection correctness quantify over the selected meaning. Bag semantics and schema evolution remain pending **C** decisions until their equality and observations are explicit. |
| **L02**, **L10** manifest/snapshot hierarchy | **R:** [Apache Iceberg 1.9.2](https://github.com/apache/iceberg/blob/071d5606bc6199a0be9b3f274ec7fbf111d88821/format/spec.md) specifies immutable data/metadata files, manifest lists, snapshots, scan metadata, and an atomic metadata-pointer swap. [Delta Protocol 4.0.0](https://github.com/delta-io/delta/blob/6d055c5c8a2e16bbf4458268a1bc271c7afcc4d2/PROTOCOL.md) supplies another shipped log/snapshot and optimistic-transaction design. | Candidate `TableSnapshot.WF` should connect schema, manifests, child closure, row/partition counts, and conservative statistics. False-negative pruning is forbidden. Both projects are path/location-oriented and permit multiple physical encodings; neither standardizes Foldlab content IDs or proves a CAS closure theorem. |
| **L04**, **L11** ordered keyed updates and structural reuse | **P:** [ForkBase](https://doi.org/10.14778/3231751.3231762) describes structurally invariant reusable indexes and a POS-Tree combining content-defined splits, Merkle hashing, and B+-tree-style query structure for multi-version data. | It supports investigating a keyed-table Merkle/POS/prolly layout. Candidate laws must cover search/range semantics, ordering/split invariants, update meaning, and preservation of unaffected subtree identities under exact stability hypotheses. There is no “prolly tree” standard; Noms, Dolt, and ForkBase encodings/split rules are not interchangeable. |

The decisive server boundary is normalization: decode external values, validate
them against a checked schema, project them to the selected logical table
meaning, and only then build canonical CAS nodes. Hashing whichever bytes an
Arrow or Parquet writer happened to emit is legitimate only when exact file-byte
identity is the declared domain object.

### 9.4 Publication, concurrency, leases, collection, and crashes

| Decisions | Evidence and source-owned result | Candidate Lean direction and limit |
| --- | --- | --- |
| **L09**, **L13**, **L16** staged and conditional publication | **R:** OCI completes blob upload before manifest publication; Iceberg commits immutable metadata then atomically replaces its current metadata pointer; Delta uses optimistic transaction-log commits. **N:** [RFC 9110 `If-Match`](https://www.rfc-editor.org/rfc/rfc9110.html#section-13.1.1) is a transport-level compare-and-set precedent. | Candidate server commands should distinguish stage, verify, admit, publish, and durable observation. Candidate `published_closed` says a visible root was admitted and its selected closure was present at the publication transition. A failed precondition must leave the mutable root unchanged. None of these sources gives media durability, multi-root atomicity, or Foldlab closure automatically. |
| **L09**, **L13** concurrent publication semantics | **P:** [Herlihy and Wing](https://doi.org/10.1145/78969.78972) define linearizability as each completed concurrent-object operation taking effect at a point between invocation and response. | Use a candidate history/trace judgment only if Foldlab promises linearizable root compare-and-set. Name separate linearization points for immutable admission and mutable publication. The literature does not require this consistency level; choosing a weaker contract would require a different observation/refinement judgment. |
| **L13**, **L14** time-bounded retention | **P:** [Gray and Cheriton](https://doi.org/10.1145/74850.74870) introduce leases for time-bounded distributed cache consistency and recovery from holder failure. | Candidate upload/GC leases need explicit holder, resource, grant epoch/time, expiry, renewal, revocation, and recovery semantics. Begin with logical epochs if possible; a timed refinement must name clock monotonicity/skew and durable lease-state assumptions. The paper is not a CAS collector and does not choose lease duration or orphan policy. |
| **L13**, **L14** concurrent reachability collection | **P:** [Dijkstra et al.](https://doi.org/10.1145/359642.359655) demonstrate invariant-driven reasoning for a collector concurrent with graph mutation. | Candidate `protected_not_collected` must be proved over reachable server states under one frozen protocol: snapshot-at-start, stop-the-world, epoch, or an incremental write barrier. Published roots, pins, and unexpired leases define the protected set. Shared-memory tri-colour GC does not solve distributed lease, publication, or crash races by citation. |
| **L06**, **L13**, **L16** durable storage and recovery | **P:** [IFSCQ](https://arxiv.org/abs/2012.07917v1) is a useful mechanized precedent for separating operation postconditions, crash conditions, recovery, and authenticated-storage failures. | A pure `get-after-put`, `published_closed`, or receipt theorem does not establish disk/object-store durability. A later candidate crash/refinement layer must relate physical commits and recovery to a previously committed logical state and make corruption/rollback observations explicit. Until then, durability is an adapter/deployment observation. |

The safety/liveness split in L14 follows directly. Reachability induction can
show that no published root is partial and no protected node is collected.
Eventual publication, collection, or synchronization additionally needs named
fairness, delivery, availability, renewal, and quiescence assumptions; none is
hidden in `ServerState.WF`.

### 9.5 Resume, synchronization, and reconciliation

| Decisions | Evidence and source-owned result | Candidate Lean direction and limit |
| --- | --- | --- |
| **L13**, **L16** resumable transfer | **R:** [tus 1.0.0](https://github.com/tus/tus-resumable-upload-protocol/blob/c6a11fa3d7b6198e00e4aa5289ccb71314162b84/protocol.md) makes the server offset authoritative, checks each patch offset, and defines discovery, expiry, checksum, and termination extensions. Google ByteStream supplies another deployed query/write/completion shape. | Candidate transition invariants should state that retained session bytes equal a prefix of the declared source, accepted offsets never exceed retained bytes, a mismatched offset mutates nothing, and completion/admission occurs at most once. Resume re-queries the server; a caller's sent-byte count is not evidence of retention. Neither protocol defines Foldlab admission or durability. |
| **L12** similar-byte synchronization | **P/R:** [the rsync algorithm](https://openresearch-repository.anu.edu.au/items/15a1c428-0ad3-49d6-bb54-9238250cbbf0/full) uses a rolling weak checksum to locate candidate blocks and a stronger checksum to confirm them. | This is prior art for byte-delta transfer, not CAS set reconciliation and never an admission substitute. Candidate reconstruction must verify final logical bytes/address; weak matches only schedule reuse. |
| **L12** exact set difference | **P:** [Minsky, Trachtenberg, and Zippel](https://doi.org/10.1109/TIT.2003.815784) give characteristic-polynomial reconciliation for similar sets. [Goodrich and Mitzenmacher](https://doi.org/10.1109/ALLERTON.2011.6120248) give invertible Bloom lookup tables whose listing succeeds with high probability below a designed difference threshold. | Define candidate `Missing` by exact finite-set/closure semantics first. An optimized reconciler either returns a checked exact difference or explicit uncertainty/failure and falls back to enumeration. IBLT decoding failure/probability, field sizing, difference bounds, and peer malice must not be erased beneath a total “sync complete” theorem. |
| **L12**, **L14** graph/root synchronization | Existing GraphSync, REAPI `FindMissingBlobs`, Hypercore, and Automerge sources show selectors, presence observations, cancellation, reports, and session state. | Candidate `SyncReport.WF` accounts for every address in its declared domain; candidate frozen-root completion establishes local materialization of the selected closure. Live bidirectional convergence is a later trace theorem under fixed conflict policy, delivery/retry, admission success, bounded mutation/quiescence, and fairness assumptions. |
| **L17** shared Merkle query planning | **N:** RFC 9162 gives exact inclusion/consistency meanings for its particular Merkle log. **R:** the pinned IPLD selector draft defines selectors as data over graph traversal, and GraphSync demonstrates root-plus-selector request/progress/cancel mechanics. **P:** ForkBase supplies ordered Merkle/POS-tree query evidence; [Generic Authenticated Data Structures, Formally](https://doi.org/10.4230/LIPIcs.ITP.2019.10) separates ideal authenticated computation from accepting verification or an explicit collision witness. | Make the exact selected-closure/query meaning primary and transport-neutral. A candidate first-order `Query`, adaptive `PlannerState`/decision machine, `QueryEvent`, and checked `QueryReport` should cover blob ranges, table projections/ranges, graph materialization, sync, and retention inspection. Candidate `planner_refines_query`, `execute_plan_correct`, and per-transport lowering simulations must show that optimization changes scheduling, not denotation. A remote selector, plan, proof, or report is untrusted input until local budget, kind, address, proof, and accounting checks pass. RFC 9162 is not a general query language; IPLD selectors are draft; GraphSync is implementation precedent; ForkBase is one ordered index. The shared IR and its exact semantics remain **C**. |

The architecture implied by the literature is deterministic semantics around
an optional accelerator:

```text
exact selected closure and exact Missing judgment
  -> protocol or probabilistic candidate difference
  -> local exact address, kind, and admission checks
  -> explicit fallback or failure
  -> checked accounting report and optional root publication
```

No probabilistic structure or peer assertion is itself evidence that the
selected closure is complete.

### 9.6 Formal refinement and conformance evidence

| Decisions | Evidence and source-owned result | Candidate Lean/conformance direction and limit |
| --- | --- | --- |
| **L04**, **L13** optimized/model refinement | **P:** [Abadi and Lamport](https://doi.org/10.1016/0304-3975(91)90224-P) treat refinement mappings from lower-level to higher-level state and the role of auxiliary variables. [Lynch and Vaandrager](https://doi.org/10.1006/inco.1995.1134) give forward/backward simulation techniques for untimed systems. | Give every optimized chunker, tree, pack store, server, and adapter an explicit abstraction relation and step/trace simulation to the small reference model. History or prophecy variables are introduced only when the observation mismatch requires them. These papers supply proof methods, not the Foldlab refinement map. |
| **L05**, **L13**, **L15** first-order commands and black-box protocol observations | **P:** [Testing Monadic Code with QuickCheck](https://doi.org/10.1145/581690.581696) uses generated command sequences against a state model. [Tretmans's ioco treatment](https://doi.org/10.1007/978-3-540-78917-8_1) gives a precise input/output transition-system conformance relation including nondeterminism and quiescence. **N:** [ISO/IEC 9646-2:1994](https://www.iso.org/standard/17476.html) separates a system-independent abstract test suite from an implementation under test. | Reify commands, scheduled environment inputs, normalized outputs, quiescence/timeout observations, and explicit verdicts. Candidate `RemoteConforms` must name its trace alphabet and allowed nondeterminism. Completeness of a finite black-box suite requires a bounded domain or explicit fault/test hypothesis; arbitrary-server completeness is unavailable. |
| **L15** generated semantic tests | **P:** [QuickCheck](https://doi.org/10.1145/351240.351266) establishes the generator/property/shrinking pattern. Arrow's official format material also maintains cross-implementation integration vectors. | Generate canonical, malformed, fragmentation, range, table, and hostile-schedule fixtures from executable reference functions and validators. Record seed, size/distribution, discarded cases, and minimized counterexample. Passing finite/random tests is bounded evidence, not the general Lean theorem or runtime refinement. Reusing current conformance schema families remains a project-owned interface choice. |
| **L15** mutation sensitivity | **P:** [DeMillo, Lipton, and Sayward](https://doi.org/10.1109/C-M.1978.218136) provide foundational mutation-testing motivation. | Derive mutants from named obligations: reset CDC state per fragment, trust declared totals, publish early, resume from local bytes, release an unverified range, prune on unsound statistics, collect a leased child, or omit sync accounting. Killing a mutant shows sensitivity to that injected fault only; a mutation score is neither implementation correctness nor theorem adequacy. |
| **L16** evidence and claim separation | ISO abstract-test architecture, ioco, QuickCheck, EverParse, and the refinement literature all distinguish a specification/model result from implementation observations. | Keep the ladder explicit: general Lean theorem; generated finite manifest; TypeScript agreement; mutation sensitivity; real HTTP/RPC/SSE/WebSocket protocol cases; deployment durability/performance observations. No later lane silently promotes an earlier claim. |

A candidate conformance theorem should be intentionally narrow, for example:

```lean
-- Candidate/G0 shape only.
def ObservableConforms
    (spec : AbstractServer) (trace : List WireObservation) : Prop :=
  decodeWireTrace trace ∈ spec.allowedTraces

-- Candidate/G0 bridge obligation only.
theorem adapter_preserves_observation :
  decodeWireTrace (runAdapter schedule) = runAbstract schedule := by
  ...
```

Even this candidate bridge theorem would cover only the modeled adapter and
alphabet. Executing a real-server suite produces observations on enumerated
traces; it does not prove that an arbitrary server universally refines the Lean
system.

### 9.7 Security consequences at the server boundary

Content identity does not imply authority. [Proofs of Ownership in Remote
Storage Systems](https://research.ibm.com/publications/proofs-of-ownership-in-remote-storage-systems)
shows why possession of a short digest alone is an insufficient ownership
test, while [message-locked encryption](https://doi.org/10.1007/978-3-642-38348-9_18)
formalizes security questions arising when keys/encodings are derived from the
message and equality is intentionally exposed for deduplication.

Accordingly, candidate server semantics should keep content verification,
authorization, tenant/dedup namespace, and presence disclosure as separate
judgments. `findMissing`, IBLT summaries, chunk existence, and “already
present” receipts can be presence oracles. Tenant-scoped answers, authorization
before retrieval/publication, rate/budget limits, and explicit equality-leakage
policy are library/deployment mechanisms; the exact policy is **C**. Neither
paper selects Foldlab's security architecture or proves it.

### 9.8 Decisions that literature does not ratify

The sources above leave these decisions entirely with Foldlab:

1. the exact blob, manifest, table, selection, and proof pre-images;
2. byte identity versus semantic-value identity for imported tables;
3. the chunk recipe and whether its full parameters or an identifier enter the
   root;
4. table equality for row order, keys, nulls, numbers, Unicode, maps,
   timestamps, metadata, and schema evolution;
5. a general DAG-closure admission and root-last publication judgment;
6. the authenticated range-proof format and early-release policy;
7. POS/prolly split rules, encoding, update stability, and balancing;
8. logical-to-physical packing, compaction, corruption, and durability
   semantics;
9. lease duration, time/skew model, root set, barrier, orphan retention, and
   crash recovery;
10. publication consistency level and its exact linearization/visibility point;
11. sync selector meaning, report accounting, fallback, and convergence
    assumptions;
12. the transport-neutral Merkle query IR, exact selected-closure denotation,
    proof/report format, plan checker, and transport-lowering boundary; and
13. the runtime observation/refinement boundary and the finite fault hypothesis
    of each conformance suite.

These are not evidence gaps to hide with an additional citation. They are the
domain contract and candidate/G0 Lean obligations that must be frozen before
proof work. The appropriate literature-backed discipline is to give each a
small semantic model, explicit assumptions and negative witnesses, an
executable validator/reference function where possible, and a named refinement
or conformance boundary.

## 10. Source ledger

All sources were read on 2026-08-27. Git blob IDs below identify the exact
selected file contents inside the named commit. No copied code enters this
report.

| Source | Exact pin / edition | Selected file receipt | Role and limit |
| --- | --- | --- | --- |
| [Bazel Remote APIs](https://github.com/bazelbuild/remote-apis/tree/becdd8f9ff811df88a22d3eadd6341753d51d167) | commit `becdd8f9ff811df88a22d3eadd6341753d51d167` | `remote_execution.proto`: SHA-256 `f0b237af779fd1de3a9a3a851915a09de3288538856bc5f5199701e0030cb70d`, 115765 bytes | REAPI v2 CAS/batch/tree/capability API. Protocol prior art only. |
| [Google ByteStream](https://github.com/googleapis/googleapis/blob/de3c0d362adbaafc7a0cd1254a8cd49a528505ee/google/bytestream/bytestream.proto) | commit `de3c0d362adbaafc7a0cd1254a8cd49a528505ee` | `bytestream.proto`: SHA-256 `961b833f35f4bdc51df4bca017cffdba299893e89762bf8041465560106dd3d6`, 7524 bytes | Range/resume/completion API. Not a Foldlab transport selection. |
| [OCI Distribution](https://github.com/opencontainers/distribution-spec/tree/a139cc423184af6078077b9b7ee336eddbd03f8f) | annotated tag `v1.1.1` object `b5c693e819628420cc04ba7d9263628276d8ca0f`; peeled commit `a139cc423184af6078077b9b7ee336eddbd03f8f` | `spec.md` blob `26e64b967d9a1e38e508f3f450500b5c0cf21a30` | Chunked upload and publication prior art. |
| [tus protocol](https://github.com/tus/tus-resumable-upload-protocol/tree/c6a11fa3d7b6198e00e4aa5289ccb71314162b84) | commit `c6a11fa3d7b6198e00e4aa5289ccb71314162b84`; protocol edition 1.0.0, 2016-03-25 | `protocol.md` blob `97f63cdba0a3911f956e1c66002b0187cec5aa4b` | Resumable-session API prior art. |
| [Git LFS](https://github.com/git-lfs/git-lfs/tree/09705b99b15cff34b4afb64e468d29f6a77b8b21) | commit `09705b99b15cff34b4afb64e468d29f6a77b8b21` | `docs/custom-transfers.md` blob `c9e475f812ea8d0bb59f66ef0e6ff60fe8bbce44` | Adapter lifecycle/progress/verification ownership. |
| [IPFS Boxo](https://github.com/ipfs/boxo/tree/63cae36adc96260c55d1e3b8bf5b9f4b78fd7080) | commit `63cae36adc96260c55d1e3b8bf5b9f4b78fd7080` | `blockstore.go` blob `3e12ea5c35ea0a34b96fb897723a8b8f1453e4c2`; `validating_blockstore.go` blob `2e7480dc437c1f43ddbf7d5c790aeecb81d76fdf` | Minimal blockstore and late-terminal-error API evidence. |
| [IPLD selector specification](https://github.com/ipld/specs/blob/a7b9376ebd43aeabba7d78487db3d9df456b7714/selectors/selectors.md) | commit `a7b9376ebd43aeabba7d78487db3d9df456b7714`; document marks itself Prescriptive-Draft | `selectors/selectors.md` blob `cd02236667bb17cd9b7869ee61121d515d7d537d` | Selector data-model prior art; not treated as a stable standard. |
| [go-graphsync](https://github.com/ipfs/go-graphsync/tree/12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0) | commit `12cbffae99eb011ab3da82c5b74e29ec8dc1c6e0` | `graphsync.go` blob `0e374250f107ca53b12c23c3c36bce25aa789014` | Shipped Go API evidence, not a protocol endorsement or proof. |
| [Rust object_store](https://github.com/apache/arrow-rs-object-store/tree/b07471e2bc341278f86e30cf80a850d56cbe2c67) | commit `b07471e2bc341278f86e30cf80a850d56cbe2c67` | `src/lib.rs` blob `7138bdb3a024416c7ba93c0c62e03160e0553de7`; `src/upload.rs` blob `d7d50b1e31d053e43d9d3a4113aed5e5c2c61dc7` | Object/multipart/range API evidence. |
| [Nix](https://github.com/NixOS/nix/tree/2c73b59da29606068c0c98db015dd3a66955525d) | tag `2.35.2` object `a400e1f45939a4e0521f66e76470eea9e8ea666b`; peeled commit `2c73b59da29606068c0c98db015dd3a66955525d` | `binary-cache-store.cc` blob `5294ee7a0330fb247ae268b232d1bbdd52a82a68`; `binary-cache-store.hh` blob `0cc5d1f3ff3f12c3ba33afb4e2ea35b4bd3bcbec`; `substitution-goal.cc` blob `90273493e28803f63cadaeb19f95fbcf5fb2ac5d`; `narinfo.md` blob `e2e2efac0eeb11f3da5d858e3645dac765e1e33a` | Restartable source, publication, closure/fallback API evidence. |
| [XET](https://datatracker.ietf.org/doc/html/draft-denis-xet-05) | `draft-denis-xet-05`, 2026-06-29; source commit [`b29b7d1564b382245aabb65ede5fc9cfc8e93d4c`](https://github.com/jedisct1/draft-denis-xet/commit/b29b7d1564b382245aabb65ede5fc9cfc8e93d4c) | archived text SHA-256 `474d64988f0e28a561403807379e19cfe2c046a43ce39f210c9fdaf55b098a03`, 101863 bytes; source `draft-denis-xet.md` blob `c8fed40144e3a77eb90bf85558ebb9ffefc3d791` | Individual Internet-Draft; range/layout/privacy prior art only. |
| [Hypercore](https://github.com/holepunchto/hypercore/tree/affec09a56d5f164292c9a3305fbfcde7a40bb85) | commit `affec09a56d5f164292c9a3305fbfcde7a40bb85` | `README.md` blob `f39f10632c6d9d746d197e7e0941f2a950dad80a` | Append-only log/sparse replication API evidence; not a general CAS contract. |
| [Automerge](https://github.com/automerge/automerge/tree/47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e) | commit `47908d6c04a0ce3fea0fa1d6b7f5ce6ba3e5792e` | `sync.rs` blob `83377e4bf9549633f60fa6a878b958f82cc8cd5c`; `sync/state.rs` blob `e85f28c62001da64f57763063035bb040a124d39` | Stateful bidirectional-sync API evidence; CRDT semantics are out of scope. |
| [Effect](https://github.com/Effect-TS/effect/tree/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07) | commit `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, corresponding package `effect@4.0.0-rc.111` | `Stream.ts` `4c2f749ac2bba62b41364aff8fa7e674829f3362`; `Sink.ts` `2d5b7ddd8e3de3f6f754f4e5a79dc393b82ea292`; `Channel.ts` `cbd1247629c76703a37e8a36371306e43cacc384`; `Scope.ts` `12e1c6b1bf1a196ef64f4593e36de2b01c6e8e5c`; `Graph.ts` `4a099e3056fc93ba7bec8ad7596a32b5186e4aab`; `HttpIncomingMessage.ts` `1b915334fad875213e71a337e7a463c3de547f37`; `HttpBody.ts` `ae9db9374cbc217a932b6b8dc15438717dcf8330`; `RpcClient.ts` `641e17a60cc1aef172748e131db2988bb2310337`; `Socket.ts` `13eba59fd6c881a0d8100d66ad621e7ec2d5dc5d`; `EventLogRemote.ts` `dc76e650e0151ceb502288d3e36d5eaa95180c8f` | Subject-source runtime/API semantics. No general correctness claim follows from source inspection. |
| [Apache Arrow Columnar Format](https://github.com/apache/arrow/blob/beccec0d0c451b7aa3e4530416ac431b3c035c69/docs/source/format/Columnar.rst) | annotated tag `apache-arrow-25.0.1` object `8bf34803daea7c13f806bf29ee7b09d16773acb2`; peeled commit `beccec0d0c451b7aa3e4530416ac431b3c035c69`; format version 1.5 | `docs/source/format/Columnar.rst` blob `2e81bd0f9424704844cecce7652bc4577d3a963d`, 74443 bytes | Official project format for columnar interchange; not a canonical logical-table identity. |
| [Apache Parquet Format](https://github.com/apache/parquet-format/tree/c47e2a66e88943fc46fde1b028a9432f14fdf5c0) | annotated tag `apache-parquet-format-2.13.0` object `a9f9c3a52bd1d6309038f4d2d3a308978b55c377`; peeled commit `c47e2a66e88943fc46fde1b028a9432f14fdf5c0` | `README.md` blob `1ce553e86e286f821412a617868f2b405d53fd5f`, 14959 bytes | Row-group/column-chunk/page layout specification; valid writer outputs need not be byte-identical. |
| [Apache Iceberg](https://github.com/apache/iceberg/blob/071d5606bc6199a0be9b3f274ec7fbf111d88821/format/spec.md) | annotated tag `apache-iceberg-1.9.2` object `21c5127ef8d8b677c28a566f8951f2a1d14c754d`; peeled commit `071d5606bc6199a0be9b3f274ec7fbf111d88821` | `format/spec.md` blob `7dec296200b722289d7ca8399e481fc1b4948386`, 184975 bytes | Immutable manifest/snapshot and atomic metadata-pointer prior art; location-addressed, not a Foldlab CAS contract. |
| [Delta Protocol](https://github.com/delta-io/delta/blob/6d055c5c8a2e16bbf4458268a1bc271c7afcc4d2/PROTOCOL.md) | annotated tag `v4.0.0` object `a2f4a7194b070a033401a0bbf7f409e679038733`; peeled commit `6d055c5c8a2e16bbf4458268a1bc271c7afcc4d2` | `PROTOCOL.md` blob `639f9caae0c8448ee6f4b201d5c028bfec4d9295`, 166593 bytes | Shipped transaction-log/snapshot/optimistic-commit prior art; not canonical CAS identity. |
| [Bao specification](https://github.com/oconnor663/bao/blob/3466bb34287f10f746d29d899d92429b81cf4302/docs/spec.md) | commit `3466bb34287f10f746d29d899d92429b81cf4302` | `docs/spec.md` blob `e06a23895d63e72cee6be398095ef75fc72176eb`, 18870 bytes | BLAKE3-specific verified-slice prior art; not a selected Foldlab range-proof format or standard. |
| [RFC 6920](https://www.rfc-editor.org/rfc/rfc6920.html), *Naming Things with Hashes* | Standards Track RFC 6920, April 2013; DOI `10.17487/RFC6920` | immutable RFC edition | Hash-algorithm/digest naming and name-data binding. Does not generally define the hash input. |
| [FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4), *Secure Hash Standard* | NIST FIPS 180-4, August 2015 update | DOI `10.6028/NIST.FIPS.180-4` | Normative SHA-2 algorithm specification; does not prove collision resistance or implementation correctness in Lean. |
| [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html), *JSON Canonicalization Scheme* | Informational RFC 8785, June 2020; DOI `10.17487/RFC8785` | immutable RFC edition | Canonical I-JSON profile; not a selected manifest format or semantic table model. |
| [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html), *Concise Binary Object Representation* | Internet Standard STD 94 / RFC 8949, December 2020; DOI `10.17487/RFC8949` | immutable RFC edition, especially §4.2 | Deterministic-CBOR requirements available to adopting protocols; ordinary CBOR is not canonical by default. |
| [EverParse](https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud) | 28th USENIX Security Symposium, 2019, pp. 1465–1482; ISBN `978-1-939133-06-9` | fixed proceedings edition | Verified parser/serializer law vocabulary in EverParse's F*/C boundary; no Foldlab theorem transfers. |
| [A Low-Bandwidth Network File System](https://doi.org/10.1145/502059.502052) | SOSP 2001, pp. 174–187; DOI `10.1145/502059.502052` | fixed ACM proceedings article | Content-defined chunking and strong confirmation of weak candidates; not a Foldlab recipe or proof. |
| [FastCDC](https://www.usenix.org/conference/atc16/technical-sessions/presentation/xia) | USENIX ATC 2016, pp. 101–114; ISBN `978-1-931971-30-0` | fixed proceedings edition | Efficient CDC algorithm and measurements; no interoperability standard or fragmentation theorem. |
| [A Digital Signature Based on a Conventional Encryption Function](https://doi.org/10.1007/3-540-48184-2_32) | CRYPTO 1987, LNCS 293, pp. 369–378; DOI `10.1007/3-540-48184-2_32` | fixed Springer proceedings chapter | Foundational Merkle-tree pattern; not general DAG closure, admission, or persistence. |
| [RFC 9162](https://www.rfc-editor.org/rfc/rfc9162.html), *Certificate Transparency Version 2.0* | Standards Track RFC 9162, December 2021; DOI `10.17487/RFC9162` | immutable RFC edition | Exact Merkle inclusion/consistency algorithms for an append-only CT log; not a generic query/CAS proof format. |
| [RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html), *HTTP Semantics* | Internet Standard STD 97 / RFC 9110, June 2022; DOI `10.17487/RFC9110` | immutable RFC edition, especially §§13–14 | Conditional and range request semantics; no cryptographic range membership or storage durability. |
| [RFC 9530](https://www.rfc-editor.org/rfc/rfc9530.html), *Digest Fields* | Standards Track RFC 9530, February 2024; DOI `10.17487/RFC9530` | immutable RFC edition | Representation/content digest-field semantics; not a Merkle inclusion proof. |
| [ForkBase](https://doi.org/10.14778/3231751.3231762) | PVLDB 11(10), 2018, pp. 1137–1150; DOI `10.14778/3231751.3231762` | fixed PVLDB article | Structurally invariant reusable indexes and POS-Tree prior art; no standard prolly-tree encoding. |
| [Linearizability](https://doi.org/10.1145/78969.78972) | ACM TOPLAS 12(3), 1990, pp. 463–492; DOI `10.1145/78969.78972` | fixed journal article | Candidate correctness condition for concurrent publication only if that guarantee is selected. |
| [Leases](https://doi.org/10.1145/74850.74870) | SOSP 1989, pp. 202–210; DOI `10.1145/74850.74870` | fixed ACM proceedings article | Time-bounded consistency/protection precedent; not a CAS collector or clock model. |
| [On-the-Fly Garbage Collection](https://doi.org/10.1145/359642.359655) | Communications of the ACM 21(11), 1978, pp. 966–975; DOI `10.1145/359642.359655` | fixed journal article | Concurrent-collector invariant precedent; shared-memory algorithm does not solve distributed CAS GC. |
| [IFSCQ](https://arxiv.org/abs/2012.07917v1) | arXiv `2012.07917v1`, 2020 | versioned publication | Mechanized authenticated-storage/crash-recovery precedent; no theorem about a future Foldlab backend. |
| [The rsync Algorithm](https://openresearch-repository.anu.edu.au/items/15a1c428-0ad3-49d6-bb54-9238250cbbf0/full) | ANU Joint Computer Science Technical Report TR-CS-96-05, June 1996 | repository item `15a1c428-0ad3-49d6-bb54-9238250cbbf0` | Similar-byte delta algorithm; not exact set reconciliation or admission. |
| [Set Reconciliation with Nearly Optimal Communication Complexity](https://doi.org/10.1109/TIT.2003.815784) | IEEE Transactions on Information Theory 49(9), 2003; DOI `10.1109/TIT.2003.815784` | fixed journal article | Characteristic-polynomial set reconciliation under its bounds/field assumptions. |
| [Invertible Bloom Lookup Tables](https://doi.org/10.1109/ALLERTON.2011.6120248) | 49th Allerton Conference, 2011; DOI `10.1109/ALLERTON.2011.6120248` | fixed IEEE proceedings article | Probabilistic difference recovery; decoding failure cannot be hidden by an exactness claim. |
| [The Existence of Refinement Mappings](https://doi.org/10.1016/0304-3975(91)90224-P) | Theoretical Computer Science 82(2), 1991, pp. 253–284; DOI `10.1016/0304-3975(91)90224-P` | fixed journal article | Refinement-mapping method and auxiliary-state precedent; no Foldlab mapping supplied. |
| [Forward and Backward Simulations, Part I](https://doi.org/10.1006/inco.1995.1134) | Information and Computation 121(2), 1995, pp. 214–233; DOI `10.1006/inco.1995.1134` | fixed journal article | Untimed simulation proof techniques; no runtime correspondence follows by citation. |
| [QuickCheck](https://doi.org/10.1145/351240.351266) | ICFP 2000, pp. 268–279; DOI `10.1145/351240.351266` | fixed ACM proceedings article | Generated properties and shrinking; finite randomized success is not proof. |
| [Testing Monadic Code with QuickCheck](https://doi.org/10.1145/581690.581696) | Haskell Workshop 2002, pp. 47–59; DOI `10.1145/581690.581696` | fixed ACM proceedings article | Model/command testing precedent; no exhaustive concurrency guarantee. |
| [Model Based Testing with Labelled Transition Systems](https://doi.org/10.1007/978-3-540-78917-8_1) | peer-reviewed FORTEST chapter, 2008, pp. 1–38; DOI `10.1007/978-3-540-78917-8_1` | fixed Springer chapter | ioco black-box conformance and quiescence precedent; complete finite suites need explicit hypotheses. |
| [ISO/IEC 9646-2:1994](https://www.iso.org/standard/17476.html) | International Standard, second edition, December 1994 | ISO reference `ISO/IEC 9646-2:1994` | Abstract-test-suite architecture; OSI scope and no proof of a modern CAS implementation. |
| [Hints on Test Data Selection](https://doi.org/10.1109/C-M.1978.218136) | IEEE Computer 11(4), 1978, pp. 34–41; DOI `10.1109/C-M.1978.218136` | fixed journal article | Foundational mutation-testing rationale; mutation sensitivity is not correctness. |
| [Generic Authenticated Data Structures, Formally](https://doi.org/10.4230/LIPIcs.ITP.2019.10) | ITP 2019, LIPIcs 141, article 10; DOI `10.4230/LIPIcs.ITP.2019.10` | fixed open-access proceedings article | Isabelle ideal/prover/verifier and explicit-collision precedent; not the candidate shared query IR. |
| [Proofs of Ownership in Remote Storage Systems](https://doi.org/10.1145/2046707.2046765) | ACM CCS 2011, pp. 491–500; DOI `10.1145/2046707.2046765` | fixed ACM proceedings article | Digest possession is insufficient ownership evidence; no selected Foldlab authorization scheme. |
| [Message-Locked Encryption and Secure Deduplication](https://doi.org/10.1007/978-3-642-38348-9_18) | EUROCRYPT 2013, LNCS 7881; DOI `10.1007/978-3-642-38348-9_18` | fixed Springer proceedings chapter | Deduplication/equality-leakage security model; not a Foldlab encryption decision. |

## Boundary of this report

The survey supports API and conformance-test design choices only. It does not
show that Foldlab implements any surveyed protocol, that its current streaming
surface performs progressive network I/O, that a remote receipt proves
durability, that a selector result is a complete closure, that two peers
converge, or that any implementation satisfies a Lean model. Those remain
separate obligations with exact judgments if pursued.
