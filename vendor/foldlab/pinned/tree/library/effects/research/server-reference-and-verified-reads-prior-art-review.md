# Prior-art and usability review: reference server, blobs, and partial reads

STATUS: **G0 conception review**. This document evaluates
[`server-reference-and-verified-reads.md`](server-reference-and-verified-reads.md)
against the current Foldlab estate and revision-pinned primary sources. It does
not ratify a profile clause, change the implementation plan, or transfer a
correctness claim from any cited system.

Evidence notation:

- **E** — behavior observed in a revision-pinned external source or immutable
  publication.
- **I** — behavior observed in the current Foldlab model, profile, or
  TypeScript implementation.
- **F** — a Foldlab-owned recommendation. The source is precedent or
  falsification evidence, not authority for the recommendation.
- **O** — an obligation still owed before the associated claim can advance.

## 1. Conclusion

The target direction is right in four important respects: one package should
make a useful client and reference peer available together; blobs should be
ordinary CAS graphs rather than a parallel store; proof-carrying reads should
remain below a high-level `CasBlob` interface; and storage should vary behind a
real adapter seam.

The design is not yet safe to ratify. Four corrections are blocking:

1. **The proposed range wire alphabet is not the Lean decoder's alphabet.**
   `DInput` has `parentNode(left,right)`, `chunkNode(bytes)`, and a
   payload-free `skipNode`; the target text specifies only a hash-bearing skip
   record and a chunk record. An honest generated stream necessarily contains
   parent records. No byte codec can refine the current machine until this is
   reconciled.
2. **The current client publication theorem is not a server durability or
   remote-closure theorem.** It shows when the client machine may record a
   publication decision from its observations. It does not establish that a
   peer retained the closure, that storage survived a crash, or that a root
   registry update was atomic.
3. **A leaf-or-parent root is too weak an evolution envelope for a public blob
   format.** It has no uniform place for recipe identity, total byte length,
   tree root kind, and future migration data. A small `BlobManifest` root node
   solves this while keeping the blob one ordinary CAS graph.
4. **`CasServerStore` is underspecified.** Admission, write-if-absent conflict
   behavior, read revalidation, visibility, durability, root compare-and-set,
   garbage-collection leases, and capability truth cannot be compressed into
   an unnamed “pluggable storage” promise.

The best usability improvement is not more public primitives. It is three deep
modules with small interfaces:

```text
CasBlob                 CasServerCore                 CasConformance
put/get/stream/slice    admit/load/publish/prove      run(profile, authority)
        |                       |                            |
        +---- CasStore ---------+---- CasObjectStore --------+
                                      CasRootRegistry
```

Callers should normally learn `CasBlob.put`, `CasBlob.get`,
`CasBlob.stream`, `CasBlob.slice`, `CasTransfer.push`, and
`CasRepository.ref`. HTTP records, Merkle frames, dependency ordering,
restartability, and adapter atomicity should remain implementation knowledge.

## 2. What the current estate already gets right

### 2.1 The existing proof and runtime spine should be extended

**I.** The current implementation already has a useful separation:

- `CasStore.put/load` owns canonical node admission and revalidation;
- `CasTransfer` owns streamed transport, missing negotiation, graph push, and
  root publication;
- the remote machine owns request/event decisions independently of HTTP;
- `Effects.Merkle` owns a chunk recipe, tree, inclusion verifier, streaming
  decoder, and named laws;
- conformance schemas and mutants make each obligation observable.

The target should extend that spine. It should not introduce a second
“server CAS” node representation or a second Merkle language.

### 2.2 Stored canonical bytes are a strong choice

**I.** Foldlab's memory store retains the exact canonical node bytes and
recomputes the requested address on load. This keeps read validation local to
one codec and one hash call.

**E.** Unison deliberately separates its logical hashing representation from
its compact SQLite serialization. A `HashHandle` connects those layers, and
verification reconstructs logical objects before hashing. The schema uses
`hash_object` to associate multiple versioned hashes with one stored object.
This is useful migration prior art, but it also demonstrates the verification
complexity of storing a different representation. See pinned
[`HashHandle.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase-sqlite/U/Codebase/Sqlite/HashHandle.hs)
and
[`create.sql`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase-sqlite/sql/create.sql).

**F.** Keep canonical node bytes as the semantic storage value in the first
filesystem and reference-server adapters. Packing, compression, or database
local IDs may be added later as physical layouts only after a decode/re-encode
refinement and crash-recovery story exist.

### 2.3 Shared codecs reduce drift, but do not make drift impossible

The target says one codec module makes client/server drift “structurally
impossible.” That is too strong.

**I.** Sharing one encoder and decoder removes a common form of duplicated-code
drift. It does not establish that the codec matches the profile, that the byte
parser refines the parsed machine, or that a shared bug is detected. A client
and server can agree on the same wrong implementation.

**F.** Replace the claim with: one shared codec implementation reduces
intra-package mismatch; exactness theorems, generated vectors, and a runtime
refinement gate independently constrain it.

## 3. Blocking correctness findings in the target document

### 3.1 P0 — range-stream syntax contradicts `DInput`

**I.** The current decoder declares:

```lean
inductive DInput (A : Type) where
  | parentNode (left right : A)
  | chunkNode (bytes : Bytes)
  | skipNode
```

`genStream` emits a `parentNode` before the selected children, and emits a bare
`skipNode` for a disjoint subtree. The target's proposed body has only:

```text
0x00 + 32-byte hash
0x01 + u32 length + chunk bytes
```

That representation has no parent record and gives skip a hash the model does
not consume. The decoder cannot authenticate a descendant without first
receiving and checking the parent's two child addresses.

**F.** Freeze one of these alternatives before Q2:

```text
0x00 | left:32 | right:32       parent
0x01 | length:u32 | bytes       chunk
0x02                            skip
```

or change `DInput` and every affected theorem to a different, fully specified
alphabet. The first option directly mirrors the current machine. Every frame
must be closed, length-bounded, and reject trailing bytes.

**O-WIRE-ALPHABET.** `decodeFrame(encodeFrame(x)) = x`, successful decoding is
exact canonical encoding, and the byte parser's output is precisely the
`DInput` list consumed by `drun`.

### 3.2 P0 — parsed-input composition is not byte-fragmentation refinement

**I.** `drun_append` proves composition over lists of already parsed `DInput`
values. It does not mention arbitrary `Uint8Array` fragment boundaries,
partial length fields, short network reads, or EOF in the middle of a record.

**E.** Bao's pinned specification explicitly calls out short reads as both an
interoperability and security pitfall, and requires implementations to keep
reading until the requested bytes are obtained or return an error. Its slice
format carries parent nodes on the path before returning chunk bytes. See
[`docs/spec.md`](https://github.com/oconnor663/bao/blob/3466bb34287f10f746d29d899d92429b81cf4302/docs/spec.md#decoder).

**F.** Add a separate sans-I/O frame parser and prove or test the bridge:

```text
parseFold(fragmentationA) = parseFold(fragmentationB)
  when flatten(fragmentationA) = flatten(fragmentationB)
```

The TypeScript mirror should consume arbitrary byte chunks, not assume one
network chunk per proof record.

**O-PARSER-FRAGMENT.** All fragmentations of one complete canonical body yield
the same parsed inputs and terminal; truncations never yield completion.

### 3.3 P0 — “root-bound” requires the current theorem's hypotheses

The target says every emitted chunk is root-bound “by construction.” The
current Lean result is more precise.

**I.** A step emits after the leaf preimage hashes to the expected frame
address. Run-level agreement with a committed chunk list requires honest
frames and yields either the committed bytes or an explicit collision witness.
The abstract hash is not assumed injective by default. The wire parser and
TypeScript implementation are also outside this theorem.

**F.** State the eventual runtime property using a named judgment:

```text
PrefixAccepted(profile, expectedRoot, requestedByteRange, trace, emitted)
```

and claim “root-checked prefix” only after:

1. the expected root was obtained through the caller's declared trust path;
2. the manifest and proof records refine the Lean inputs;
3. each emission is licensed by the decoder; and
4. the theorem retains its equality-or-collision conclusion unless a separate
   hash assumption is declared.

The server proves membership relative to a supplied root. It does not prove
that the root is the one the user intended.

Q3's honest-generator completeness result does not by itself establish the
adversarial property needed at the remote boundary: every range accepted from
an untrusted server originated at the requested root and requested positions.
That requires a separate accepted-range origin/binding judgment over arbitrary
input traces. Its conclusion must remain `expected bytes ∨ hash collision`
until an explicit collision-resistance assumption is admitted.

**O-ADVERSARIAL-RANGE.** For every input trace accepted for `(root, lo, hi)`,
the emitted sequence is the committed sequence at those positions, or the
trace supplies a collision witness; completeness for `genStream` is a separate
honest-server theorem.

### 3.4 P0 — client root-last is not server publication correctness

**I.** The client machine's confirmed and published sets are observations and
decisions inside that model. A successful remote acknowledgment does not imply
media durability, crash survival, server closure, or linearizable root update.
The profile currently makes server closure checking optional.

**E.** OCI makes blob completion precede manifest publication; Nix writes data
before cache metadata; Unison recursively saves causal parents before the
causal and, in sync, commits a batch transaction only after validation. These
are implementation precedents, not a Foldlab theorem. See pinned OCI v1.1.1,
Nix 2.35.2, and Unison
[`SyncV2.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/unison-cli/src/Unison/Share/SyncV2.hs#L196-L209).

**F.** Introduce a server transition system before using “reference server” as
evidence for root visibility. At minimum it needs states for staged bytes,
admitted objects, protected roots, mutable root heads, and durability class.

**O-SERVER-PUBLISH.** A successful root-head transition implies the manifest
and selected closure were admitted at that transition, the update obeyed its
compare-and-set precondition, and no failed transition changed the visible
head. Crash survival is a distinct adapter/refinement property.

### 3.5 P0 — byte ranges and chunk ranges are conflated

The proposed header carries leaf `total`, `from`, and `count`, while the public
surface reads like byte slicing. The current Lean decoder uses chunk indices.

`DParams.total` is supplied by the server, and a slice generator need not visit
the final chunk. The current success state therefore does not authenticate the
claimed total chunk count or total byte length. Do not expose a
`lengthValidated` result from this path. Either bind both values in an
authenticated blob descriptor/manifest, or require a proof that reaches and
validates the final edge before reporting them as checked.

**F.** Public `CasBlob.slice` should accept a byte range. An internal planner
maps it to the intersecting leaf interval and trims the verified first and last
chunks. The manifest commits to `totalBytes`, `leafCount`, and `recipeId`.
Specify strict or clamped bounds once; do not inherit Bao's permissive behavior
accidentally. Use an encoded unsigned 64-bit byte offset/length even if the
first implementation imposes a lower configured limit.

**O-BYTE-SLICE.** Successful byte slicing equals
`flatten(wholeChunks).drop(offset).take(length)` under the declared bounds.
This is stronger than the existing chunk-index slice agreement and should be a
separate theorem.

### 3.6 P1 — `maxBlobBytes` currently names a node-body limit

**I.** The current capability field bounds a single transferred canonical
node. A chunked blob is intended to exceed it. Calling it `maxBlobBytes` makes
the new public blob abstraction misleading.

**F.** Keep the eight-byte `/0` field's wire meaning stable, but document it as
the maximum canonical node body accepted by `/0`. In the next profile use
`maxNodeBytes`; publish independent range/proof/manifest limits. Blob support
requires the effective node limit to hold every leaf, parent, and manifest
node—not merely the raw chunk size.

## 4. Unison: the most useful estate precedent

Unison should be used here as a production design study, not as a proof source.
Its strongest lessons are about long-lived identity, indexing, synchronization,
and human interaction with hashes.

### 4.1 Stable logical hashing is distinct from physical storage

**E.** Unison prepends hashing version `Tag 2` in its logical token pipeline.
The SQLite schema separately stores object bytes, primary hashes, a
`hash_object` relation, and `hash_version`. One object may be reachable through
multiple hashes after rehashing. Exact sources:

- [`Tokenizable.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/unison-hashing-v2/src/Unison/Hashing/V2/Tokenizable.hs#L28-L50)
- [`create.sql`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase-sqlite/sql/create.sql#L33-L82)
- [`Queries.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase-sqlite/U/Codebase/Sqlite/Queries.hs#L1007-L1033)

**F.** Foldlab should not copy the alternate storage codec yet, but it should
reserve a migration plane now:

- persistent keys remain full `ContentId` values;
- a derived alias/index may map legacy scheme addresses to one canonical
  stored object;
- indexes and aliases never become evidence that bytes match an address;
- every scheme/version has a registered decoder and address function;
- unknown versions fail closed.

This prevents a future hash or recipe upgrade from becoming an all-at-once
server migration.

### 4.2 Validation belongs before admission, not behind a speed flag

**E.** Unison's `validateTempEntity` recomputes hashes for terms,
declarations, namespaces, patches, and causals and reports hash/encoding
failures. Its V2 sorted stream validates batches and saves them in a
transaction; validation may run concurrently with insertion, but the
transaction does not commit before validation succeeds. See
[`EntityValidation.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/unison-share-api/src/Unison/Sync/EntityValidation.hs)
and the V2 transaction cited above.

**F.** The public reference server should have no “skip validation” option.
A benchmark-only unchecked adapter, if ever needed, should be explicitly named
`Unsafe...`, excluded from the reference server, and unable to produce a
conformance verdict.

### 4.3 Dependency-first streaming and bounded unordered ingestion

**E.** Unison exposes a tiny worklist interface:

```haskell
data TrySyncResult entity = Missing [entity] | Done | PreviouslyDone | NonFatalError
data Sync m entity = Sync { trySync :: entity -> m (TrySyncResult entity) }
```

On `Missing deps`, it prepends dependencies and retries the entity. The newer
V2 path supports a dependency-sorted stream that can be inserted incrementally
and an unsorted stream that is buffered and topologically sorted. See
[`U.Codebase.Sync`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase-sync/U/Codebase/Sync.hs)
and
[`SyncV2.sortDependencyFirst`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/unison-cli/src/Unison/Share/SyncV2.hs#L269-L309).

**F.** Keep children-first `push` as the default because it streams with
bounded memory. Add an optional server composite for interoperability:

```text
ingestUnordered(stream, { maxStagedNodes, maxStagedBytes })
  -> complete | MissingDependencies | BudgetExceeded
```

It stages untrusted nodes, admits only ready nodes, reports exact missing
dependencies, and publishes nothing until the requested roots are closed. It
must not weaken `CasStore.put`'s dependency-first admission rule.

### 4.4 Names, short hashes, and ambiguity are a user interface plane

**E.** Unison's `ShortHash` is explicitly a query syntax over a hash prefix,
optional cycle position, and constructor id. Its database indexes base32 text
for prefix search. The query can match multiple objects; the full hash remains
identity. See
[`ShortHash.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/core/Unison/ShortHash.hs)
and the `hash_base32` index in `create.sql`.

**F.** Add a separate inspection/resolution module, never short-id overloads on
`CasStore.load`:

```ts
type ResolveResult =
  | { readonly _tag: "Resolved"; readonly id: ContentId }
  | { readonly _tag: "Ambiguous"; readonly candidates: ReadonlyArray<ContentId> }
  | { readonly _tag: "NotFound" }

CasInspect.resolve("a41f...")
CasInspect.describe(id)
CasInspect.closure(id)
CasInspect.explainRead(blob, range)
```

Short forms belong in CLI/UI and must never authorize a write, root update, or
security decision without unique full-id resolution.

### 4.5 Causal roots make mutable names auditable

**E.** Unison models a causal value with a causal hash, value hash, parents,
and lazy value. Its SQLite schema stores the causal and many-to-many parent
relation separately; root namespace points at a causal. See pinned
[`Causal.hs`](https://github.com/unisonweb/unison/blob/84b95a623711b57b9ff7163f124b214d626b81e4/codebase2/codebase/U/Codebase/Causal.hs)
and `causal`/`causal_parent` in `create.sql`.

**F.** Keep immutable content and mutable root heads separate. A usable server
should eventually expose named refs whose value is a content-addressed update
record:

```text
RootUpdate { name, previous?, next, actor?, message?, timestamp? }
```

The mutable registry stores only the current update id. Updates use
compare-and-set, corresponding to HTTP `If-Match` semantics in
[RFC 9110 §13.1.1](https://www.rfc-editor.org/rfc/rfc9110.html#section-13.1.1).
Authorship and timestamps are metadata unless the profile deliberately puts
them in the update identity.

### 4.6 Schema versions and indexes are operational design, not afterthoughts

**E.** Unison checks a stored schema version, runs explicit migrations, and
maintains indexes for hash prefixes, dependency/dependent queries, types,
mentions, names, causal parents, and recent history. Its migration 18 adds a
dependency lookup index independently of object identity.

**F.** Every persistent Foldlab adapter should have:

- an explicit physical schema version unrelated to CAS scheme version;
- startup refusal or an explicit migration path on unknown versions;
- rebuildable derived indexes for prefix, references, reverse references,
  roots, and reachability;
- a `doctor` command that revalidates canonical bytes and reports stale index
  rows;
- no index row that can bypass full address checking.

### 4.7 Unison's mistakes reinforce Foldlab's framing discipline

**E/I.** The estate's pinned Unison study documents two relevant failure
classes: an unframed token stream can admit ambiguous concatenations, and
incomplete domain tagging/canonical ordering can make logically distinct
carriers collide or make recursive ordering partial. Foldlab's node codec
already uses explicit version, kind, and length frames.

**F.** Blob and proof formats must preserve this discipline at every layer:
separate manifest, parent, leaf, and chunk-data kinds; explicit frame tags;
exact lengths; ordered refs; and a recipe identifier in the manifest. Do not
rely on the fact that the surrounding HTTP path says “proof.”

## 5. What the dedicated CAS systems add

### 5.1 Comparative findings

| Source | Exact external behavior (**E**) | Foldlab implication (**F**) |
|---|---|---|
| Git `v2.55.0` | Object identity commits to a type/length-framed object; wire negotiation and pack storage are distinct from loose-object identity; refs are mutable names. | Keep canonical identity, physical packing, negotiation, and mutable refs as separate planes. A future pack adapter must not change ids. |
| Nix `2.35.2` | Binary-cache data is written before metadata; narinfo carries references and hashes; substitution tries sources and realizes closure. | Publication metadata follows content. Closure and source fallback belong in a deep workflow, with source-specific failures retained. |
| Boxo `63cae36...` | The blockstore interface is small (`Has`, `Get`, `GetSize`, `Put`, `PutMany`, iteration); a validating wrapper checks blocks against CIDs. | A small immutable object-store port plus a validating core is credible. Iteration errors and late failures must remain visible. |
| IPLD selectors `a7b937...` / GraphSync `12cbff...` | A root plus selector describes traversal; requests expose progress, completion, error, cancellation, and limits. | Reuse the shared Merkle/CAS query planner for graph/range reads. Do not make each endpoint invent traversal and accounting. |
| REAPI `becdd8...` | `FindMissingBlobs`, batch reads/writes, and paginated `GetTree` separate presence, transfer, and traversal. | Preserve `missing`, `push`, and traversal reports; make batch accounting exact. Presence never admits. |
| ByteStream `de3c0d...` | `Read` uses offset/limit; streamed `Write` carries offset and finish; `QueryWriteStatus` makes server retention authoritative for resume. | If resumable blob upload is added, retained server offset—not client sent bytes—controls restart. |
| OCI Distribution `v1.1.1` | Blob upload supports staged/chunked completion; manifests publish only after referenced blobs exist; blob GET has standard range precedent. | Distinguish staging, admission/completion, and publication. HTTP range semantics alone do not authenticate a byte range to a Merkle root. |
| XET draft `-05` | Chunks have reusable content hashes; higher layers commit to ordered hash/size terms; shard indexes and truncated lookup accelerators are separate from full identity. | Preserve chunk dedup independently of position, bind order in leaf/manifest nodes, and keep short/index keys collision-checked and non-authoritative. |
| Bao `3466bb...` | Parent chaining values precede chunks in a pre-order encoding; a valid chunk may be released after its path is checked; length cannot be exposed before final-chunk validation; encodings may be malleable. | Parent frames are mandatory. Separate content authenticity from canonical wire exactness and from validated total length. |

Exact repository identities are reused from
`remote-cas-wire-sweep-sources.json` and
`streaming-sync-cas-api-prior-art.json` in the provenance receipt.

### 5.2 Standards boundaries

- [RFC 6920](https://www.rfc-editor.org/rfc/rfc6920.html) is naming-with-hashes
  precedent, not a Foldlab node codec.
- [RFC 8949 §4.2.1](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2.1)
  demonstrates that deterministic encoding rules must be explicit; Foldlab's
  binary codec remains project-owned.
- [RFC 9162](https://www.rfc-editor.org/rfc/rfc9162.html) defines inclusion and
  consistency for its Merkle log shape. It does not standardize this blob tree,
  query planner, or proof stream.
- [RFC 9110 §14](https://www.rfc-editor.org/rfc/rfc9110.html#section-14) defines
  HTTP range semantics. A `206` response is not cryptographic membership
  evidence.
- [RFC 9530](https://www.rfc-editor.org/rfc/rfc9530.html) defines HTTP digest
  fields. A digest of the response content is useful transport evidence but
  does not, by itself, prove that a partial response belongs to the requested
  CAS root.

## 6. Recommended deep-module architecture

### 6.1 External module: `CasBlob`

This is the developer-facing abstraction. It hides recipe selection, stream
fragmentation, local staging, Merkle construction, graph push, proof parsing,
and first/last-chunk trimming.

```ts
export type BlobRef = ContentId & BlobRefBrand

export interface CasBlobShape {
  readonly put: (
    source: Stream.Stream<Uint8Array, CasError>,
    options?: { readonly recipe?: BlobRecipeId }
  ) => Effect.Effect<BlobRef, BlobError, CasStore>

  /** All-or-nothing materialization; no bytes escape on a late failure. */
  readonly get: (
    ref: BlobRef
  ) => Effect.Effect<Uint8Array, BlobError, CasStore | CasTransfer>

  /** Root-checked prefix semantics; a later terminal error remains visible. */
  readonly stream: (
    ref: BlobRef
  ) => Effect.Effect<Stream.Stream<Uint8Array, BlobError>, BlobError, Scope.Scope>

  readonly slice: (
    ref: BlobRef,
    range: ByteRange
  ) => Effect.Effect<Stream.Stream<Uint8Array, BlobError>, BlobError, Scope.Scope>

  readonly inspect: (ref: BlobRef) => Effect.Effect<BlobInfo, BlobError>
}
```

`BlobRef` is a phantom/brand over the same full `ContentId`; it is not a second
wire identity. This gives callers kind safety without violating the one-store
decision.

`put` should first admit the constructed graph to the local `CasStore`. Once
that completes, remote retries read replayable nodes from CAS even if the
original input stream was one-shot. This removes most `Replayable`/`OneShot`
complexity from ordinary blob callers.

### 6.2 External module: `CasRepository`

Content ids are not a complete application UX. Applications need stable names,
optimistic updates, history, and resolution.

```ts
export interface CasRepositoryShape {
  readonly resolve: (name: RootName) => Effect.Effect<RootHead, RefError>
  readonly compareAndSet: (
    name: RootName,
    expected: RootRevision | "absent",
    next: ContentId
  ) => Effect.Effect<RootHead, RefError>
  readonly history: (name: RootName) => Stream.Stream<RootUpdate, RefError>
}
```

This module can later store root updates as CAS nodes while the mutable adapter
holds only each name's head. It should remain optional for applications that
need anonymous content only.

### 6.3 Internal deep module: `CasServerCore`

HTTP handlers should decode, call this module, and encode. The core owns all
semantic policy:

```ts
export interface CasServerCoreShape {
  readonly capabilities: (principal: Principal) => Effect.Effect<ServerCapabilities>
  readonly load: (principal: Principal, id: ContentId) => Effect.Effect<CanonicalNodeBytes, ServerError>
  readonly admit: (principal: Principal, id: ContentId, bytes: Uint8Array) => Effect.Effect<AdmissionReceipt, ServerError>
  readonly missing: (principal: Principal, ids: ReadonlyArray<ContentId>) => Effect.Effect<PresenceReport, ServerError>
  readonly publish: (principal: Principal, command: PublishCommand) => Effect.Effect<RootHead, ServerError>
  readonly prove: (principal: Principal, query: MerkleQuery) => Effect.Effect<ProofStream, ServerError, Scope.Scope>
}
```

The interface earns depth: admission, closure checks, quotas, leases, receipt
accounting, proof generation, and adapter normalization stay behind six
operations.

### 6.4 Real adapter seams

There are at least two genuine seams because memory, filesystem, and future
object/database stores vary independently from the protocol:

```ts
export interface CasObjectStoreShape {
  readonly get: (id: ContentId) => Effect.Effect<Uint8Array, ObjectNotFound | StorageError>
  readonly putIfAbsent: (
    id: ContentId,
    admitted: AdmittedNodeBytes
  ) => Effect.Effect<"stored" | "present", StorageError>
  readonly hasMany: (
    ids: ReadonlyArray<ContentId>
  ) => Effect.Effect<ReadonlyArray<boolean>, StorageError>
  readonly properties: Effect.Effect<ObjectStoreProperties, StorageError>
}

export interface CasRootRegistryShape {
  readonly get: (name: RootName) => Effect.Effect<RootHead, RefNotFound | StorageError>
  readonly compareAndSet: (command: RootCasCommand) => Effect.Effect<RootHead, RefConflict | StorageError>
}
```

Deletion, scanning, repair, and garbage collection belong in a separate
operator-facing `CasMaintenanceStore`. They should not enlarge the ordinary
server store interface or become remotely reachable by accident.

### 6.5 Capability truth is an intersection

The target derives capabilities from policy alone. The truthful document is:

```text
effective capabilities
  = protocol implementation
  ∩ authenticated-principal policy
  ∩ object-store properties
  ∩ root-registry properties
  ∩ configured resource limits
```

Identity-defining recipe parameters must never be selected silently by a
server. A server may truthfully advertise the set of recipe ids it supports;
the caller/profile still chooses the recipe. If capabilities vary by principal,
HTTP caching must vary on the authorization context or be disabled.

## 7. Blob representation: keep one graph, add a manifest and dedup layer

### 7.1 Recommended logical graph

```text
BlobManifestV0
  payload: recipeId | totalBytes | leafCount
  ref[0]: Merkle root

BlobParentV0
  ref[0]: left subtree
  ref[1]: right subtree

BlobLeafV0
  payload: absoluteIndex | chunkLength
  ref[0]: ChunkDataV0

ChunkDataV0
  payload: raw chunk bytes
```

All four are ordinary canonical CAS nodes. The blob id is the manifest node's
ordinary `ContentId`.

This is deeper than embedding `(index, bytes)` directly in the leaf:

- the leaf remains position-bound;
- identical raw chunks deduplicate across positions and blobs;
- the manifest uniformly commits recipe and total-length data;
- empty and one-chunk blobs have the same root kind;
- future recipes can coexist without an out-of-band reinterpretation;
- a proof checks chunk bytes to `ChunkDataV0`, then the indexed leaf, then its
  parent path, then the manifest's tree reference.

The cost is one leaf wrapper and one extra lookup per chunk. Measure that cost
against real workloads before replacing it with an inline-leaf recipe.

### 7.2 Position binding is not the same as chunk identity

The target currently makes the leaf preimage `(index, chunk bytes)`, so equal
bytes at different positions have different node ids. BLAKE3's chunk counter
is relevant to tree binding, but it does not force a CAS to use the indexed
leaf as the reusable storage chunk.

**E.** XET gives raw chunks their own hashes and commits order and size at the
file/xorb aggregation layers. **F.** The leaf-wrapper design adopts that
separation without adopting XET's format. It preserves the current
position-binding theorem shape while recovering cross-position dedup.

### 7.3 Recipe identity and evolution

The chunker and tree shape are different parameters. `pow2Below` defines the
binary tree split; it is not the chunk boundary algorithm.

The manifest's `recipeId` should resolve to a frozen record such as:

```text
BlobRecipeV0 {
  chunking = Fixed { bytes }
  tree = LeftBalancedBinaryPow2Below
  leaf = IndexedChunkReference
  hashScheme = CasScheme0
  empty = OneEmptyChunk
}
```

Start with fixed-size chunking because it matches the current proof carrier and
is easy to stream. Content-defined chunking is a future recipe, not a runtime
tuning flag. LBFS, FastCDC, XET, restic, and Borg are evidence that CDC improves
reuse under insertions; none makes one parameter set canonical for Foldlab.

**O-RECIPE-EVOLUTION.** A reader selects semantics from the manifest recipe id;
unknown ids fail closed; old recipes remain readable; changing any
identity-affecting parameter changes the manifest id.

### 7.4 Proof stream and inclusion document

For the current decoder, the minimum parsed record set is parent/chunk/skip.
With referenced chunk nodes, a chunk record must carry enough information to
recompute both `ChunkDataV0` and `BlobLeafV0`, or the stream must carry the leaf
record explicitly. The exact choice belongs in the model before the wire.

An inclusion opening must reject:

- `index >= leafCount`;
- a sibling count inconsistent with the derived tree path;
- an oversized chunk or proof;
- a chunk length inconsistent with the recipe/final position;
- a manifest recipe/type mismatch;
- trailing or unknown records.

The current abstract decoder absorbs further inputs once it is `done`; that is
appropriate only as an internal machine convenience. The wire framer must
require exactly one complete response and reject every extra frame or trailing
byte after completion.

The response requires both output-budget and proof-amplification budgets. A
tiny requested range must not license an unbounded parent stream.

### 7.5 Two read semantics are necessary for honest UX

Early emission is useful, but it cannot offer all-or-nothing consumption. A
consumer may act on a checked prefix before a later record is truncated.

Expose the distinction in method names and docs:

- `get` — materialize/spool, validate completion, then return; atomic to the
  caller.
- `stream` / `slice` — emit each root-checked prefix chunk when licensed;
  preserve any later terminal failure. Cancellation leaves an observed prefix
  and no completion receipt.

Do not describe a prefix stream as a successfully read blob until its terminal
is complete. Progress events are advisory and never admission evidence.

## 8. Server storage, crash, and concurrency semantics

### 8.1 Admission state machine

The server should expose a receipt only after these conceptual stages:

```text
receive bounded bytes
  -> closed canonical decode
  -> address recomputation
  -> kind/reference checks
  -> write-if-absent
  -> duplicate revalidation or conflict
  -> admitted acknowledgement
```

`AdmittedNodeBytes` should be an opaque internal type constructed only by the
core. Adapters accept it; they do not perform protocol decoding themselves.
Loads revalidate bytes before returning them across the semantic seam.

### 8.2 Duplicate and collision behavior

Write-if-absent has three semantic outcomes:

- absent and stored;
- already present with identical canonical bytes;
- same id associated with different/corrupt bytes.

The third is not “already present.” It is an integrity fault that should fail,
be observable, and prevent publication. Claims that address equality means
byte equality remain conditional on the declared hash hypothesis.

### 8.3 Durability must be named

Memory, filesystem, SQLite, and cloud object stores do not mean the same thing
by success. Define a small declared class, for example:

```text
volatile | processPersistent | crashPersistent | replicated
```

These labels are project-owned and would need exact operational judgments.
The memory adapter may truthfully advertise only `volatile`. A filesystem
adapter claiming crash persistence needs a temp-write, file flush, atomic
rename/replace, directory flush, restart scan, and corruption behavior pinned
for each supported platform. A protocol `200` must not silently be described as
durable without that adapter evidence.

### 8.4 Root updates and garbage collection

Immutable objects simplify concurrency, but mutable root heads and deletion do
not. Root publication should use compare-and-set. Closure checking and head
update must hold a reachability lease or otherwise exclude GC for the selected
closure. A GC pass marks from a root snapshot plus active leases; sweep may
delete only nodes outside both sets. A failed publish changes neither head nor
lease-protected objects.

This is later than the first append-only filesystem reference server. Making
the first adapter append-only is a valid way to postpone—not solve—the GC race.

## 9. Effect v4 implementation and packaging direction

### 9.1 Keep authoritative dependencies visible in layers

The current package pins Effect `4.0.0-rc.111` at source commit
`0dd7825e...`. At that pin:

- `HttpRouter` supplies route layers, `serve`, and a Fetch-compatible
  `toWebHandler`;
- `HttpServerResponse.stream` accepts a `Stream<Uint8Array, E>`;
- `ChannelSchema` encodes/decodes schema values at channel boundaries;
- `Graph` supplies directed graph snapshots, cycle checks, DFS/BFS, and
  topological traversal.

These are implementation aids, not semantic authorities.

**F.** Prefer this assembly shape:

```ts
const CasApplication = CasServerHttp.routes.pipe(
  Layer.provide(CasServerCore.layer),
  Layer.provide(CasObjectStore.layerFile(config.directory)),
  Layer.provide(CasRootRegistry.layerFile(config.refsDirectory)),
  Layer.provide(CasServerPolicy.layer(config.policy))
)

const NodeServer = HttpRouter.serve(CasApplication).pipe(
  Layer.provide(NodeHttpServer.layer(config.listen))
)
```

The convenience `CasServer.layer(config)` may compose defaults, but authority,
credentials, persistence, and platform server providers must remain visible in
its requirement type or explicit config. Tests substitute memory adapters at
the same seams.

### 9.2 Use streams and channels where they add real leverage

- `Stream` is the public backpressured body and verified-output carrier.
- a private `Channel`/sans-I/O parser owns partial frame state;
- `ChannelSchema` may validate already-delimited records if its codec fits, but
  it does not replace the custom incremental binary framer or its refinement;
- server work is scoped; disconnect/interruption closes the proof generator;
- bounded queues use suspending backpressure, never dropping proof or content
  records.

### 9.3 Use `Graph` as a projection, not persistent identity

The server and client can project admitted refs into `effect/Graph` for cycle
diagnostics, topological upload order, explain plans, and fixtures. Graph node
indexes are process-local. Persistent edges remain typed `ContentId`
references, and every projected graph must be derived from revalidated nodes.

### 9.4 Package by subpath, even if installation stays singular

The package is currently private and depends only on `effect`. A published
reference server introduces platform and operational concerns that browser-only
clients should not import accidentally.

Recommended exports:

```text
@foldlab/effect-replay/cas
@foldlab/effect-replay/cas/blob
@foldlab/effect-replay/cas/remote
@foldlab/effect-replay/cas/server
@foldlab/effect-replay/cas/server/node
@foldlab/effect-replay/cas/conformance
@foldlab/effect-replay/cas/inspect
```

The server core and Fetch handler can remain platform-neutral; Node/Bun live
layers are optional peer/platform entry points. “One install” need not mean one
large eager dependency surface.

## 10. Developer and operator experience

### 10.1 One-file happy paths

Local domain value:

```ts
const User = Cas.value({
  kindTag: 0x21,
  revision: 0,
  schema: UserSchema
})

const id = yield* User.put(user)
const roundTrip = yield* User.get(id)
```

Blob to remote:

```ts
const blob = yield* CasBlob.Service
const ref = yield* blob.put(fileBytes)
const transfer = yield* CasTransfer
yield* transfer.push(ref)
```

Reference server:

```ts
CasServer.layer({
  store: CasObjectStore.layerFile("./cas-data"),
  roots: CasRootRegistry.layerFile("./cas-data/refs"),
  policy: CasServerPolicy.openLocal
})
```

These are target shapes, not current compilable interfaces.

### 10.2 Inspection must ship with the server

A content-addressed system without inspection tools is hostile to users. Ship:

```text
cas inspect <full-id-or-prefix>
cas cat <id>
cas refs [name]
cas history <name>
cas closure <id> --explain
cas verify <id|--all>
cas doctor
cas gc --dry-run
cas conformance <authority> --profile cas-http/0
```

Every error should carry the operation, full id when known, profile, authority
without credentials, expected/actual values where safe, and the conformance
clause id. Redacted credentials must remain structurally absent from reports.

### 10.3 Progress and receipts

High-level workflows should return reports, not require users to reconstruct
success from log events:

- put: logical bytes, chunks, new/reused nodes, root, recipe;
- push: transferred/already-present, retries, published root;
- read: requested range, emitted bytes, proof bytes, terminal status;
- conformance: profile, capability snapshot, passed/failed/skipped clauses,
  minimized fixture/reproduction command.

Use optional progress streams for UI. The final report is semantic output;
progress remains advisory.

## 11. Conformance UX and rigor

### 11.1 Do not collapse every result into one “conformant” bit

Report independent suites:

1. wire codec and status mapping;
2. node admission and load revalidation;
3. graph ordering/publication;
4. proof/range generation and parsing;
5. interruption/backpressure/budget behavior;
6. root compare-and-set;
7. restart/crash behavior for adapters that declare persistence;
8. security-policy and information-disclosure fixtures.

A peer may pass wire conformance while making no durability declaration.

### 11.2 Test through the same deep interfaces

- `CasObjectStore` gets a reusable adapter contract suite.
- `CasServerCore` tests use memory and fault-injection adapters.
- black-box HTTP tests target the reference server and foreign peers.
- generated vectors bind exact profile and model versions.
- every failure prints one command containing seed, fixture id, fragmentation,
  fault schedule, and expected/actual terminal.

### 11.3 Required negative and hostile fixtures

Add at least:

- missing parent record, hash-bearing skip when bare skip is required, unknown
  tag, truncated length, trailing bytes;
- one-byte-at-a-time and every-boundary fragmentation;
- wrong total, overflowed `from + count`, empty blob, final short chunk, range
  at/past end;
- valid early prefix followed by corrupt parent/chunk or truncation;
- proof amplification and oversized declared tree;
- duplicate id with different resident bytes;
- acknowledgment before durable adapter completion;
- root publish racing GC, stale `If-Match`, concurrent publishers;
- capability document exceeding actual adapter limits;
- cancellation after each receive/verify/store/publish transition;
- short-hash ambiguity and cross-tenant presence probing.

Mutants should correspond one-to-one with named obligations. Killing a mutant
shows sensitivity to that injected defect only.

### 11.4 Security boundary

The reference package owns safe hooks and defaults; the deployer owns identity
provider choice and authorization policy. The core still must enforce:

- authenticated principal passed explicitly to every semantic operation;
- per-principal/tenant root and presence namespaces;
- byte, node, key, proof, depth, concurrency, and time budgets;
- no cross-tenant global digest-existence oracle by default;
- authorization on root updates independently of object upload;
- root trust provenance exposed to the client;
- constant-time digest comparison where the crypto/provider makes it
  available;
- audit records with secrets structurally redacted.

Proofs of ownership and message-locked-encryption literature in the existing
streaming prior-art receipt are warnings that global dedup/presence can disclose
content. They do not provide a turnkey policy.

## 12. Prioritized changes to the target design

### Before ratifying MRK-2

1. Correct the proof-stream alphabet and add parent frames.
2. Define byte-range semantics separately from chunk-index semantics.
3. Adopt a uniform blob manifest and freeze recipe-id semantics.
4. Decide inline indexed leaves versus referenced content chunks; prefer the
   referenced-chunk design if dedup is a headline property.
5. Add incremental byte-parser fragmentation and EOF obligations.
6. Rewrite early-emission claims with the current collision witness and
   trusted-root hypotheses.

### Before building the reference server

7. Freeze `CasObjectStore` and `CasRootRegistry` contracts, including duplicate
   conflict, visibility, and declared durability.
8. Define effective capabilities as the policy/backend/implementation
   intersection.
9. Model server admission and root publication; do not reuse client published
   state as a server theorem.
10. Keep the first filesystem adapter append-only if GC concurrency is not yet
    modeled.
11. Put platform server providers behind subpath exports and explicit layers.

### Before calling the package pleasant to use

12. Ship `CasBlob`, `CasRepository`, `CasInspect`, and the CLI/report surfaces.
13. Return typed final reports and preserve late stream errors.
14. Add unique-prefix resolution with explicit ambiguity.
15. Provide adapter contract tests and one-command black-box conformance with
    reproducible failures.

## 13. Source ledger and provenance boundary

### Newly resolved source

Unison is fixed to commit
[`84b95a623711b57b9ff7163f124b214d626b81e4`](https://github.com/unisonweb/unison/tree/84b95a623711b57b9ff7163f124b214d626b81e4),
root tree `ebfc54745fac4588fff9e5175b90871a477b2d91`. Exact Git blobs,
independent SHA-256 digests, and byte lengths for every cited Unison file are
recorded in
`.reference/provenance/receipts/server-reference-and-verified-reads-prior-art-review.json`.

### Reused resolved sources

- Git `v2.55.0`, OCI Distribution `v1.1.1`, Bazel REAPI
  `becdd8f9...`, ByteStream `de3c0d...`, Nix `2.35.2`, and related wire
  sources: `remote-cas-wire-sweep-sources.json`.
- Boxo `63cae36...`, IPLD selectors `a7b937...`, GraphSync `12cbff...`,
  XET draft/source, Bao `3466bb...`, and the literature/standards crosswalk:
  `streaming-sync-cas-api-prior-art.json`.
- RFC 9110 and RFC 9530 immutable editions:
  `remote-transport-standards-and-lean-models.json` and the streaming receipt.
- Effect source commit `0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`:
  `.reference/provenance/sources.lock.json` and the matching package pin.

### Claim boundary

No cited source establishes Foldlab's codec exactness, blob identity,
partial-read judgment, server publication property, storage durability,
runtime/model refinement, or interoperability. Every interface and obligation
marked **F** or **O** remains project-owned and pending ratification. No build,
test, external server, or conformance suite was run for this review.
