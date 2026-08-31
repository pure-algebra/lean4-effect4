# Remote CAS prior art — a four-sweep compendium

Status: conception-mode research, 2026-08-27. G0/G1 findings only; no
ratified rule, model statement, or shipped API changes here. Gathered by
four parallel research agents (admitted-tool outputs with the estate's
standard empty trust contribution — the citations carry the weight),
reviewed and condensed first-hand by the coordinator. Companion design
synthesis: `remote-cas-conformance-design.md`.

Provenance standing: Part I was read at exact tags/commits (its pin
table below) and the downloaded spec bytes are preserved off-repo at
`C:\Users\kokok\AppData\Local\Temp\foldlab-remote-cas-wiresweep-2026-08-27`
for byte-receipt minting if any source is promoted to Source Lock; the
sources are deterministically re-fetchable at their pins regardless.
Parts II–IV were read from live primary pages on 2026-08-27 and carry
NO byte pins yet — the same explicitly-pending standing the
service-derivation survey assigns to its live links. Per estate
discipline, no gated claim may depend on any of this until pinned.
`[not confirmed]` and `[inference]` marks are preserved from review.

## Cross-sweep convergences (coordinator's review)

Five findings recur independently across all four sweeps and should be
treated as the load-bearing consensus of shipped CAS practice:

1. **The only integrity layer that has ever caught the documented
   failures is client-side recomputation at the trust boundary.** Every
   surviving system recomputes identity from received bytes (Git, Nix,
   OSTree, casync/desync, REAPI-compressed, IPFS-trustless); the weak
   ends (OCI's SHOULD, bitswap's silence, path gateways) are exactly
   where the duty blurs. Server digests, headers, fingerprints, and
   reconciliation answers are routing hints.
2. **Presence is advisory in both directions and never durable**, and
   negative caching is the documented foot-gun at multiple layers at
   once (client, server memory, CDN edge). Every robust design pairs a
   presence fast-path with a repair path.
3. **Closure is a client invariant enforced at a named publication
   point** (quarantine-then-refs, transaction-refs-last, root-last
   convention); no surveyed server contract enforces it, and one (OCI)
   explicitly MAY accept dangling parents.
4. **Absence and corruption never share an error clause** in any system
   that survived production (casync MISSING vs ABORT, Nix SubstituteGone
   vs hash-mismatch, REAPI NOT_FOUND vs INVALID_ARGUMENT, OCI
   *_UNKNOWN vs DIGEST_INVALID), and integrity failures are terminal
   for those bytes — never retried unchanged.
5. **Domain separation inside the pre-image is the defense against
   structural second-preimage/ambiguity attacks** (RFC 6962 leaf/node
   prefixes, Git type headers, Xet keyed roles, Bitcoin CVE-2012-2459
   as the failure case) — the estate's `versionByte ++ kindTag ++
   frame(...)` is already this defense.

---

# Part I — wire protocols in shipped CAS systems

All findings read at exact pins, downloaded 2026-08-27.

## Source pins

- Git tag `v2.55.0` (gitprotocol-pack/http/v2, gitformat-pack/loose,
  git-index-pack, git-receive-pack, transfer/fetch/receive config docs)
- OCI distribution-spec `v1.1.1` (2025-01-29); image-spec `v1.1.1`
  descriptor.md (2025-03-03)
- Docker Registry HTTP API V2 @ distribution/distribution
  `5cb406d511b7b9163bff9b6439072e4892e5ae3b` (the exact commit OCI
  v1.1.1's appendix cites)
- Bazel REAPI @ `becdd8f9ff811df88a22d3eadd6341753d51d167` (matches the
  estate's existing pin); ByteStream @ googleapis
  `de3c0d362adbaafc7a0cd1254a8cd49a528505ee`
- Nix tag `2.35.2` (binary-cache/narinfo/nix-cache-info/store-path
  docs + path-info.cc, substitution-goal.cc, local-store.cc)
- OSTree @ `1d5a312a3189b0fbd70fe6769aadb19a366fedb2` (repo.md,
  formats.md, repository-management.md, pull man/source)
- casync @ `b4b7e5606f785572b78a43626a27a45fe3df2fbd` (README, rst,
  caprotocol.h, castore.c, caremote.c); desync @
  `ff9ccfab7db1dc89395f56079f4de66626f2af1d` (README)

## Git

Presence/negotiation: ref advertisement; `want` lines then `have`
blocks of 32 in flight; ACK continue/common/ready vs NAK; gives up
after 256 unACKed haves, armed only after at least one
`ACK %s continue`. Negotiation is heuristic over commit ancestry, not a
per-object oracle. v1 forbids wants outside the advertisement; v2 fetch
relaxes ("wants can be anything") and adds opt-in `object-info` (size
only). Push: server advertises tips plus anonymous `.have` lines; the
receiver never enumerates objects.

Verification: identity is the hash of `<type> <size>\0<data>`; packed
objects reconstruct that prefix — IDs are always recomputed, never
trusted. Whole-pack trailer checksum; idx v2 per-object CRC32 (pack-to-
pack copies without undetected corruption). `transfer.fsckObjects`
defaults FALSE. Push side has a QUARANTINE: incoming objects land in a
temporary object directory and migrate only after pre-receive passes; a
failed push leaves no on-disk data; refs to quarantined objects are
rejected. Fetch has NO quarantine — the docs explicitly warn it "cannot
be relied upon to leave the object store clean" (workaround: mirror via
push in two steps). Connectivity (transitive closure) is checked on
receive by default. `index-pack --strict/--max-input-size`,
`receive.maxInputSize` bound inputs.

Ordering/closure: no per-object ordering — one pack; closure is
enforced at the publication point: refs move only after
unpack + index + connectivity + quarantine migration + per-ref old-id
compare-and-swap. "A packfile MUST be sent if either create or update
command is used, even if the server already has all the necessary
objects" (the mandatory empty pack).

Resume/range: smart HTTP is stateless — the client retains all state;
no partial-pack resume exists. `packfile-uris` offloads bulk packs to
plain HTTP(S), verified and connectivity-checked by the client
afterwards. The dumb protocol is static files with ordinary HTTP
caching.

Errors: `ERR` pkt-line may replace any expected pkt-line; sideband
channel 3 for fatals mid-stream; `report-status(-v2)` separates unpack
status from per-ref ok/ng reasons; absent repo MUST NOT 200.

Refusals: no auth in the protocol (transport's job); hidden refs are
explicitly not confidentiality ("keep private data in a separate
repository"); thin packs are wire-only and thickened on receipt.

## OCI distribution-spec v1.1.1

Presence: `HEAD /v2/<name>/blobs/<digest>` → 200 + digest/length
headers, else MUST 404. No batch presence endpoint.

Verification: pull-side is the client's, stated SHOULD ("Clients SHOULD
verify that the response body matches the requested digest"); the
image-spec descriptor adds: verify size before digest "to reduce hash
collision space", avoid heavy processing before hashing, embedded
`data` MUST match. Push-side the registry MUST verify the closing PUT's
digest (`DIGEST_INVALID`/`SIZE_INVALID`) and MUST store manifests in
the exact bytes provided.

Ordering/closure: blobs-first, manifest-last is "typically"; a registry
MAY reject a dangling manifest (`MANIFEST_BLOB_UNKNOWN`) — and so MAY
accept one; it MUST initially accept a dangling `subject`.

Resume/range: blob GET SHOULD support Range; chunked PATCH uploads are
strictly ordered (out-of-order → MUST 416; offset recoverable via GET →
`Range`); session closed by `PUT ?digest=<whole-blob>`.

Idempotency: digest-keyed; concurrent same-layer uploads both proceed,
one copy stored. Cross-repo mount → 201, with a mandated 202 fallback
to a plain upload; `from` MAY be optional (mount from anywhere
findable) — the presence-oracle edge.

Errors: a closed 14-code enum (BLOB_UNKNOWN, DIGEST_INVALID,
MANIFEST_BLOB_UNKNOWN, SIZE_INVALID, UNAUTHORIZED vs DENIED distinct,
TOOMANYREQUESTS, …) in a JSON envelope; 413 for oversize manifests.

Redirects/refusals: blob/upload `Location` may be off-registry (signed
cloud URLs); the 307/302 redirect contract lives in the cited Registry
V2 base spec. Deletes MAY be disabled; only Pull is mandatory;
referrers-tag race protection is explicitly the client's.

## Bazel REAPI CAS + ByteStream

Presence: `FindMissingBlobs` — a true batch have-not check; querying
SHOULD extend blob lifetimes (presence doubles as TTL touch). Empty
blobs are fictional (always available). Missing Action inputs surface
lazily as `FAILED_PRECONDITION` + per-blob MISSING violations.

Verification: `Digest = (hash, size)` and size is integral to identity
— right hash with wrong size MUST be rejected. Upload verification is
the server's (MUST, `INVALID_ARGUMENT` on mismatch); download
verification is the client's (MUST for compressed reads).

Ordering/closure: none enforced — Merkle directories upload in any
order; `GetTree` silently omits missing subtrees; lifetime is
implementation-specific, so parents can outlive children. Closure is a
client-workflow property (find-missing → upload → use).

Resume: `Write` resumes from `QueryWriteStatus().committed_size`, which
"may be less than the amount of data the client previously sent";
offsets MUST equal committed size. Compressed reads: offsets in the
uncompressed domain.

Idempotency: concurrent same-data uploads legal; duplicate completion
terminates early WITHOUT error at full committed size; after a
digest-mismatch the client "should not attempt to retry the upload."

Errors: per-item `google.rpc.Status` in both batch directions
("succeed or fail independently"); `RetryInfo` SHOULD be respected;
limits discovered via Capabilities (`max_batch_total_size_bytes`,
`max_cas_blob_size_bytes`). No retention guarantee. This commit already
carries capability-gated content-defined-chunking extensions
(SplitBlob/SpliceBlob, FastCDC).

## Nix binary cache (2.35.2)

Presence: static files over HTTP — `nix-cache-info` (StoreDir,
WantMassQuery, Priority), one `.narinfo` per object, NARs at the
narinfo URL. No batch endpoint; the client computes the closure and
queries per path.

Verification (source-confirmed, three layers): signatures checked twice
(before download and again at addToStore), binding path + narHash +
narSize + THE REFERENCE LIST in one fingerprint; the NAR stream is teed
through a hash sink ("hash mismatch importing path"); content addresses
are recomputed (self-references via sentinel), and CA paths are exempt
from signatures because the path itself is recomputed.

Closure: enforced on the READ side — references are recursively
substituted and re-verified before the parent installs. Publish-side
ordering `[not confirmed]`.

Errors (from source): `InvalidPath` → next substituter;
`SubstituteGone` (narinfo seen, NAR since GC'd) → behaves as
never-existed; hash/size/CA mismatch → hard errors; store-dir mismatch
→ refuse the cache entirely.

## OSTree

Presence: a deliberately dumb server — objects, refs as text files, one
summary file (every ref + all static deltas); delta existence testable
in one request because delta names derive from the two commit
checksums. Pull runs inside a repository transaction: fetch/verify in
any order, ref set LAST; an aborted pull leaves at worst unreferenced
objects. Every fetched metadata and content object's checksum is
recomputed (source-confirmed); GPG default ON per-remote; local
sources default to trust-and-hardlink with `--untrusted` to force
verification. Content identity covers the UNCOMPRESSED form — `.filez`
storage objects "do not match the hash they are named as" (the storage
envelope is outside identity). Retries default 5 per object. OSTree
REFUSES a smart server (static webservers/CDNs are the canonical
target); the summary is a single-writer derived index.

## casync / desync

Two planes: casync's framed remote protocol (HELLO capability flags;
pull = INDEX frames then per-chunk REQUEST → CHUNK|MISSING; push is
receiver-driven — the server requests exactly what it lacks) and dumb
HTTP chunk stores (GET by chunk id; desync adds HEAD existence and PUT;
seeds substitute for presence). Verification source-confirmed: every
incoming chunk's digest recomputed over the UNCOMPRESSED bytes
(`-EBADMSG` on mismatch); a poisoned cache FAILS LOUDLY (invalid cached
chunks are never skipped or auto-removed); encrypted stores' AEAD is
not bound to the chunk name — a swap is caught only by the consumer's
content validation. No store-level closure (pruned chunks fail at
extract). desync failover groups require identical stores — a miss is
an immediate failure, not try-elsewhere, by design. casync's own
store-wide `verify` was "(NOT IMPLEMENTED YET)" — left to consumers.
Encryption never hides chunk identity (plaintext-hash names remain a
documented presence oracle).

## Part I implications (15)

1. Recompute identity at the trust boundary before caching or
   returning — upgrade OCI's SHOULD to a client-side MUST.
2. Declared size is part of identity; check it FIRST — the byte-budget
   check before hashing is the DoS boundary.
3. Presence is advisory and never durable; no negative caching by
   default; re-check near use (`SubstituteGone` is the named pattern).
4. Real batch protocols return per-item status; a response that fails
   to account for every requested key is a protocol error.
5. Duplicate upload is success; integrity failure is never retried
   unchanged.
6. Resume only against a server-authoritative committed offset (which
   may regress) — never a locally remembered sent-byte count.
7. Closure is enforced at named publication points; never infer closure
   from server acceptance of a parent.
8. The mutable-name plane stays separate and compare-and-swap guarded.
9. The shipped error taxonomy: integrity (terminal) / absence (normal,
   per-key) / transport (retryable under policy) / auth (two flavors) /
   capacity / protocol-limit — absence and corruption never share a
   clause.
10. Honor server-declared limits and capabilities via a first-class
    probe; split or reroute rather than hardcode.
11. Expect redirects to offloaded storage; verification and credential
    scope are independent of transport origin.
12. Retry budgets are per-layer configuration with server-informed
    policy; shipped defaults span 0 to 5.
13. Storage envelope ≠ identity: decode, then verify the canonical
    form; never hash wire bytes.
14. Presence is an oracle; scope it per authorization boundary.
15. Quarantine-then-admit beats write-then-check (git's fetch side is
    the shipped cautionary tale); partial downloads are discarded,
    never installed.

Known gaps: Nix publish ordering and NAR resume; git push thin-pack
default; OSTree Range use; the 307 sentence lives in Registry V2, not
the OCI text itself.

---

# Part II — distributed addressing theory and integrity machinery

Live primary pages, 2026-08-27; no byte pins.

## IPFS (CID/multihash, bitswap, gateways)

Multihash = varint function code + length + digest (self-identifying);
CIDv1 puts the codec inside identity; strict decoding rejects over-long
varints and trailing bytes. Bitswap 1.2.0 separates presence
(want-have/DONT_HAVE) from payload (want-block); blocks are capped 2
MiB, messages 4 MiB (MUST) — the transfer unit equals the hashing unit.
The bitswap spec contains NO validation language; the 2026
trustless-gateway spec is where the duty lands: recompute every block
against the REQUESTED CID, treat incomplete CARs as failures, assume no
CAR ordering/dedup/determinism unless declared. Path gateways
structurally cannot be client-verified (deserialized responses) — a
trust-the-gateway mode. CARv1 explicitly does not guarantee coherent
DAGs, complete roots, ordering, dedup, or deterministic encoding. A CID
is not a file hash: identical bytes yield different CIDs under
different chunkers/layouts/codecs. GraphSync (remote selector
execution) has an incomplete 2018 spec, unspecified requester-side
verification, and its largest deployment (Filecoin) is retiring it for
trustless HTTP `[partly secondary-sourced]`.

## BLAKE3 / bao / iroh (verified streaming)

BLAKE3 is internally a Merkle tree over 1024-byte chunks with distinct
root finalization — verified streaming is native. Bao's decoder
verifies every chaining value top-down, releasing no byte before its
chunk authenticates against the root; the length header is an
unverified hint gated on final-chunk validation and must not leak by
any route. Slices are self-contained verified extracts. Iroh ships this
over QUIC with 16 KiB chunk-group granularity (grouping does not change
the root), both-sides validation, and resume-by-missing-ranges from any
provider. The strongest partial-content story surveyed: ranges
verifiable without turning layout into a DAG. Bao encodings are
byte-malleable in the inert sense (trailing garbage ignored).

## Set reconciliation (RBSR / negentropy)

Range-based set reconciliation (arXiv:2212.13567): both sides order
their sets canonically, exchange per-range fingerprints, split
mismatching ranges recursively; rounds scale with log set size
independent of the diff (~3 round trips at 10^6 elements), transferred
bytes with the difference; servers can be stateless; no shared tree
structure required. Fingerprints are forgeable by construction (plain
XOR falls to Gaussian elimination; the additive scheme is a hardened
compromise) — reconciliation output is a FETCH PLAN, never evidence;
every fetched item is verified against its own ID afterwards.

## Chunking and identity (FastCDC, Xet, restic, borg)

The load-bearing split: Xet and IPFS commit chunk layout INTO identity
(change the chunker, change every file hash); restic and borg keep
chunking strictly BELOW identity (no whole-file content address exists
that a different chunker would break — a transfer/storage detail);
BLAKE3 fixes chunking inside the hash function (invisible to identity,
free for transport). Restic and borg keep chunking parameters SECRET
(per-repo polynomial/seed) as an anti-fingerprinting measure — the
opposite regime from putting them in identity. Xet's distinct keyed
hash roles per plane (chunk/xorb/file/term) are the domain-separation
pattern; its out-of-band algorithm suite is the named agility warning.

## Venti / Perkeep

Venti: write-once by construction, append-only sealed arenas,
whole-block SHA-1 scores, probabilistic (non-adversarial) collision
stance — and no agility path when SHA-1 fell. Dedup requires identical
block size and alignment (chunking-determines-dedup, 2002 edition).
Perkeep: immutable blobs; blobrefs name the hash function per
reference; mutability lives entirely above the CAS in signed permanodes
and claims.

## The address-integrity boundary

A server-supplied digest is a routing hint; only recomputed digests
have authority. Structural ambiguity produces equal roots under a
perfect hash (Bitcoin CVE-2012-2459: duplicate-tail Merkle rule, plus
the cached-invalidity denial-of-service that followed) — the defense is
unambiguous construction and domain separation (RFC 6962 0x00/0x01
prefixes, "required to give second preimage resistance"), which the
estate's kind-in-pre-image already implements. Hash agility strategies
shipped: in-identifier (multihash — many names per content, verifier
surface grows forever), whole-repository migration with bidirectional
mapping (Git SHA-1→SHA-256: one format per repo, translation tables,
dual signatures, staged interop), function-name-in-reference (Perkeep),
and no-agility (Venti, stranded). No surveyed system states its
collision assumption as a named dischargeable premise — the estate's
lattice is stricter than all of them.

## Part II implications (15, condensed)

Whole-node addressing stands; future chunking enters as declared
identity or not at all. Size caps are protocol constants, part of
verifiability. BLAKE3/bao is the fork decision if a large-payload kind
ever arrives. Server digests are routing hints; batch entries fail
closed on misalignment. The verification duty belongs in the CLIENT
contract, not the transport spec. Adopt the have/want split for upload
negotiation. Reject remote selector execution; client-driven traversal
with CAR-batching only as a cache-warming hint. RBSR is the future
anti-entropy shape — transport-only, fetch plans never evidence.
Root-last is universally corroborated; no container format substitutes
for closure checking. Keep kind-in-pre-image under any future
aggregation; never cache negative verdicts by address unless the
derivation is deterministic and re-checkable. Hash agility = the Git
model (one function per admitted store, migration by explicit mapping
outside content identity); no per-node self-describing hashes.
Presence endpoints per-namespace; cross-tenant dedup is a policy
decision with a named privacy cost. Wire lengths/counts are hints
bounded by declared budgets. Resumability follows the verification
unit (here: the node). Mutable names stay out of the CAS and out of
reconciliation; heads move by compare-and-set only.

Unconfirmed: FastCDC numerics (abstract-sourced), Perkeep current
default hash, iroh outboard overhead at 16 KiB, parts of the Filecoin
GraphSync retirement.

---

# Part III — production failure and consistency semantics

Live primary sources (specs, source, issue trackers, postmortems),
2026-08-27; no byte pins.

## GC vs liveness

Documented failures: Git's advertise-then-prune race (mitigated by
mtime grace, explicitly imperfect, then cruft packs); OCI reference
registry GC corrupting concurrent pushes (distribution#3045) and
mass-deleting under multi-arch manifests (#4461); the registry's
in-memory descriptor cache surviving GC so re-pushes of a "present"
digest are silently skipped while content stays missing (#3802, #4569,
#1803) — the cleanest presence-oracle-desync on record; OSTree prune
racing in-flight commits (2015 design thread); Nix collecting paths a
running shell depends on (nix#2208, closed not-planned); OCI referrers
dangling by design (client-maintained eventually-consistent tag index).

Shipped mechanisms: Nix registered roots + per-process temp-root files
+ a GC lock with a socket handshake ("the collector may delete the path
before the lock is obtained, never after"); IPFS pin/GC locks (adds
block during GC); Harbor's 2-hour online-GC grace window; OSTree
exclusive-lock prune; Git server-side quarantine; REAPI's client-driven
repair loop (SHOULD-extend lifetimes on query; MISSING violations name
what to re-upload).

Unpromised: retention itself, anywhere (IPFS "discoverability is not
availability"; REAPI eviction at any time; Docker Hub's unilateral 2020
retention episode).

## Concurrency, atomicity, durability

Git writes loose objects via temp-file + rename; since v2.47.0 an
`EEXIST` triggers a byte-compare (`check_collision`) except where the
hash was just computed from the bytes in hand — dedup-by-name is only
sound under exactly that condition. Git does NOT fsync loose objects by
default ("committed,-loose-object"), and the crash-truncation class
(empty loose objects) is the documented result. REAPI resolves
same-digest upload races as success; containerd ingest is invisible
until Commit (ErrAlreadyExists = dedup race); OCI chunk sessions
re-sync via 416 + authoritative Range.

## Caching

Negative caching is the multi-layer foot-gun: Nix's 1-hour client
negative TTL stacks under cache.nixos.org's 1-hour CDN-edge negative
TTL with purge coordination required to be safe (and cachix documents
the resulting staleness). CDN streaming-miss delivery produces
truncated/corrupt bodies that ONLY client NAR-hash verification turns
into hard errors instead of poisoned stores. `Docker-Content-Digest` is
optional and containerd cannot rely on it — verification is client-side
at ingest commit.

## Multi-tenant and auth

OCI token scopes are per-repository; cross-repo mount deliberately
relaxed proof-of-possession (v2.3.0 notes), and v1.1.1's from-optional
mounting makes an unscoped registry a digest-existence oracle
`[inference; current exploitability unconfirmed]`. Nix separates
content trust (path signatures binding the reference list) from
transport auth entirely. Xet documents the same dedup-oracle channel
with keyed-hash mitigations (already pinned in-repo).

## Partial failure

REAPI: per-item status is the norm; "batch OK" is meaningless; digest
mismatch is non-retryable with unchanged bytes; FindMissingBlobs is
advisory (races eviction). ByteStream committed offsets can regress.
OCI gives a taxonomy, not closure — a registry MAY accept a manifest
referencing absent blobs, so root-last is a client invariant. Retry is
unsafe: after integrity rejection; rewriting finalized resources; blind
re-PATCH without re-reading the session Range.

## Incidents

Amazon S3, 2008-07-20: single-bit-corrupted internal gossip spread
because SYSTEM STATE carried no checksums while customer payloads did —
verification must cover control state, not just payloads. SHAttered →
Git 2.13 shipped collision-DETECTING SHA-1 by default. The distribution
GC incident set (above). The cache.nixos.org corruption class (caught
only by client verification). Git crash-truncation (no-fsync default).
No documented incident was found of a major registry serving
wrong-digest bytes that verifying clients ACCEPTED — the recurring
pattern is truncation caught by clients and deletion caught by nothing
`[inference from absence — unconfirmed]`.

## Part III implications (15, condensed)

Verification-on-receipt is the layer that catches real failures. Never
negative-cache by default; expect an invisible server-side negative
layer too. Presence is racy in both directions; skip work on it only
when a later step re-establishes truth and a repair path exists.
Uploads are idempotent only as exact-digest server-verified operations;
integrity rejection is terminal. Resume by re-querying committed state;
offsets regress. Root-last is a client invariant; never rely on
server-side rejection as the backstop. The liveness contract is
explicit pin/root semantics plus a re-upload repair path — surfaced as
named adapter properties, including "backend has no GC fence" when
true. Local writes: temp-file + rename + digest at commit; the
durability (fsync) stance is named policy; tolerate truncated files on
load. Dedup-by-name without byte comparison only when the digest was
just computed from the bytes in hand; never skip admission on
presence. Verify control state (presence indexes, head maps, batch
framing) with the same fail-closed posture as payloads. The error
taxonomy production clients branch on matches the estate's seven-family
table and supports a dedicated requested-root-absent clause
(ContentNotFound). Presence/dedup fast paths are cross-tenant side
channels unless namespace-scoped; no global existence call. Nothing
external promises retention; "durable" is conditional on a named
backend contract. Client-maintained secondary indexes are
eventual-consistency liabilities — derived indexes belong in the
mutable-heads service under compare-and-set.

---

# Part IV — conformance-testing prior art for effectful systems

Live primary sources, 2026-08-27; no byte pins.

## The harness landscape

**OCI conformance suite**: everything real (Go tests against a live
registry), env-toggled workflow categories that are ordered and
stateful, hand-written HTTP assertions, run-time-generated content, no
fault injection, accommodation env vars as the fossil record of
registry divergence, HTML reports embedding redacted transcripts (a
live-lane audit artifact worth copying). **REAPI**: no official
conformance suite — the independent remote-apis-testing matrix pairs
real clients with real servers and asserts only "the build passed";
the per-blob semantics that matter for a CAS are specified but
conformance-tested by nobody — the assertion-density warning. **Git's
own protocol tests**: two tiers — a pure-protocol tier piping pkt-line
bytes through `test-tool serve-v2` and byte-comparing expect files
(conformance vectors for a wire protocol, including malformed rows),
and a real-Apache tier whose `t/lib-httpd/` is a catalog of scripted
CGI faults (mid-frame truncation, 429s, and `apply-one-time-script.sh`
— a fault that fires exactly once at a chosen conversation point, then
restores honest behavior). **Jepsen/Elle**: real faults against real
systems, model-checking the observed history afterwards; workloads
co-designed for traceability; sound but incomplete, unreproducible.
**ShardStore (S3, SOSP 2021)**: executable Rust reference models
step-compared with the implementation under property-based sequences;
models double as unit-test mocks and therefore stay maintained;
dependency-tracked crash-consistency properties; Loom/Shuttle for
concurrency. **FoundationDB**: whole cluster in one deterministic
simulated process, seed ⇒ bit-identical re-execution, BUGGIFY fault
points. **SibylFS**: a formal spec used as an ACCEPTANCE ORACLE —
observed traces checked for membership in the allowed-behavior set
(expectation-as-set for deliberately loose specs).
**quickcheck-state-machine / Hypothesis stateful**: generated,
shrinking operation sequences checked against a reference model; qsm
adds linearizability search over parallel suffixes. **etcd
robustness**: real cluster + gofail failpoints concurrent with
traffic, validated post hoc against a simplified model; every found
bug becomes a permanent named reproduction target (`test-robustness-
issueNNNN`) that must stay detectable — the regression discipline.
**Toxiproxy**: a closed parameterized transport-fault taxonomy
(latency, bandwidth, timeout, slicer, reset_peer, limit_data),
TCP-only, reproducible in kind not schedule. **VCR**: record/replay
cassettes whose own `re_record_interval` feature is the admission of
the staleness problem — a discovery tool, unsound as conformance
fixtures.

## Direct vector prior art

RFC 8448 publishes complete TLS 1.3 handshake transcripts with all
secrets pinned — golden transcripts for a protocol happy path. Smithy
carries protocol test cases IN THE MODEL, consumed by every language's
codegen, with determinism designed in (epoch timestamps, pinned
idempotency tokens) — but cases are hand-authored, not computed by
executing a semantics. BoringSSL's runner/shim is a deterministic
HOSTILE fake-remote (a Go TLS stack with configurable bugs) driving
the library under test through a tiny shim — fault schedules live as
code, not data. h2spec sends spec-mapped valid and invalid frame
sequences at live servers. gRPC interop's prose-specified cases are
re-implemented per language; its "Postponed Tests" list (reconnection,
backoff, buggy-server resilience) is precisely the effectful edge
nobody's vectors cover. IPLD codec-fixtures is the CAS-native shape:
the same block in three codecs named by CID, decoded and re-encoded
across every codec with CID equality as the assertion, plus a
negative-fixtures tree — the ecosystem-scale version of the estate's
CAS-001/002 lane. The sans-io pattern (h11, hyper-h2, wsproto) is the
architectural precondition that makes wire vectors sufficient: a
protocol core as a pure state machine whose conformance surface IS
data.

## Part IV implications (18, condensed — the design seeds)

Make the adapter core sans-io; then the existing workflow applies
unchanged because the effectful seam has been made data. Put the
deterministic fake-remote's fault SCHEDULE in the manifest row as
fixture data ({ops, schedule} → {wireCommands, decisions, outcome}) —
BoringSSL proves scripted misbehaving peers, git proves one-shot
mid-conversation faults, Smithy proves model-carried vectors; moving
the schedule into the vector is the estate-specific synthesis. Model
the CLIENT DECISION MACHINE over an abstract exchange alphabet, never
HTTP. Reference canonical bytes from the ratified codec lane rather
than re-authoring them in wire vectors. Determinize time the way
replay already did; retry/backoff becomes a decision trace with
row-carried seeds. Most remote obligations fit existing schema
families (FAIL-CLOSED, TRACE-EXCLUDES, EXACT-STEP,
DISTINCTNESS-adjacent); the refinement and cache-observation judgments
are genuinely new shapes — plan a WGR-2 catalog event. The canonical
fault vector is wrong-bytes-for-address; the mutant catalog writes
itself (cache-before-admission, retry-non-idempotent-upload,
accept-truncated-batch, accept-permuted-batch,
negative-cache-not-found, renormalize-remote-response). Mutation
directions generalize unchanged. Property/state-machine testing is the
complement (the in-memory store is already the reference model AND the
mock — ShardStore's maintenance lesson), flipped via declared-evidence
lists at G4. Interrupted-upload consistency is the crash-consistency
analog: schedules carry declared interruption points; after position k
the possibly-published set is exactly what upload order permits.
Acceptance-set expectations (anyOf) only where the model legitimately
allows several behaviors — a manifest-shape ratification event, used
sparingly. Live-server conformance is a fourth lane, OCI-shaped,
evidence never contract. Keep live-lane assertions semantic (the REAPI
warning). Recorded transcripts are inputs to fixture transcription,
never fixtures (the VCR prohibition, already latent in
generated-vectors law). Transport-fault vocabularies collapse into the
abstract alphabet's semantic residue (truncation, reset, silence).
Auth stays out of vectors except as a declared policy trace. Adopt
etcd's regression discipline: every defect becomes a permanent named
schedule vector. Sequence: single-op baseline → batching/upload-order
→ property lane → live lane. NOVEL-GROUND FLAG: no surveyed project
generates wire-level expectations by executing a mechanized model —
Lean-computed schedule-conditioned decision traces would be new; the
remote Pass A must grill the manifest shape before any statement is
minted.

---

## Full source lists

Part I pins are tabled above. Parts II–IV cite, among others: IPFS
specs (cid, bitswap, path/subdomain/trustless gateways, CARv1),
multiformats/multihash, BLAKE3 repo, bao spec, iroh-blobs docs,
arXiv:2212.13567, negentropy repo + logperiodic.com/rbsr.html, USENIX
ATC'16 FastCDC (abstract-sourced), draft-denis-xet-05 (byte-pinned
in-repo), restic and borg internals docs, Venti FAST'02 (9p.io),
perkeep.org/doc, git hash-function-transition doc, RFC 6962,
CVE-2012-2459 (bitcoin.it), github.blog GC article, git-receive-pack /
git-fsck / core config docs, git object-file.c v2.47.0 + v2.13.0
RelNotes, distribution GC docs + issues #3045/#4461/#3802/#4569/#1803
+ v2.3.0 release + token auth spec, opencontainers distribution-spec
v1.1.1, remote-apis @becdd8f9ff + bytestream.proto, NixOS/nix manual
2.28–2.35 + gc.cc + issues #2208/#9664, boxo blockstore, kubo#8768,
OSTree list thread + repo-config + #2344, Harbor GC 2.3.0,
containerd#3238/#6691 + content.go, Maintainers:Fastly wiki, cachix
FAQ, docker/roadmap#152, S3 2008 postmortem mirrors, OCI conformance
v1.1.1, remote-apis-testing (GitLab), Bazel REAPI testing blog
2019-09-02, git t/lib-httpd + t5701 + t5616, jepsen + elle repos,
ShardStore SOSP'21 (DOI 10.1145/3477132.3483540), FoundationDB testing
docs, SibylFS (SOSP'15), quickcheck-state-machine, Hypothesis stateful
docs, etcd robustness README, Shopify/toxiproxy, vcr/vcr, RFC 8448,
Smithy protocol compliance tests, BoringSSL ssl/test, h2spec, gRPC
interop descriptions, quic-interop-runner, ipld/codec-fixtures,
sans-io.readthedocs.io.
