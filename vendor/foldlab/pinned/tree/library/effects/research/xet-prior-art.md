# XET as prior art for the Effect Replay CAS

Status: project research input, 2026-08-26

Claim posture: **bounded design comparison only**. This note does not amend the
ratified Effect Replay contract, select a representation, admit a theorem, or
claim correspondence with an implementation. XET remains a work-in-progress
individual Internet-Draft, not semantic authority for Foldlab.

## Source identity and disposition

The supplied editor's-copy URL is mutable and labels itself
`draft-denis-xet-latest`. The exact edition selected for this comparison is
**Frank Denis, _XET: Content-Addressable Storage Protocol for Efficient Data
Transfer_, `draft-denis-xet-05`, 29 June 2026**. At the snapshot date it is an
active individual Internet-Draft, intended as Informational, with no RFC stream
and no formal standing in the IETF standards process; it expires 31 December
2026. ([Datatracker edition page](https://datatracker.ietf.org/doc/html/draft-denis-xet-05),
[revision history](https://datatracker.ietf.org/doc/draft-denis-xet/history/))

Exact edition pin:

| Field | Value |
| --- | --- |
| Archived bytes | [`draft-denis-xet-05.txt`](https://www.ietf.org/archive/id/draft-denis-xet-05.txt) |
| Byte length | `101863` |
| SHA-256 content digest | `474d64988f0e28a561403807379e19cfe2c046a43ce39f210c9fdaf55b098a03` |
| Source repository | [`jedisct1/draft-denis-xet`](https://github.com/jedisct1/draft-denis-xet) |
| Source commit | [`b29b7d1564b382245aabb65ede5fc9cfc8e93d4c`](https://github.com/jedisct1/draft-denis-xet/commit/b29b7d1564b382245aabb65ede5fc9cfc8e93d4c) |
| Root tree | `cff859aa964cf50ecda49bb01ca4fcbf0ac94bfd` |
| Source file | `draft-denis-xet.md`; Git blob `c8fed40144e3a77eb90bf85558ebb9ffefc3d791`; SHA-256 `d1112adbdb7f4a451b8c19f06c280703ff4ca7dfbd89d3b316da4b191b781d7c`; `77555` bytes |

The [numbered HTML edition](https://www.ietf.org/archive/id/draft-denis-xet-05.html)
is retained as a human-facing link but excluded from byte pinning: fresh
downloads had equal length but different digests because an injected script
changed between responses. Two fresh downloads of the archived text above
matched the stated digest and length. The mutable
[editor's copy](https://jedisct1.github.io/draft-denis-xet/draft-denis-xet.html)
is a discovery link only.

Recommended estate disposition: admit the exact text edition and source commit
as **prior art for CAS storage, transfer, and format design**. It is neither a
normative authority nor subject-source evidence for Effect behavior. The draft
and source repository may be studied for ideas; copying its reference
implementation would require a separate code-component and licensing review.

## What XET directly specifies

XET is a client/server protocol for large-file storage and transfer. A client
splits files into variable-sized chunks, deduplicates chunks, aggregates new
chunks into compressed containers called **xorbs**, uploads those containers,
and then uploads **shards** describing file reconstructions and xorb contents.
A file reconstruction is an ordered list of **terms**, each naming a contiguous
chunk range inside a xorb. ([Sections 2–3](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-2),
[section 8](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-8),
[section 9](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-9))

The only defined algorithm suite combines BLAKE3, Gearhash, and LZ4. The suite
fixes the hash function, content-defined chunker, compression formats, domain-
separation keys, and parameters. It targets 64 KiB chunks, forbids boundaries
below 8 KiB, and forces them at 128 KiB. The suite is selected out of band and
is not identified inside xorb or shard binary formats.
([Sections 4–5](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-4))

XET assigns different commitments to different logical objects:

- a chunk hash commits to raw chunk data;
- a xorb hash commits to the ordered sequence of chunk hashes and sizes through
  a deterministic variable-fan-out aggregated hash tree, not to byte-for-byte
  xorb serialization;
- a file hash commits to the complete ordered chunk composition, with an
  additional keyed step for non-empty files; and
- a term verification hash commits to the raw concatenation of chunk hashes in
  one term's range.

Different keys separate these hash roles. Compression choices and ignored xorb
footer fields such as a uniqueness nonce do not affect the xorb hash.
([Section 6](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-6))

The binary formats carry explicit byte order, sizes, magic values, versions,
offsets, chunk hashes, and boundary tables. Unknown chunk versions and invalid
or truncated size fields are rejected. Shards also carry lookup tables whose
keys truncate full hashes to 64 bits for search, while the full 32-byte values
remain the identities in the primary records. Operational shard metadata
includes creation time, key expiry, and storage statistics.
([Section 7](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-7),
[section 9](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-9))

Upload is ordered bottom-up: referenced xorbs must be uploaded before the shard
that names them. Download obtains ordered reconstruction terms, fetches only
the required xorb ranges, decompresses the selected chunks, concatenates them
in order, and checks expected lengths. The recommended HTTP API returns an
error for a hash-mismatched or invalid xorb and for a shard whose referenced
xorb is absent. ([Sections 11–12](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-11),
[Appendix A](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#appendix-A))

Deduplication is layered across the current upload session, cached shard
metadata, and a global service. The draft deliberately trades maximum
deduplication against read fragmentation, and protects global discovery with
rotating keyed hashes. It also documents the residual content-existence and
cross-access-boundary privacy issues.
([Section 10](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-10),
[section 14](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-14))

Finally, the draft publishes fixed test vectors for chunk hashing, hash-string
conversion, internal-node hashing, and term verification, plus a link to
reference files. These are interoperability fixtures, not proofs.
([Appendix C](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#appendix-C))

## Comparison with Foldlab

The XET column below reports the selected draft. The evaluation column is a
Foldlab inference against the ratified
[Effect Replay context](../../../docs/effect-replay/CONTEXT.md), the
[implementation plan](../IMPLEMENTATION-PLAN.md), the pre-grade
[machine algebra](../../machine/MACHINE-ALGEBRA.md), and the ratified
[conformance workflow](../CONFORMANCE-WORKFLOW.md).

| Axis | XET, directly sourced | Foldlab evaluation and boundary |
| --- | --- | --- |
| Object and data model | Files become chunks; chunks are packed into xorbs; ordered terms reconstruct files; shards index both reconstructions and xorb contents. ([§§2–3, 8–9](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-8)) | Useful precedent for separating logical content, a storage envelope, reconstruction metadata, and indexes. It is not the Effect Replay carrier: Foldlab nodes have versioned kinds, canonical payloads, and ordered typed references, while histories represent logical operation occurrences. |
| Chunking and deduplication | Deterministic Gearhash content-defined chunking uses 8–128 KiB chunks; local, cached, and global deduplication operate on chunk hashes; implementations are advised not to fragment reconstructions excessively. ([§5](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-5), [§10](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-10)) | Strong prior art for a future bulk-blob kind, checkpoint payload, or remote store. It should not enter the M2 CAS node codec: current operation and history nodes are structured, bounded data, and occurrence distinctness must never be replaced by content deduplication. |
| Canonical encoding, identity, framing, and versioning | Chunk and shard encodings are exact and versioned, but a xorb hash commits to ordered decompressed chunk content rather than serialized bytes; compression and an ignored nonce may vary. The algorithm suite is selected out of band and is absent from binary formats. ([§4.3](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-4.3), [§6.2](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-6.2), [§7](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-7)) | The identity/storage-layout split supports Foldlab's existing rule that storage layout never participates in node identity. XET does not support Foldlab's stronger `versionByte ++ kindTag ++ frame(encode(canon node))` pre-image or one canonical representation per admitted node. Its out-of-band suite is a warning: a portable Foldlab scheme must not silently change digest or codec configuration under one scheme identity. |
| Merkle and DAG structure | Xorb and file hashes use a deterministic, hash-shaped variable-fan-out aggregation of ordered `(hash, size)` leaves. Terms separately name xorb chunk ranges. ([§6.2](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-6.2), [§8](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-8)) | The aggregation tree is a commitment algorithm, not a stored kind-typed dependency DAG with closure and acyclicity judgments. Foldlab should keep its stored reference graph distinct from any future chunk-aggregation tree. Range references, if needed later, should be a declared view or node kind rather than an implicit reinterpretation of CAS references. |
| Metadata and storage layout | Xorb footers permit tail-located metadata and range access. Shards combine primary full hashes with offset/count tables, truncated-hash lookup accelerators, timestamps, expiring discovery keys, and storage statistics. ([§7.5](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-7.5), [§9.6](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-9.6)) | Valuable evidence for separate planes: full address versus derived lookup key, immutable content versus expiring operational metadata, and identity versus physical offsets. Foldlab's full digest must remain authoritative; any truncated or host-shaped index remains a collision-checked accelerator outside identity. |
| Ingestion and reconstruction | Clients upload xorbs before a referencing shard; reconstruction processes ordered terms and validates ranges and lengths. ([§8](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-8), [§11](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-11)) | Supports bottom-up graph ingestion and a root-last publication pattern. It does not supply a transactional commit or orphan-collection law: a failure between xorb and shard upload can leave unreferenced content. Foldlab should state orphan and root-publication behavior separately when it adds persistence. |
| Integrity and admission | Parsers reject unknown versions, oversized declarations, and truncated payloads; the recommended API rejects invalid/hash-mismatched xorbs and shards with missing referenced xorbs. Download hash verification is generally a `SHOULD`, not one uniform admission judgment. ([§7.3](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-7.3), [§12.7](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-12.7), [Appendix A](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#appendix-A)) | Useful negative-fixture inventory, but weaker than Foldlab's fail-closed node admission and load-time address recomputation. XET does not provide wrong-kind reference checks, a single clause-named decision surface, or a proof that the readable store is well formed by construction. |
| Hash assumptions and security | Suites must provide at least 128 bits of collision and preimage resistance and keyed hashing for domain separation. Identity hashes are 32 bytes; only lookup tables truncate. The caching section speaks pragmatically of no collision risk and immutable content at a hash. ([§4.2](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-4.2), [§13.1](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-13.1)) | This is implementation and threat-model prior art, not a mathematical identity premise. Foldlab's Level-0/Level-1/empty-Level-2 lattice is stricter: reflection from address equality requires named `hInj`, while concrete collision behavior is characterized rather than hidden behind collision-resistance prose. XET must not be cited to promote a Foldlab address theorem. |
| History, replay, and occurrence semantics | The protocol reconstructs file bytes from ordered chunk ranges. It defines no execution history, request/outcome channel, cursor, occurrence identity, mismatch taxonomy, live fallback, or session witness. ([Abstract and §3](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#section-3)) | No support for `RPL-*`, `SES-*`, `CMP-*`, no-live-fallback, behavioral compatibility, or history-under-approximation claims. At most, its separation of reusable chunk content from ordered reconstruction position is an analogy for Foldlab's already-ratified separation between deduplicated request content and distinct occurrences. |
| Verification, trust, and claims | The draft uses BCP 14 conformance language, detailed pseudocode, fixed formats, test vectors, and reference implementations. It is an active individual I-D with no formal IETF standing. ([edition status](https://datatracker.ietf.org/doc/html/draft-denis-xet-05), [Appendix C](https://datatracker.ietf.org/doc/html/draft-denis-xet-05#appendix-C)) | Useful fixture and interoperability practice only. XET supplies no Lean theorem, proof trust report, source-to-model relation, Effect observation, TypeScript agreement, or Foldlab gate stamp. Its vectors would be sampled external-conformance evidence, not proof, if Foldlab later implemented XET; any gate would depend on a separately declared relation. |

## Supports

As bounded prior art, XET supports studying these design patterns:

- semantic content identity separated from compression, nonce fields, offsets,
  and other storage-layout choices;
- exact binary framing with independent version checks and defensive bounds;
- full-length identities separated from truncated, collision-checked lookup
  accelerators;
- bottom-up upload followed by publication of reconstruction metadata;
- ordered range reconstruction and partial retrieval for large payloads;
- derived indexes and expiring discovery metadata kept outside immutable
  content identity;
- layered deduplication with explicit fragmentation and privacy trade-offs; and
- byte-level cross-implementation vectors for every non-obvious encoding or
  hash conversion.

## Does not support

XET does not support any claim that:

- Foldlab's CAS node codec is canonical, injective, or decoder-complete;
- a Foldlab content identifier reflects content equality without `hInj`;
- a Foldlab store has typed-reference closure, acyclicity, or one-kind-per-
  address;
- an Effect Replay history is complete, request-compatible, outcome-admissible,
  deterministic, exact-consuming, or free of live fallback;
- equal request content identifies an operation occurrence;
- ordinary TypeScript orchestration is covered by the Lean model;
- the TypeScript implementation agrees with the Foldlab model; or
- any Foldlab code is proved, conforming, interoperable with XET, or suitable
  for remote persistence.

## Concrete lessons for Foldlab

### M2 decisions and fixtures

1. **Keep the semantic node and any storage envelope separate.** XET's xorb
   root remains stable across permitted compression and nonce variation. If
   Foldlab later compresses or packs nodes, the envelope should decode to an
   admitted canonical node whose project-owned pre-image still determines the
   content identifier. The envelope itself should not quietly become a second
   identity surface.

2. **Bind the production suite explicitly.** XET requires every participant to
   agree out of band on one suite. Foldlab's current version and kind framing is
   safer for project-owned identities, but Pass B should still make it
   impossible to switch the concrete digest or canonical codec under an
   unchanged portable scheme identity. Any cross-store identifier redesign is
   a contract proposal and must return to grilling.

3. **Expand the decoder's falsification matrix.** In addition to the ratified
   unknown-kind, non-canonical, address-mismatch, dangling-reference, and
   wrong-kind cases, the byte codec should exercise unknown scheme versions,
   truncated length frames, lengths beyond declared limits, count/offset
   disagreement, trailing bytes, and full-address mismatch. XET sections 7 and
   9 are useful parser-case inventories, not Foldlab requirements by
   themselves.

4. **Never promote an index key into an address.** XET's 64-bit truncated
   lookup values are search aids backed by full hashes. Foldlab should preserve
   the same separation if a filesystem or remote adapter later introduces
   prefix indexes, sharding, or bloom filters: candidate lookup is followed by
   full-address and content verification.

5. **Make graph publication root-last.** The current admission rule already
   checks reference closure at `put`. A future bulk import or filesystem
   adapter should write children before parents and publish a retained root
   only after its closure is present. Crash-created orphans, atomic root
   updates, and collection remain separate later obligations; XET does not
   close them.

6. **Use XET's vector shape, not its answers.** `CAS-001` vectors should cover
   each encoder arm, domain-separation byte, boundary length, and rejection
   clause, with canonical outputs generated by the Lean model under the
   ratified workflow. XET's literal vectors belong in Foldlab only if a future
   XET interoperability adapter becomes a declared consumer.

### Deferred extensions

7. **Do not add content-defined chunking to the initial CAS.** It earns its
   complexity only for large opaque payloads where insertion-stable
   deduplication and range retrieval are measured requirements. A future blob
   kind, checkpoint, or archive extension should re-enter Pass A with chunk
   parameters, maximum sizes, range observations, fragmentation policy, and
   migration behavior frozen together.

8. **Model range reconstruction as data.** If large histories or attachments
   need partial retrieval, an ordered range descriptor can be a first-class
   kind referencing immutable blobs. It must not redefine logical history
   occurrence or permit content-keyed substitution of repeated calls.

9. **Keep remote discovery privacy in scope.** Global deduplication can expose
   content-existence information even when keyed matching limits enumeration.
   A future remote CAS needs an explicit authorization unit, discovery
   namespace, key-rotation policy, and rule for whether deduplication may cross
   access boundaries. None is needed for the first in-memory adapter.

10. **Retain the current hash-hypothesis lattice.** XET's security requirements
    are useful when selecting a concrete digest and threat model, but its
    practical collision language should not alter theorem premises or claim
    wording. Full digest width and keyed domain separation are implementation
    lessons; address reflection remains Level 1 only.

## Recommended catalog entry

| Source | Pin and role | Supports | Does not support |
| --- | --- | --- | --- |
| [XET draft](https://datatracker.ietf.org/doc/html/draft-denis-xet-05) | `draft-denis-xet-05`; source commit `b29b7d1564b382245aabb65ede5fc9cfc8e93d4c`; CAS storage/transfer prior art | Separation of logical content identity from serialized xorb layout; deterministic chunking and hash aggregation; versioned binary formats; full-hash identities with truncated lookup indexes; bottom-up upload; ordered range reconstruction; remote-dedup privacy and test-vector patterns | Foldlab canonical-codec or hash-reflection laws; typed graph admission; Effect history, replay, occurrence, or session semantics; Lean proofs; TypeScript/model correspondence; IETF endorsement or an RFC |

That row is the complete permitted disposition. Any stronger use requires a new
source role and its own claim-boundary review.
