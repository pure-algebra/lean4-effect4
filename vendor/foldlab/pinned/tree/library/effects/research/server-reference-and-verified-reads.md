# Server reference, blob mode, and verified partial reads — target design

STATUS: design survey — hypotheses and dockets only; nothing here is
normative until ratified into the profile document or the plan. Wire
clauses that are already normative live in `PROFILE-CAS-HTTP-0.md`.

Direction (operator, 2026-08-27): design the server tooling and API
target first; work toward the reference server; the goal is a
published library; verified partial reads are the active workstream.

## 1. Where this ends up

The published artifact is not "a client library." It is a small
protocol with a proved model, shipped as four things from one
package:

1. **Client** — the verified sync client (existing lane).
2. **Reference server** — `CasServer.layer` over pluggable storage,
   in the same package, so client and server come from one install
   and a developer stands up verified sync in one file.
3. **Conformance kit** — the model-generated vector families packaged
   as an executable black-box suite: implement a server in any
   language, point the kit at an authority, get a verdict.
4. **The profile document** — the wire spec, outsider-legible,
   versioned with the model.

The splash gate stays as ratified: the TypeScript verifier passing
end-to-end against the reference server.

## 2. Target server architecture

- `CasServer.layer(config)` composes platform HTTP-API handlers from
  the SAME closed codecs the client uses — one codec module serves
  both directions. (Corrected at the prior-art review: this reduces
  intra-package mismatch; it does not make drift impossible — a
  client and server can agree on the same wrong implementation, so
  the exactness theorems, generated vectors, and refinement gates
  independently constrain the shared codec.)
- `CasServerStore` — the storage backend service (memory and
  filesystem ship; anything else is user-provided). The server core
  enforces admission on upload: a conforming server verifies
  canonical bytes against the address before storing, mirroring
  client admission. A server never stores what it cannot re-derive.
- `CasServerPolicy` — auth hooks and declared limits. The capability
  document is DERIVED from policy, never hand-written, so served
  capabilities always equal enforced capabilities.
- The test-side conformance peer interface remains the adoption seam:
  the reference server is its production realization, and the adopted
  LeanServer binds behind the same seam at its own slice, informing a
  future Lean SERVER machine whose laws would generate
  server-conformance vectors the same way the client machine does
  today.

## 3. Blob mode (client-side): yes, and it is one store, not two

Question on the table: does the client need a blob mode? Yes — three
forcing functions:

- The byte budget bounds any single node, so content above
  `maxBlobBytes` has NO lawful representation today; the library's
  answer to "store a large payload" is currently "you cannot."
- Verified partial reads only exist over content that was COMMITTED
  as a chunk tree; a range proof of an unchunked node is meaningless.
  The partial-reads workstream requires the blob data model.
- The Merkle machinery (MRK-1) has no consumer until blobs exist;
  the plan already names chunked `CasBlob` as the deferred
  implementation consumption.

The design that keeps it one system:

- **A blob is a node graph, not a second store.** Leaves are ordinary
  CAS nodes carrying (index, chunk bytes) exactly as the proved
  pre-image model does; parents are ordinary two-reference nodes; the
  blob's identity is the ROOT NODE'S ADDRESS — an ordinary content
  identifier. No parallel identity kind, no parallel storage plane.
- Everything already proved then applies verbatim: find-missing
  negotiation plans a blob push; children-first upload IS leaf-first
  upload; the confirmed-set publish gate makes "the blob is fully
  present before its root is visible" a theorem we already have;
  the pull composite (staging area) pulls blob closures with no new
  machinery.
- **Position-bound leaves, by the proved model.** Leaf pre-images
  carry the index (as in the inclusion-binding theorem and as BLAKE3
  binds its chunk counter), so identical chunk bytes at different
  positions are distinct nodes. The cross-position deduplication this
  forgoes is the same trade BLAKE3 makes; position binding is what
  the opening-binds-committed law is made of. Documented, not
  fought.
- **The chunk recipe is a PROFILE constant, never a capability.**
  If chunk size were server-declared, one payload would chunk
  differently per authority and content identity would fragment
  across servers. The profile pins the canonical chunk size and the
  standards split (the power-of-two-below rule shared by RFC 9162
  and BLAKE3, already the model's `pow2Below`); a server whose
  declared byte budget cannot host the profile chunk size simply
  cannot host blobs, discovered at capability probe.
- **Explicit mode, never a threshold.** `CasBlob.put` is a distinct
  operation; an ordinary value put never silently becomes a blob
  (the authority-mode precedent: no silent fallback anywhere).

Caller surface (target):

- `CasBlob.put(stream)` → blob root (chunks canonically, builds the
  tree locally, admits nodes locally; wire transfer is `push`).
- `CasBlob.read(root)` → verified whole-blob stream (early emission
  chunk-by-chunk, each chunk root-bound by the streaming decoder —
  replacing spool-everything for large content).
- `CasBlob.slice(root, from, count)` → verified range stream (the
  partial read).
- `CasBlob.verify(opening)` → inclusion check for a single chunk
  (the audit primitive).

## 4. The proof plane (wire, target — planned in the profile)

Two endpoints over root-addressed blobs:

- **Range stream** — `GET {authority}/stream/{root-hex}` with `from`
  and `count`: response body is a closed header (big-endian u32
  total-leaf-count, u32 from, u32 count echoed — client fails closed
  on any disagreement with its request) followed by a framed
  pre-order stream whose item alphabet is EXACTLY the verified
  streaming decoder's input language: `0x00` bare (skip — a subtree
  outside the range; its address was already bound by its parent, so
  carrying one would be a side channel), `0x01` + u32 length + chunk
  bytes (leaf), or `0x02` + two 32-byte child addresses (parent).
  The client runs the decoder; every emitted chunk is root-bound by
  construction, fragmentation cannot change outcomes (the pure-fold
  law), a complete decode determines its root, and slice agreement
  ties the range read to the whole read. The wire format being the
  decoder's input alphabet means the committed MRK stream vectors
  constrain the wire directly. (Corrected at the build: an earlier
  draft of this sketch had the skip carrying a hash — the model's
  skip is bare, and the model is right.)
- **Inclusion opening** — `GET {authority}/proofs/{root-hex}/{index}`:
  a closed opening document (u32 index, u32 total, u32 leaf length +
  leaf bytes, then the sibling hashes bottom-up). The verifier
  derives sides from index and total — the encoding-malleability
  boundary mint — and acceptance is exactly recomputation-match with
  the collision-extraction disjunct behind binding.

Whole-blob verified download is the degenerate range (`from = 0`,
`count = total`). The event plane (advisory notifications) remains a
named future beside these; notification never constitutes admission.

## 5. Dockets

**MRK-2 / partial reads, conformance lane (needs ratification —
Q1–Q5):**

- **Q1** — MRK-007 as planned: the consistency verifier (the RFC 9162
  subproof shape over append-only structures) with reflection iff and
  the prefix-agreement corollary.
- **Q2** — proof-document codecs under the control-codec discipline:
  the opening document and the stream header/item framings, each with
  decode-of-encode identity and exactness (decode's image IS the
  canonical encoding), emitted as CODEC-family vector rows, additive.
- **Q3** — ranged stream generation completeness: the server-half
  theorem — for any tree and in-range request, the generated
  skip/leaf stream decodes completely and emits exactly the requested
  range (the existing whole-stream generator law, generalized to
  ranges), so the stream endpoint has an honest reference emitter.
- **Q4** — the blob refinement tie: the abstract Merkle hash
  instantiated as the address of the corresponding canonical node
  encoding (leaf and parent node kinds), tying the proof plane's
  roots to ordinary content identifiers — the blob-mode keystone,
  AGREEMENT-shaped like the machine-to-store tie.
- **Q5** — the key-list codec's Lean exactness treatment (the W2
  framing), closing the RMT-014 narrowing observation — landed after
  the F1 delivery so committed manifests do not move mid-slice.

**F2, implementation lane (after F1):** TypeScript mirrors of
chunk/tree/verify/decoder consuming the committed MRK families
through the harness; the proof-document codecs; `CasBlob` put/read/
slice/verify over the mirrored machinery; direction-2 mutants
verbatim.

**S-lane (after F2):** S1 — the reference server and conformance-kit
packaging as section 2; S2 — the LeanServer binding slice and the
server-machine survey.

## 6. Priority recommendation

Conformance lane proceeds with Q1–Q4 on ratification (the proof
substance of partial reads; zero collision with the F1 slice in
flight), then Q5 at F1 acceptance. Implementation lane: F1 (in
flight) → F2 → S1. The axiom-profile gate lands between slices as
standing hardening.
