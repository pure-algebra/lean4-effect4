# Conformance ledger

Generated from the obligation inventory and the instance registry; do not edit by hand. Regenerate with mise run gen:effects.

| ID | Status |
| --- | --- |
| CAS-001 | instantiated (CODEC) |
| CAS-002 | instantiated (REJECTION-CLAUSE) |
| CAS-003 | standing review rule |
| CAS-004 | evidenced — TypeScript evidence (test/CasValueJson.test.ts) |
| RPL-001 | discharged — carrier construction (step\_iff\_reduce) |
| RPL-002 | instantiated (TRACE-EXCLUDES) |
| RPL-003 | instantiated (EXACT-STEP) |
| RPL-004 | instantiated (FAIL-CLOSED) |
| RPL-005 | instantiated (FAIL-CLOSED) |
| SES-001 | instantiated (TRACE-EXCLUDES) |
| SES-002 | instantiated (WF-PRESERVE) |
| SES-003 | instantiated (FAIL-CLOSED) |
| CMP-001 | instantiated (HOMOMORPHISM) |
| CMP-002 | instantiated (DISTINCTNESS) |
| CMP-003 | deferred to M7 |
| CTX-001 | evidenced — TypeScript evidence (test/ReplaySession.test.ts) |
| CTX-002 | evidenced — TypeScript evidence (test/ReplaySession.test.ts) |
| ADM-001 | standing review rule |
| BRG-001 | evidenced — differential suite (test/ReplayReducer.test.ts) |
| BRG-002 | pending — differential evidence at M6 |
| DUR-001 | standing review rule |
| PRJ-001 | evidenced — TypeScript evidence (test/CasValue.test.ts) |
| PRJ-002 | evidenced — TypeScript evidence (test/CasValue.test.ts) |
| PRJ-003 | evidenced — TypeScript evidence (test/CasValue.test.ts) |
| PRJ-004 | evidenced — TypeScript evidence (test/CasService.test.ts) |
| PRJ-005 | evidenced — TypeScript evidence (test/CasService.test.ts) |
| PRJ-006 | standing review rule |
| RMT-001 | instantiated (TRACE-EXCLUDES) |
| RMT-002 | instantiated (FAIL-CLOSED) |
| RMT-003 | instantiated (TRACE-EXCLUDES) |
| RMT-004 | instantiated (EXACT-STEP) |
| RMT-005 | instantiated (TRACE-EXCLUDES) |
| RMT-006 | instantiated (FAIL-CLOSED) |
| RMT-007 | instantiated (TRACE-EXCLUDES) |
| RMT-008 | instantiated (FAIL-CLOSED) |
| RMT-009 | pending — FAIL-CLOSED instance at R4 |
| RMT-010 | pending — TRACE-EXCLUDES instance at R4 |
| RMT-011 | pending — TypeScript evidence at R4 |
| RMT-012 | pending — TypeScript evidence at R4 |
| RMT-013 | standing review rule |
| RMT-014 | instantiated (FAIL-CLOSED) |
| RMT-015 | instantiated (AGREEMENT) |
| RMT-016 | pending — AGREEMENT instance at R4 |
| RMT-017 | instantiated (FAIL-CLOSED) |
| SRV-001 | evidenced — TypeScript evidence (test/server/ServerConformance.test.ts) |
| MRK-001 | instantiated (CODEC) |
| MRK-002 | instantiated (TRACE-EXCLUDES) |
| MRK-003 | instantiated (TRACE-EXCLUDES) |
| MRK-004 | discharged — carrier construction (complete\_decode\_root) |
| MRK-005 | instantiated (AGREEMENT) |
| MRK-006 | instantiated (AGREEMENT) |
| MRK-007 | instantiated (AGREEMENT) |
| MRK-008 | discharged — carrier construction (drun\_append) |
| MRK-009 | standing review rule |
| MRK-010 | discharged — carrier construction (opening\_binds\_committed) |
| MRK-011 | instantiated (CODEC) |
| MRK-012 | instantiated (CODEC) |
| MRK-013 | discharged — carrier construction (ranged\_generation\_complete) |
| MRK-014 | discharged — carrier construction (blob\_root\_addr) |
| MRK-015 | discharged — carrier construction (parse\_fragmentation\_invariant) |
| MRK-016 | discharged — carrier construction (ranged\_binding) |
| MRK-017 | pending — by carrier construction at MRK-3 |
| MRK-018 | instantiated (CODEC) |
| MRK-019 | discharged — carrier construction (response\_trailing\_rejected) |
| MRK-020 | pending — TypeScript evidence at E3 |
| SRV-001 | pending — by carrier construction at S-M1 |
| SRV-002 | pending — by carrier construction at S-M1 |
| SRV-003 | pending — TypeScript evidence at S-M2 |
| SRV-004 | pending — by carrier construction at S-M1 |
| SRV-005 | pending — TypeScript evidence at S-M2 |
| SRV-006 | pending — by carrier construction at S-M2 |

## CAS-001

Project-owned canonical node encoding has one byte representation per admitted node.

**Sentence:** Canonicalization is idempotent, canonical values round-trip, and the encoding is injective on canonical forms — every admitted CAS node has exactly one byte representation: canonicalization is the identity on the admitted-node carrier, the decoder accepts nothing outside the encoder image, and trailing bytes are rejected.

## CAS-002

Graph admission rejects dangling or wrong-kind references.

**Sentence:** Admission rejects exactly the raw values a named clause condemns, and every rejection names its clause — a CAS node enters the store only when every typed reference resolves at its declared kind: a reference to an unbound address is rejected as dangling, and a reference whose declared kind tag disagrees with the resident node's kind tag is rejected as wrong-kind.

## CAS-003

Every address law is assigned to hash Level 0 or carries an explicit Level-1 hInj premise; no theorem occupies Level 2.

## CAS-004

A value's canonical encoding is the UTF-8 bytes of its compact JSON rendering — codepoint-sorted keys, integers only, JSON short-escape strings — one encoding per structure, language-neutral.

## RPL-001

Replay is deterministic for a fixed admitted state and request.

## RPL-002

Replay-mode decision traces never select live delegation, and replay construction has no live-service requirement.

**Sentence:** In replay mode, no step ever emits a live-delegation decision — replay is hermetic: whether a live adapter was requested is a projection of the decision trace, and in replay mode that projection is empty by law, never by luck.

## RPL-003

Matching consumes exactly the permitted occurrence.

**Sentence:** When the emitted invocation matches the entry at the cursor, one reducer step advances the cursor by exactly one — a matching request consumes exactly the permitted occurrence: never zero, never two.

## RPL-004

Mismatch fails closed.

**Sentence:** When request-side compatibility at the cursor fails, the step rejects with a typed mismatch category and the cursor is unchanged — a mismatch fails closed: it consumes nothing, names its category, and is terminal for the attempt; nothing falls through to a live adapter.

## RPL-005

Completion rejects unconsumed suffix entries; the rejection carries the program's terminal so far.

**Sentence:** When completion arrives before the cursor reaches the history length, the step rejects with the unconsumed-suffix category and the cursor is unchanged — the rejection carries the program's terminal so far, so a same-looking final value cannot hide a recorded action that was never re-emitted.

## SES-001

Record-mode append failure aborts the session through the transport seam; histories are truthful prefixes, never gapped subsequences.

**Sentence:** In an aborted session, no step ever emits an occurrence-append decision — a record-mode append failure aborts the session structurally, nothing appends past the failure, and histories stay truthful prefixes, never gapped subsequences.

## SES-002

Every reducer step preserves session-state well-formedness.

**Sentence:** On every input, one reducer step from a well-formed session state yields a well-formed session state — the cursor stays inside the history, and record mode keeps it pinned to the history length.

## SES-003

Record-mode delegation is exclusive and outcome-solicited; unsolicited steps fail closed and lawful record runs append in invocation order.

**Sentence:** When record-mode delegation is not solicited — an invocation while one is outstanding, or a recorded outcome without or beside its outstanding invocation — the step rejects with a typed category and the history length is unchanged; delegation is exclusive, outcomes append only as solicited, and lawful record runs append in invocation order.

## CMP-001

Sequential interpretation threads replay state compositionally across success and typed-failure outcomes.

**Sentence:** Interpretation respects return and sequential bind across both outcome cases — sequential interpretation threads the replay session state compositionally: a returned value consumes nothing, a nested program continues from exactly the state its prefix reached, and both halting cases — the program's own typed failure and the session's typed rejection — short-circuit carrying the state they stopped at, so the cursor neither resets nor forks across composition; the recorded outcome envelope reaches the leaf continuation on both channels, so recovery fires exactly as it did live.

## CMP-002

Identical requests remain separate occurrences.

**Sentence:** Two occurrences with identical invocation content remain distinct occurrence positions — the store deduplicates request nodes while the history keeps entries distinct; position is the occurrence identity, and every solicited call pair claims a fresh one.

## CMP-003

Transparent and opaque policies have distinct, declared framed traces.

## CTX-001

Wrapped service construction supplies the same caller-facing interface without recursive lookup.

## CTX-002

Conforming orchestration cannot consult default Clock/Random behavior; replay-mode tripwires surface ambient use as a Violated outcome.

## ADM-001

G2 traceability distinguishes reified Lean-program quantification from discipline-conforming TypeScript orchestration.

## BRG-001

Model fixtures and the TypeScript reducer compare one declared normalized decision trace.

## BRG-002

The pinned Effect integration agrees on the enumerated domain.

## DUR-001

No exactly-once claim crosses the live-action/history-append crash gap.

## PRJ-001

Value-descriptor identity is explicit and checked: kind tag and revision are declared, and reading verifies the expected root kind.

## PRJ-002

A value round-trips through its descriptor: get after put returns the declared domain canonicalization.

## PRJ-003

A payload failing the descriptor's schema is rejected with a typed projection error distinct from the CAS error family and the mismatch taxonomy.

## PRJ-004

Fixed-root hydration matches by-value construction: the layer builds the same caller-facing shape, construction errors stay on the layer, and method error unions never widen.

## PRJ-005

Hydrated record construction stays non-recursive and single-wrapped: layerAs targets the internal live role only, never resolves the public wrapper, and double wrapping stays rejected.

## PRJ-006

Equal roots imply no stronger value equality than the hash-hypothesis lattice permits.

## RMT-001

No remote-loaded node reaches the cache or the caller without passing standard admission; a wire-supplied digest is a routing hint, never an identity.

**Sentence:** When the pending input is not entitled — its bytes do not answer an in-flight operation, pass the declared budget, and verify for that operation's key — no step ever emits a cache decision or a return to the caller: a wire-supplied digest is a routing hint, never an identity, and only verification admits a remote-loaded node in either direction.

## RMT-002

Declared sizes and counts are checked against declared budgets before any hashing or decoding.

**Sentence:** When a declaration exceeds the declared budgets — a fresh upload whose content size is over the byte budget, or a load response whose declared length is — the step rejects with the typed budget rejection, the cache is unchanged, and no verification, cache, or return decision occurs: at the model's altitude nothing over budget proceeds toward admission, and the shell obligation that an oversized declared body is never read or buffered arrives with the R2 streaming byte counter.

## RMT-003

An integrity failure is terminal for those bytes: no wire attempt ever repeats unchanged content.

**Sentence:** When a key-content pair stands integrity-rejected, no step ever issues an upload command carrying that key and that exact content again, under any operation identifier — the rejection memory only grows, so an integrity failure is terminal for those bytes over the whole run, and only changed content can try the wire.

## RMT-004

An already-present exact-digest upload resolves as success with zero additional transfer commands.

**Sentence:** When an upload request names a key already admitted in the cache with content that verifies for it — within the byte budget, not integrity-rejected, its identifier free — one machine step changes the issued-command count by exactly zero: an already-present exact-digest upload resolves as success with no transfer, and duplicate content never becomes duplicate wire traffic.

## RMT-005

No admission or publication decision is taken on a presence answer alone, and absence is never negatively cached by default.

**Sentence:** When the pending input answers an in-flight find-missing operation, no step ever caches: a presence answer is planning data that steers upload scheduling and nothing else — it admits nothing, returns nothing, publishes nothing, and absence is never negatively cached, because no admission reading of the reported-missing set exists at all.

## RMT-006

A batch response accounts for every requested key per-key; an unaccounted or misaligned key fails the batch closed with no cross-key substitution.

**Sentence:** When a batch response fails exact per-key accounting — every requested key answered once, in request order, nothing extra — the whole batch is rejected with the typed batch rejection and the cache, confirmed, and published sets stay exactly as they were: no per-key answer is partially applied and no answer substitutes across keys.

## RMT-007

Children upload before parents and the root publishes last; server acceptance of a parent never implies closure.

**Sentence:** When the pending input is not an entitled publish request — the root and every key of its declared closure confirmed by verified acknowledgments or loads, on a free identifier — no step ever issues a publish command: children upload before parents, the root publishes last, the refusal is a typed ordering refusal, and server acceptance of any upload confirms exactly that key, never its children.

## RMT-008

At any declared interruption point, no partial node is admitted, no root is published, and resources are closed.

**Sentence:** When an interruption arrives for an operation in flight, the step resolves as a typed give-up with the cache, confirmed, and published sets exactly as they were — no partial node is admitted, no root is published, and the in-flight entry is cleared so resources release without semantic residue.

## RMT-009

Interrupted transfers resume only from a re-queried, server-reported committed offset, tolerating regression.

## RMT-010

Retries are bounded by declared policy, rendered as decisions, and never repeat a non-idempotent wire attempt.

## RMT-011

Server-declared limits are discovered at layer acquisition and honored by splitting or rerouting.

## RMT-012

Verification and credential scope are independent of transport origin; credentials never cross redirect hosts.

## RMT-013

Presence-style operations carry a namespace; no global existence query exists on the surface.

## RMT-014

Batch framing, capability documents, and presence indexes parse fail-closed with the same posture as node bytes.

**Sentence:** When capability-document bytes are not the canonical encoding of representable limits, the closed decoder returns nothing — truncation, oversize fields, and trailing bytes are all rejected with the same fail-closed posture as node bytes, and a successful decode's input is exactly the canonical encoding of its result.

## RMT-015

A successful remote load implements the logical admitted-node load.

**Sentence:** On leaf admitted nodes within the declared byte budget, the remote client's completed load run and the logical admitted-node store load agree at the delivered bytes under exact canonical encoding — a successful remote load implements the logical admitted-node load: what the machine delivers is precisely the canonical encoding of the node the store holds at that address, so remote success can never produce a node the logical load would not.

## RMT-016

A local admitted-node hit is observationally equivalent to a successful remote load for immutable nodes.

## RMT-017

Attested presence confirms for publish: a key the peer reports present whose bytes the client holds and verifies locally enters the confirmed set; without the presence report or the local verification the attestation is refused, and attestation never admits to the cache.

**Sentence:** When an attestation is not entitled — the peer never reported the key present, or the held bytes fail local verification — the step refuses with a typed result and the confirmed count is unchanged; an entitled attestation confirms the key for publication without admitting anything to the cache.

## SRV-001

The server's semantic core is the interpretation of the model's finite request trees over the storage seam: for every scripted session, the implementation returns the model's outcomes and issues exactly the model's storage events, in order.

## MRK-001

One chunk-tree root per declared recipe and content: chunking is a lossless declared partition, and the root is a function of the recipe parameters and the bytes.

**Sentence:** Chunking under the declared recipe is a lossless partition: rejoining the chunks restores the bytes exactly, two different contents never chunk alike, and the checked inverse accepts exactly the lists chunking produces — the recipe is declared, never inferred, so one root exists per recipe and content and no rechunk can mint a second identity.

## MRK-002

The streaming decoder emits a chunk only after it verifies against its expected subtree address; against a committed chunk list, every emission matches, or a hash-collision witness exists in the consumed prefix.

**Sentence:** When the pending input is not entitled to emit — the decoder is not active on an in-range leaf frame whose expected address the input chunk's leaf pre-image hashes to — no step ever emits: emission IS verification, and against a committed list every emission matches the committed chunk at its index or a hash-collision witness exists in the consumed prefix, the decoder being under no obligation to detect the collision.

## MRK-003

No decoder run observes the length or end-of-input before the final chunk validates against the root.

**Sentence:** When the pending input is not a verified final chunk, no step ever validates the length: the declared length is exposed to the caller only when the final chunk itself validates against the root, so a truncated or length-tweaked stream can never make the decoder vouch for a length it did not verify.

## MRK-004

A complete decode determines its root: the recomputed root of the emitted output equals the expected root, so no output completely decodes under two roots.

## MRK-005

Slice decoding agrees with the whole decode restricted to the requested range.

**Sentence:** On nonempty chunk lists and any requested range, the slice decode over the range extractor's stream and the whole decode filtered to the range agree at their emission lists — a slice emits exactly the bytes the whole decode would emit at those offsets, never more, so slice and encoding carriers stay transport while roots and decoded bytes stay the identity.

## MRK-006

The inclusion verifier accepts exactly the openings whose recomputed root matches; honestly generated paths verify; and two accepted openings of one root and index with different leaves yield a computable collision.

**Sentence:** On every opening — an index, a count, leaf bytes, a sibling list, and an expected root — the executable inclusion verifier and the decided inclusion judgment agree at the boolean: the verifier accepts exactly the openings whose derived-side recomputation reaches the expected root, honestly generated paths verify, and two accepted openings of one root and index carry the same bytes or exhibit a computable hash collision.

## MRK-007

The consistency verifier accepts exactly the related root pairs, and consistency forces prefix agreement or exhibits a collision.

**Sentence:** On every claimed relation — an old size, a new size, two roots, and a proof — the executable consistency verifier and the decided consistency judgment agree at the boolean: the verifier accepts exactly the proofs whose size-derived rebuild reproduces both roots with the proof exactly consumed, honestly generated proofs relate the committed prefix root to the whole root, and an accepted proof against an honest new tree forces the old root to be the committed prefix's root or exhibits a computable hash collision.

## MRK-008

The decoder is a pure fold: runs compose over input concatenation, so transport fragmentation below the parser cannot change any emission, rejection, or terminal.

## MRK-009

Slice and encoding bytes are transport, never identity: only roots and decoded bytes are identity-bearing, and encoding malleability is documented rather than fought.

## MRK-010

An accepted opening binds its index's committed chunk: bytes accepted at an index equal the chunk the tree commits at that index, or a collision is exhibited.

## MRK-011

Inclusion-opening documents parse fail-closed and exactly: sides are never encoded, truncation and malformed fields are rejected, and a successful decode's input is exactly the canonical encoding of its result.

**Sentence:** Inclusion-opening documents parse fail-closed and exactly: the canonical encoding carries the index, the count, the length-prefixed leaf bytes, and the sibling addresses root-side first with sides never encoded; truncation, malformed fields, and trailing content are rejected, and a successful decode's input is exactly the canonical encoding of its result.

## MRK-012

Range-stream documents parse fail-closed and exactly over the decoder's input alphabet: unknown tags and truncated items are rejected, and a successful decode's input is exactly the canonical encoding of its result.

**Sentence:** Range-stream documents parse fail-closed and exactly over the decoder's input alphabet: a twelve-byte header — the declared total and the requested range, echoed so a client fails closed on disagreement — then tagged items, a bare skip, a length-prefixed chunk, or a parent's two child addresses; unknown tags and truncated items are rejected, the framing is self-delimiting, and a successful decode's input is exactly the canonical encoding of its result.

## MRK-013

Ranged stream generation is complete: for any requested range the honest extractor's stream decodes to its done status and emits exactly the owed ranged emissions.

## MRK-014

The Merkle address function instantiated as the address of the canonical blob-node encoding makes a blob root an ordinary content identifier, and a bounded pre-image collision transfers to a byte-level hash collision.

## MRK-015

Byte-level frame parsing is incremental and fragmentation-invariant: all fragmentations of one complete body yield the same parsed inputs and terminal, and truncation never yields completion.

## MRK-016

Every input trace accepted for a root and range emits exactly the committed bytes at those positions or supplies a collision witness; honest-generator completeness is a separate theorem.

## MRK-017

Successful byte-range slicing equals the flattened whole restricted to the requested byte window under the declared bounds.

## MRK-018

A blob manifest commits recipe identity, total bytes, and leaf count; readers select semantics from the recipe id and unknown ids fail closed; changing any identity-affecting recipe parameter changes the manifest id.

**Sentence:** Blob-manifest contents parse fail-closed and exactly: the canonical sixteen-byte payload commits the recipe identity, the total byte length, and the leaf count; truncation, trailing content, and UNKNOWN RECIPE IDENTIFIERS are all rejected at decode, so a reader selects semantics from the registered recipe id and never guesses, and changing any identity-affecting recipe parameter changes the manifest identity.

## MRK-019

A proof response is exactly one complete decode: trailing content after the machine's done status is rejected at the framer, and responses are bounded by declared output and proof-amplification budgets.

## MRK-020

A ranged blob read touches exactly the proof-necessary nodes: the manifest, the parents on intersecting paths, the intersecting leaves, and their chunk data — never a node outside the range's spine.

## SRV-001

A successful root-head transition implies the manifest and selected closure were admitted at that transition under its compare-and-set precondition, and no failed transition changes the visible head; crash survival is a distinct adapter property.

## SRV-002

Server admission runs bounded receive, closed decode, address recomputation, and reference checks before write-if-absent, and loads revalidate bytes before crossing the semantic seam.

## SRV-003

Write-if-absent distinguishes stored, already-present-identical, and same-address-different-bytes; the third is an integrity fault that fails, is observable, and blocks publication.

## SRV-004

Served capabilities are the intersection of implementation, principal policy, store properties, registry properties, and configured limits; a served capability never exceeds an enforced one.

## SRV-005

Adapters declare a durability class and success claims never exceed the declaration; the memory adapter is volatile, and crash-persistent claims carry platform-pinned write, rename, and flush evidence.

## SRV-006

Root heads move only by compare-and-set; concurrent publishers serialize; stale expectations fail with the standard precondition semantics.
