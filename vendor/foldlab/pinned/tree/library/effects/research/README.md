# Effects library research inputs

Status: project-local copies, 2026-08-26.

These documents are copied inputs for scoping the `effects` library. They are
not new authorities, specifications, or claim-bearing outputs. Their canonical
owners remain the corresponding files under the repository's `docs/` tree;
refresh these copies explicitly rather than editing them independently.

The copies are retained because the project bootstrap requested a local
research pack. The sync task refreshes them from the canonical owners
(`mise run gen:effects:research`), and the gate asserts byte equality
(`check:effects:research`, part of the root check). No claim may cite a
copied path when a canonical path exists.

## Effect research reports

- [`effect-operational-semantics-reference-sweep.md`](docs/research/effect-operational-semantics-reference-sweep.md) — copied from `docs/research/`
- [`effect-runtime-ground-truth-extraction-scope.md`](docs/research/effect-runtime-ground-truth-extraction-scope.md) — copied from `docs/research/`
- [`effect-modeling-wasm-interoperability-optimization-frontier.md`](docs/research/effect-modeling-wasm-interoperability-optimization-frontier.md) — copied from `docs/research/`

## Effect semantics reference pack

- [`README.md`](docs/effect-typescript-semantics/README.md)
- [`CONTEXT.md`](docs/effect-typescript-semantics/CONTEXT.md)
- [`CLAIM-GATES.md`](docs/effect-typescript-semantics/CLAIM-GATES.md)
- [`IMPLEMENTATION-PLAN.md`](docs/effect-typescript-semantics/IMPLEMENTATION-PLAN.md)

The reference pack is copied from `docs/effect-typescript-semantics/`. Its
internal links to documents outside this snapshot point back to their canonical
repository locations.

## Project research

- [`cas-soundness-roundtrip-references.md`](cas-soundness-roundtrip-references.md)
  separates codec exactness, CAS store algebra, structural admission,
  authenticated observation, and crash recovery, then maps theorem-bearing
  references for each layer to the current Effects and machine obligations.
- [`fp-lean-cas-proof-obligations.md`](fp-lean-cas-proof-obligations.md)
  maps the official *Functional Programming in Lean* treatment of strengthened
  accumulator invariants, functional equivalence, index bounds, and termination
  measures to the current and deferred Effects CAS proof obligations.
- [`cas-effect-program-replay.md`](cas-effect-program-replay.md) studies how a
  content-addressed program graph, an append-only effect history, checkpoints,
  and replay witnesses must remain separate. It proposes a fail-closed replay
  design and staged research direction without selecting a domain contract.
- [`effect-service-cas-derivation-design.md`](effect-service-cas-derivation-design.md)
  proposes an explicit domain-value projection and Effect `Layer` hydration
  seam, then evaluates remote-store, batching, cache, scoped-client, offline,
  and checked materialized-graph considerations without ratifying an API.
- [`xet-prior-art.md`](xet-prior-art.md) evaluates the exact
  `draft-denis-xet-05` edition as bounded CAS storage/transfer prior art for the
  ratified Effect Replay design. It records reusable materialization patterns,
  strict non-support boundaries, and deferred recommendations without amending
  the contract.
- [`tree-sitter-plan-prior-art.md`](tree-sitter-plan-prior-art.md) records the
  `lean4-tree-sitter` implementation plan as design prior art for the
  conformance workflow's schema bundles: proof obligations as structure
  fields, kits made unrepresentable-when-missing, and the sentence field as
  the plain-meaning source.
- [`lean4-markdown-prior-art.md`](lean4-markdown-prior-art.md) records the
  `lean4-markdown` library as design prior art for the typed human-surface
  emitter: the `Represent` projection typeclass and arity-checked tables,
  re-expressed in an owned module whose default path escapes (route (b),
  ruled 2026-08-26).
- [`effect-scope-and-ambient-tripwire-analysis.md`](effect-scope-and-ambient-tripwire-analysis.md)
  answers, against the pinned runtime source, whether Scope APIs are
  warranted for CAS behavior (not in the in-memory slice; two named
  adoption points) and how the tracing/Clock ambient trap resolves
  (`TracerTimingEnabled = false` in replay construction; deterministic
  time by describing it), without ratifying any change.
- [`effect4-schema-custom-codecs-for-cas-values.md`](effect4-schema-custom-codecs-for-cas-values.md)
  reviews the pinned v4 Schema implementation for custom encode/decode
  machinery behind CAS value descriptors: the sanctioned built-in
  constructor vocabulary, the `decodeTo`/`encodeTo` discipline with a
  per-descriptor round-trip fixture, a `Schema.Json` static-bound
  candidate, and `SchemaRepresentation` noted as future prior art —
  without ratifying any change.
- [`remote-cas-prior-art-compendium.md`](remote-cas-prior-art-compendium.md)
  condenses a four-sweep study of shipped CAS practice — wire protocols
  at exact pins (Git, OCI, REAPI, Nix, OSTree, casync), distributed
  addressing theory (IPFS, BLAKE3/bao, RBSR, chunking regimes, Venti),
  production failure semantics (GC races, presence-oracle desync,
  negative caching, the S3 2008 control-state lesson), and
  conformance-testing prior art (OCI suite, git's protocol fixtures,
  ShardStore, FoundationDB, etcd robustness, BoringSSL, sans-io) —
  with five cross-sweep convergences and per-part implication lists.
- [`remote-cas-conformance-design.md`](remote-cas-conformance-design.md)
  synthesizes the compendium into the remote-CAS conformance design:
  a sans-io client decision machine over an abstract exchange
  alphabet, fault schedules as manifest fixture data (flagged novel
  ground), a sixteen-row candidate obligation catalog with family
  fits, the four-lane evidence architecture, the staged R ladder, and
  the remote Pass A docket skeleton — hypotheses only, nothing
  promoted.
- [`remote-transport-standards-and-lean-models.md`](remote-transport-standards-and-lean-models.md)
  maps current HTTP/1.1–3, gRPC, JSON-RPC, SSE, and WebSocket standards
  to remote-CAS client obligations; audits Lean protocol runtimes and
  transition/refinement libraries (including LeanServer); and proposes
  a weak-trace refinement plus real-transport conformance architecture.
  The model and theorem docket remain unratified G0 research.
- [`streaming-sync-cas-api-prior-art.md`](streaming-sync-cas-api-prior-art.md)
  surveys the concrete APIs of REAPI/ByteStream, OCI, tus, `object_store`,
  Git LFS, IPFS/IPLD/GraphSync, Nix, XET, Hypercore, Automerge, and pinned
  Effect v4; compares them with the R2 stream-shaped whole-object baseline;
  and proposes private wire adapters and protocol drivers beneath distinct
  `CasTransfer`, `CasBlob`, and `CasSync` deep modules. All API shapes and
  sequencing recommendations remain unratified G0 research.
- [`effect4-layer-semantics-remote-service-design.md`](effect4-layer-semantics-remote-service-design.md)
  reviews the pinned v4 layer, scope, stream, and HTTP-client semantics
  behind the ratified four-service streaming architecture, then proposes
  the service shapes, layer graph, typed error taxonomy, and an
  eight-item decision docket (transport never a service key, tagged
  upload restartability, completion witness as a typed channel terminal)
  for the R2 slice — recommendations only, nothing ratified.
- [`effect-vitest-conformance-harness.md`](effect-vitest-conformance-harness.md)
  designs the generic @effect/vitest harness for consuming Lean
  conformance families: one wire-schema binding per family over two
  kind-level runners, the system under test as a Layer so the four
  evidence lanes select by substitution, a manifest-source service with
  closed decoding as the drift tripwire, a peer matrix whose expected
  divergences make LeanServer's audited gaps detection-target
  assertions, and TestClock as the R4 deterministic-time hook — an
  eight-item decision docket, nothing implemented while R2 is in
  flight.
- [`merkle-conformance-proof-infrastructure.md`](merkle-conformance-proof-infrastructure.md)
  designs the Merkle-structure conformance and proof infrastructure:
  the bao verified-streaming spec and RFC 9162's proof algorithms
  worked first-hand into ten MRK obligation candidates (emission
  soundness with the keeps-consuming correction, the final-chunk
  temporal rule, no decoding collisions, slice–whole agreement,
  verifier reflections, position binding), a sans-io decoder machine
  over structural pre-images with constructive collision-witness
  disjuncts, and a mechanized-prior utilization map anchored on
  veri-auth's collision-free logic and VCVio's computable collision
  extraction — with the absence result that no prover has mechanized
  bao streaming or the RFC 9162 algorithms. A nine-item decision
  docket; nothing ratified.
- [`server-reference-and-verified-reads.md`](server-reference-and-verified-reads.md)
  is the target design for the published shape: the four-artifact
  package (client, reference server over pluggable `CasServerStore`
  backends with policy-derived capabilities, black-box conformance
  kit, profile document), the blob mode as a node graph rather than a
  second store (position-bound leaves per the proved model, the chunk
  recipe a profile constant, explicit mode), the proof plane whose
  range-stream wire language is exactly the verified-streaming
  decoder's input alphabet, and the Q1–Q5 / F2 / S-lane dockets —
  dockets pending ratification, target sections non-normative.
- [`server-reference-and-verified-reads-prior-art-review.md`](server-reference-and-verified-reads-prior-art-review.md)
  is the G0 prior-art and usability review of the server target
  design against revision-pinned sources (Unison newly pinned;
  Git/OCI/REAPI/ByteStream/Nix/Boxo/IPLD/XET/Bao reused through
  standing receipts): four blocking corrections (wire alphabet,
  server-publication versus client-publication, the blob manifest
  envelope, storage-contract underspecification), the
  deep-module architecture (`CasBlob`, `CasRepository`,
  `CasServerCore`, object-store and root-registry seams), and the
  O-obligation list adopted as the MRK-3 and S-M dockets.
- [`cas-scheme-0-hash-ruling.md`](cas-scheme-0-hash-ruling.md) is the
  G0 decision docket pinning the production address scheme (H1–H6):
  SHA-256 over the canonical node encoding through WebCrypto, full
  width, profile-pinned with no per-address prefix, the hash as an
  injected Effect service, generated known-answer fixtures, and the
  digests-are-not-secrets boundary — pending ratification; the
  package must not publish before it.
- [`leanserver-adoption.md`](leanserver-adoption.md) is the formal
  adoption record for LeanServer at its ratified pin: the
  materialized gitignored clone, blob-level digest verification
  against the transport-standards receipt (with the Windows CRLF
  caution), the two adopted roles, the C5 claim boundary (never a
  standards oracle; its theorem count is not estate evidence), the
  audited gaps as named detection targets, and the
  own-slice integration roadmap.

## Local external inputs

- [`BLAZE.md`](BLAZE.md) records the study note for the gitignored checkout at
  `.reference/clones/blaze`. Blaze has not been admitted to the canonical
  Source Lock, so the note is prior-art orientation rather than claim evidence.
- `.reference/papers/relational_separation_logic_for_effect_handlers.pdf` and
  its LiteParse reading copy under `.reference/papers/extracted/` are local-only
  paper inputs. They remain pending paper-lock and catalog admission and must
  not be cited as estate evidence until that admission is completed.
- [`general_compilation_techniques_effect_handlers_3473576.pdf`](docs/general_compilation_techniques_effect_handlers_3473576.pdf)
  is an off-pattern local copy, not an admitted project document or evidence
  source. M0 must either relocate its exact bytes into `.reference/papers/`
  through the provenance procedure or remove the duplicate after confirming a
  canonical copy. No move or deletion is authorized by this note.
