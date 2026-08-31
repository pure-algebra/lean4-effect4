# CONTEXT — the Effect Replay context

Status: RATIFIED by grilling 2026-08-26 (operator, in-session; recommendations
accepted, with one operator strengthening: full independence from the Entity
Store context). Amended 2026-08-26 at the M1 interface freeze
(operator-ratified): the append-failure mechanism is a structural session
abort through the transport seam — see the replay session entry. Amended
2026-08-27 at the CMP-001 ratification (operator-ratified): two entries
minted — reified program and interpretation halt. Amended 2026-08-27 at
the descriptor Pass A (operator-ratified): four entries minted — value
descriptor, typed root, projection codec failure, hydrated service
layer. Amended 2026-08-27 at the remote Pass A (operator-ratified):
four entries minted — remote exchange event, wire command, fault
schedule, remote client machine. Amended 2026-08-27 at the R1
acceptance (operator-ratified): three entries minted — streamed
transfer service, event notification service, remote transport.
Amended 2026-08-27 at the MRK-1 ratification (operator-ratified):
four entries minted — chunk tree, inclusion opening,
verified-streaming decoder, encoding-malleability boundary — and the
R2-delivered transfer and transport labels filled. Amended 2026-08-27
at the R1–R11 ratification (operator-ratified, R11): one entry minted
— solicited delegation — the mismatch taxonomy grown to eight
categories, and the replay session's form gains the pending slot and
its well-formedness clause. Amended 2026-08-28 at the CAS-first
ratification (operator-ratified, the seven rulings all as recommended):
the dual-lane effects-model@0.3.0 corpus is retired in place to
`library/effects/archive/lean-model-0.3` (tag `archive/effects-model-0.3`)
and the record/replay plane stashed to
`library/effects/archive/replay-plane` while the library focuses on CAS
semantics, the DSL, and metaprogramming; the live Lean model moves to
`library/cas` and every code label follows its file. Six entries minted
— byte-plane seam, path reader, store-root layout, typed-reference
marker law, store loader, server plane — and the typed root gains its
edge form and model carrier. Replay-plane entries remain minted
vocabulary; their code labels point into the stash. Amended 2026-08-28
at the schema self-description landing (operator-directed, in-session):
two entries minted — canonical schema, materializer. Amended 2026-08-28
at the effects-backend design session (operator-directed, in-session;
design basis [library/cas/EFFECTS-BACKEND.md](../../library/cas/EFFECTS-BACKEND.md)):
two entries minted — TypeScript backend, program vector — and one rule
ratified — programs-are-content. Amended 2026-08-28 at the
effects-backend RATIFICATION (operator: "make this official and pin
it"; the R1–R14 dialogue is the grilling record): three entries
minted — handler, the tower, representation strata — and one rule
ratified — the-direction-law. Amended 2026-08-28 at the
canonicalization ruling (operator-ratified, in-session; four rulings,
each as recommended: methods are first-class structure values;
completeness instances syntactic-only; duplicate keys refuse at
admission, normalization never repairs; both mints approved): two
entries minted — canonicalization method, form address — and the
"form hash" spelling retired. Kind:
**glossary**. This document owns the context's vocabulary
and nothing else. The design view lives in
[library/effects/IMPLEMENTATION-PLAN.md](../../library/effects/IMPLEMENTATION-PLAN.md);
the user-facing projection of this vocabulary — the two-register split
the CLI renders — is pinned in
[library/effects/VOCABULARY.md](../../library/effects/VOCABULARY.md);
claims are stamped per [CLAIM-GATES.md](../effect-typescript-semantics/CLAIM-GATES.md).

## Scope and independence

This glossary owns the CAS replay library's vocabulary: minted terms and minted
rules for content-addressed storage of operation histories and their
substitution replay. It owns no behavior (the implementation plan), no claim
standing (the gate ladder), and no source pins (Source Provenance).

The context is fully independent of the Entity Store context: no term below
borrows from it, and shared English words are ordinary usage, not borrowed
judgments. The machine algebra
([MACHINE-ALGEBRA.md](../../library/machine/MACHINE-ALGEBRA.md), pre-grade) is
this context's *pattern source* for canonicalization, framing, and the
hash-hypothesis lattice — attribution, not dependency. The ratified relationship
is a deliberate fork of the machine's obligation shapes; convergence to direct
instantiation is expected only after the machine algebra is itself ratified, and
enters as an ordinary refactor proposal at that time.

### Lexical rules

1. No bare "Admissible" or "Admitted" as a minted judgment name. Every admission
   judgment in this context is compound-named and says what is admitted.
2. Orchestration that follows the documented discipline is **conforming**, never
   "admitted" — admission-family words are reserved for checks a machine runs.
3. "Verdict" does not appear in this context; a session has an **outcome**.
4. "Canonical" follows the machine's `canon` pattern and is glossed on first
   use in any surface that uses it.

---

## Terms

### Operation description
- **Kind:** schema. **Code label:** `library/effects/archive/replay-plane/src/replay/Operation.ts`
  (descriptions and the statically checked `describeService`).
- **Form:** stable operation identity, revision, request Schema, success Schema,
  typed-failure Schema, and leaf-replay class for one method of a described
  Effect service.
- **Obligations:** any Schema change is accompanied by a revision bump; a drift
  without a bump is caught at consumption as outcome inadmissibility, never
  silently accepted. Descriptions are explicit; reflection is insufficient.
- **Avoid:** deriving a description from runtime inspection; treating equal
  identities with different revisions as matchable.

### CAS node
- **Kind:** model (carrier). **Code label:** `library/cas/Cas/Node.lean`
  (carrier) and `library/cas/Cas/Codec.lean` (canonical codec); provisional
  `src/cas/Node.ts`.
- **Form:** versioned kind, canonical payload bytes, and ordered typed
  references — the data-plus-references pattern. References live inside the
  framed body as full-length address bytes in declared order.
- **Obligations:** node admission before store; the obligation column maps to
  the machine's O-shapes through the fork's standing correspondence table (an
  M2 deliverable). Identity is the pre-image bytes, never the storage layout.
- **Avoid:** storing un-admitted bytes; letting archive or storage layout
  participate in identity.

### Content identifier
- **Kind:** model (function with premises). **Code label:**
  `library/cas/Cas/Address.lean` (address function and lattice levels) and
  `library/cas/Cas/Separation.lean` (kind/version separation).
- **Form:** digest of the project-owned pre-image
  `versionByte ++ kindTag ++ frame(encode(canon node))`. The hash `H` is
  abstract in the model; the concrete digest is an injected adapter (first:
  SHA-256 via platform crypto). Kind tags are a one-byte plane per scheme
  version; addresses are full digest output, never truncated.
- **Obligations:** the hash-hypothesis lattice. Level 0 (no premise on `H`):
  canon idempotence, framing, kind/version separation, equal-encoding
  deduplication, and collision characterization. Level 1: address equality
  reflects content equality only under an explicit named `hInj` premise.
  Level 2 is empty: no theorem assumes collision resistance. Any
  pre-image-affecting change bumps the scheme version byte.
- **Avoid:** hashing Schema's default JSON encoding; stating an address law
  without its lattice level; "hashing proves identity."

### Node admission
- **Kind:** model (judgment). **Code label:** `library/cas/Cas/Admission.lean`
  (judgment and checked put) with the store carrier in
  `library/cas/Cas/Store.lean`; provisional `src/cas/Store.ts`.
- **Form:** raw node to admitted node or clause-named typed CAS error
  (address mismatch, non-canonical bytes, unknown kind, dangling or wrong-kind
  reference). Closure and kind-typing are checked at `put`; `load` verifies
  address recomputation, canonical decode, and known kind.
- **Obligations:** fail-closed; the readable store is well-formed by
  construction. CAS errors are a distinct typed family from mismatch
  categories.
- **Avoid:** renormalize-on-read (a named defect, same standing as live
  fallback); checking closure only at load; folding CAS errors into the
  mismatch taxonomy.

### History entry
- **Kind:** model (carrier). **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/History.lean`
  (invocation and entry carriers) with the outcome envelope in
  `library/effects/archive/lean-model-0.3/Effects/Replay/Outcome.lean`.
- **Form:** one logical operation occurrence: operation identity and revision,
  canonical request, decision, outcome envelope, and predecessor information.
- **Obligations:** the outcome envelope is channel-preserving two-case data —
  success of the declared success Schema or failure of the declared
  typed-failure Schema — and substitution re-injects through the native Effect
  channels so recovery combinators fire exactly as they did live. Failures are
  Schema-tagged data values; stack traces, host error identity, and cause
  chains are not recorded.
- **Avoid:** recording an outcome as a bare value that erases the channel;
  collapsing defect or interruption into the envelope (they are deferred, not
  merged).

### Occurrence identity
- **Kind:** model (identity discipline). **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Replay/Session.lean` (flat history; position is the occurrence)
  with the distinctness law in `library/effects/archive/lean-model-0.3/Effects/Replay/Laws.lean`.
- **Form:** structural `(executionId, index)`. Under exact positional matching,
  position is the semantics; identity and matching rule coincide.
- **Obligations:** identical invocation content never collapses occurrences —
  the store deduplicates request nodes while history keeps entries distinct.
  Request-content-keyed reuse answering an occurrence is a named defect.
- **Avoid:** content-derived occurrence identifiers; nonce machinery before
  frames or migration demand it.

### Replay session
- **Kind:** model (state machine). **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Replay/Session.lean` (state carrier) with the total reducer in
  `library/effects/archive/lean-model-0.3/Effects/Replay/Reducer.lean` and the derived relation in
  `library/effects/archive/lean-model-0.3/Effects/Replay/Relation.lean`; provisional `library/effects/archive/replay-plane/src/replay/Session.ts`,
  `library/effects/archive/replay-plane/src/replay/Reducer.ts`, and `library/effects/archive/replay-plane/src/replay/Replay.ts`.
- **Form:** mode (record or replay), execution identity, history root, flat
  cursor, pending delegation slot, ordered decision trace, and terminal
  abort state. Well-formedness keeps the cursor inside the history, pins it
  to the history length in record mode, and keeps the pending slot empty in
  replay mode.
- **Obligations:** a record-mode append failure aborts the session through
  the defect-class transport seam — the failure is in no wrapped method's
  error channel, so orchestration cannot catch it, no later wrapped
  operation runs, and it surfaces as the session's typed store error.
  Histories are therefore truthful prefixes, never gapped subsequences,
  structurally rather than by a mutable poisoned flag (a wrapped method's
  error union cannot widen without breaking caller-facing type identity, so
  the flag-guarded alternative is unrepresentable). Replay mode is hermetic:
  no live service exists in its environment, and tripwire Clock/Random
  defaults surface ambient use as a `Violated` outcome (mechanism verified
  against the pinned source, 2026-08-26: both are `Context.Reference` keys
  overridable per scope with `Effect.provideService`).
- **Avoid:** recording past an append failure; giving a replay session a live
  dependency; "poisoned flag" phrasing — the abort is structural.

### Solicited delegation
- **Kind:** model (protocol). **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/Session.lean`
  (`pending` slot) with the guarding steps in `library/effects/archive/lean-model-0.3/Effects/Replay/Reducer.lean`;
  provisional `library/effects/archive/replay-plane/src/replay/Reducer.ts`.
- **Form:** record-mode delegation is exclusive and paired — an invoke
  registers the outstanding invocation in the session's pending slot, the
  live outcome appends only by naming that registered invocation, and the
  append clears the slot.
- **Obligations:** a second invoke while one is outstanding rejects as
  delegation outstanding; a recorded outcome without or beside its
  registered invocation rejects as unsolicited; lawful record runs
  therefore append in invocation order.
- **Avoid:** treating the slot as a concurrency queue — one outstanding
  delegation is the ruled protocol, and sound concurrent recording is a
  designed post-alpha milestone, never an incremental widening.

### Decision trace
- **Kind:** model (observable). **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Replay/Decision.lean`; provisional `library/effects/archive/replay-plane/src/replay/Decision.ts`.
- **Form:** the ordered decisions emitted by the pure reducer. Minimum cases:
  live delegation, record-mode occurrence append, recorded substitution,
  history consumption, typed rejection, completion.
- **Obligations:** the primary observation of the differential suite; "was a
  live adapter requested" is a derived projection of the trace, never a
  separate oracle.
- **Avoid:** comparators that drop live-delegation or rejection decisions.

### Mismatch category
- **Kind:** taxonomy. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/Decision.lean`
  (`MismatchCategory`).
- **Form:** eight categories. Request-side, checked against the entry at the
  cursor: operation mismatch, revision mismatch, request mismatch, history
  exhausted. Record-side, checked against the pending delegation slot:
  delegation outstanding, unsolicited outcome. Completion-side: unconsumed
  suffix. Outcome-side, checked at consumption: outcome inadmissible.
- **Obligations:** request-side compatibility and outcome-side admissibility
  are distinct checks with distinct categories; the set is caller-visible API.
- **Avoid:** an "order mismatch" category (it always manifests as a
  request-side case at the current position); folding CAS storage failures in
  (distinct typed family); folding ambient violations in (a session-outcome
  case, not a category).

### Session outcome
- **Kind:** model (tagged result). **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Replay/Session.lean` (`SessionOutcome`); completion checked
  uniformly by the reducer in `library/effects/archive/lean-model-0.3/Effects/Replay/Reducer.lean`.
- **Form:** `Completed` with the terminal; `Rejected` with category, position,
  and — for the unconsumed-suffix case only — the program's terminal so far; or
  `Violated` with the ambient-service violation.
- **Obligations:** completion means the program reached a terminal (success or
  declared typed failure) *and* the cursor equals the history length, uniformly
  across both terminal kinds. Transport from wrapped methods to the session
  boundary is a named defect-class seam with its own trust statement:
  caller-facing method types stay byte-identical across live, record, and
  replay, and the internal defect is plumbing, never modeled defect semantics.
- **Avoid:** "verdict"; widening wrapped-method error unions with replay
  errors; presenting the transport defect as modeled defect behavior.

### Replay witness
- **Kind:** schema. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/Witness.lean`
  (immutable carrier); `library/effects/archive/replay-plane/src/storage.ts` (`StoredWitness`,
  internal: consumed count plus history root — the ratified selected
  representation; entries stay recoverable through the root chain).
- **Form:** mode, execution identity, consumed history, decision trace, and
  session outcome, immutable.
- **Obligations:** carries execution identity, never program identity;
  compatibility is behavioral — emitted stream against recorded stream — never
  nominal.
- **Avoid:** any field or prose implying "this is the program that recorded
  it" or "the code is unchanged"; reading a witness as evidence the external
  world would answer the same today.

### Reified program
- **Kind:** model (carrier). **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/Program.lean`;
  interpreted in `library/effects/archive/lean-model-0.3/Effects/Replay/Interp.lean`.
- **Form:** a closed, terminating sequential program over invocation
  leaves: a returned value, the program's own typed failure, or an
  invocation whose continuation receives the recorded outcome envelope.
- **Obligations:** the continuation receives both envelope channels, so
  recovery fires exactly as it did live and re-raising is the
  continuation's choice; a leaf interprets as one reducer step, and
  sequential composition interprets as a monad morphism into the
  interpretation carrier. Continuations are meta-level and
  model-internal; the serializable first-order descriptor with a
  defunctionalized continuation machine is a later, separately admitted
  lane.
- **Avoid:** serializing a continuation, or reading a history as a
  checkpoint of one — a captured continuation is not a value snapshot;
  presenting reified-program theorems as universal over ordinary
  TypeScript orchestration (the G2 quantifier gap).

### Interpretation halt
- **Kind:** taxonomy. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Replay/Interp.lean`
  (`Halt`).
- **Form:** why an interpretation stopped short of a value: the program's
  own typed failure; the session's typed rejection at a position; or
  absorbed — a leaf reached under an already-aborted session.
- **Obligations:** every halt carries the session state it stopped at —
  the cursor neither resets nor forks across composition; the taxonomy
  mirrors what the session boundary observes and never widens a wrapped
  method's error union; absorbed is a totality case, not a behavior —
  the interpreter split never starts a program on an aborted session,
  and the reachable leaf results are pinned by theorem.
- **Avoid:** folding halt cases into a wrapped method's error type;
  reading absorbed as reachable behavior.

### Value descriptor
- **Kind:** module. **Code label:** `src/cas/Value.ts`.
- **Form:** declared kind tag and revision, a service-free value Schema,
  and the declared canonical encoding of the Schema's Encoded form;
  `put` admits one leaf node with no references, `get` loads, verifies
  the expected kind, and decodes.
- **Obligations:** identity and revision are explicit — a Schema change
  bumps the revision, and drift is caught at read as a typed projection
  failure; payload bytes come from the declared canonical encoding,
  never a default JSON carrying a canonicality claim; this slice is
  leaf-only.
- **Avoid:** deriving graph partitioning from Schema AST shape;
  `PrimaryKey` as a content identifier; reading equal roots as value
  equality beyond the hash-hypothesis lattice.

### Typed root
- **Kind:** schema. **Code label:** `src/cas/Value.ts` (runtime) and
  `library/cas/Cas/Refs.lean` (model carrier `Root α`).
- **Form:** a branded content identifier carrying the descriptor's
  phantom value type and expected kind tag; assignable wherever a
  content identifier is; constructed by `put`. Its edge form is an
  ordinary typed reference (expected tag plus address) — exactly what
  node admission checks — so typed edges need no projection-side
  machinery. In the model, dereference is total over closed stores
  (`Root.closed_deref`).
- **Obligations:** the phantom never bypasses runtime kind validation —
  every load re-checks the kind; a root is data, never proof of
  presence: a dangling root fails closed at load. Reads require only
  the store loader, never the writer.
- **Avoid:** phantom-only trust; treating a root as a replay-compared
  identity before the session dependency-manifest extension exists.

### Projection codec failure
- **Kind:** taxonomy. **Code label:** `src/cas/Value.ts`.
- **Form:** one typed error family for descriptor encode and decode
  failures, carrying the direction, the content identifier where known,
  and the issue; distinct from the CAS error family and the mismatch
  taxonomy.
- **Obligations:** projection codec failures are never folded into the
  store's failure clause and never silently renormalized.
- **Avoid:** folding into the CAS family; retry-with-renormalize.

### Hydrated service layer
- **Kind:** module. **Code label:** `src/cas/Service.ts`.
- **Form:** a fixed-root service construction over a value descriptor:
  `layer(root)` builds the public service eagerly; `layerAs(tag, root)`
  builds the same shape under another key — the record-construction seam
  targets the kit's internal live role.
- **Obligations:** eager hydration by default so caller-facing method
  types stay unchanged; construction errors stay on the layer channel;
  live authorities stay visible in `R` and outside the content root; the
  wrapper never resolves its public tag and double wrapping stays
  rejected.
- **Avoid:** lazy per-method acquisition that hides errors; a hidden
  service root read as replay identity.

### Remote exchange event
- **Kind:** taxonomy. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Remote/Event.lean`.
- **Form:** the abstract server-event alphabet the remote client
  machine consumes: ok with declared length and bytes; absent;
  truncated; reset; silence; unauthenticated; denied; rate-limited
  with retry-after; capacity; redirected; integrity mismatch (a
  server-side integrity rejection — neither absence nor transport);
  per-key batch results; capabilities with limits; and declared
  interruption.
- **Obligations:** absence and corruption never share a member; every
  event is data carrying no wall-clock or host detail; the alphabet is
  the model's entire view of the wire.
- **Avoid:** HTTP vocabulary in members; folding integrity failures
  into transport members; events carrying credentials.

### Wire command
- **Kind:** taxonomy. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Remote/Command.lean`.
- **Form:** what the machine emits toward the shell: capability probe,
  load, find-missing, upload, query-committed, publish-root.
- **Obligations:** commands are data and the shell owns their transport
  realization; command sequences are part of the compared conformance
  surface alongside decisions.
- **Avoid:** commands carrying credentials or ambient state; a command
  whose meaning depends on transport origin.

### Fault schedule
- **Kind:** schema. **Code label:** the schedule-vector rows emitted by
  `library/effects/archive/lean-model-0.3/Effects/Conformance/ManifestRemote.lean`.
- **Form:** identifier-tagged operations, scripted server events each
  correlated to the operation they answer (declared interruption
  included), and an explicit interleaving sequence referencing every
  operation and event exactly once — complete accounting by
  construction; executed by the model to compute the row's
  expectations.
- **Obligations:** schedules are fixture data under the
  generated-vectors law; retry delays and attempt counts are decision
  data, never wall-clock; any randomness derives from a row-carried
  seed or is excluded by the declared normalization.
- **Avoid:** recorded transcripts as schedules; wall-clock in any
  field; schedules that embed server internals beyond the alphabet.

### Remote client machine
- **Kind:** model (state machine). **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Remote/Machine.lean` with the laws in
  `library/effects/archive/lean-model-0.3/Effects/Remote/Laws.lean`.
- **Form:** sans-io: state and one input in; a result, wire commands,
  and decisions out, commands and decisions identifier-tagged.
  Operations carry client-assigned identifiers with an in-flight map,
  so unrelated operations proceed concurrently and every wire event
  correlates to one operation — never an ambient fiber identity. The
  Effect shell owns all I/O; state carriers prefer the Lean standard
  library's structures.
- **Obligations:** total on the alphabet; every invariant is stated
  over its decisions and commands; the machine never models the
  server, HTTP, TLS, or time.
- **Avoid:** I/O or services inside the machine; modeling server
  behavior beyond the alphabet; treating shell behavior as
  model-covered.

### Streamed transfer service
- **Kind:** module. **Code label:** `src/cas/Transfer.ts`
  (`CasTransfer`), provided with the store by `Cas.layerRemote`
  (`src/Cas.ts`).
- **Form:** streamed upload and download mechanics above the logical
  store: `putStream` checks or computes the address incrementally and
  succeeds only after complete consumption and remote commitment; a
  public download stream emits early only when each chunk is
  independently content-addressed or carries a valid Merkle proof —
  under a whole-object hash, complete verification precedes any
  trusted byte, through a scoped temporary spool where needed.
- **Obligations:** `CasStore.load` still returns whole admitted nodes,
  never a partially received stream; upload retry requires a
  restartable or replayable source — a one-shot stream is never
  transparently retried; explicit encoded, decoded, decompressed, and
  queued-byte limits are enforced — backpressure is not a budget.
- **Avoid:** collapsing transfer mechanics into the logical store;
  releasing unverified bytes early; retrying one-shot sources.

### Event notification service
- **Kind:** module. **Code label:** pending R2+ (provisional
  `src/cas/Events.ts`, `CasEvents`).
- **Form:** advisory notification and progress streams (server-sent
  events, WebSocket) beside the data planes — HTTP and gRPC remain
  the primary CAS data planes.
- **Obligations:** notification delivery never constitutes CAS
  admission; the channels stay advisory unless acknowledgement,
  deduplication, replay, and resumption are defined above them
  (server-sent-event cursors are not exactly-once).
- **Avoid:** admitting on a notification; treating an event stream as
  a data plane.

### Remote transport
- **Kind:** module (adapter-internal). **Code label:**
  `src/internal/remoteTransport.ts` (`RemoteCasTransport`), realized
  for the declared `cas-http/0` profile by
  `src/internal/remoteHttp.ts`; never a `Context` service key.
- **Form:** the raw untrusted protocol streams behind the verified
  semantic adapter: one command executed at a time, responses mapped
  into the exchange alphabet before the semantic core sees them.
- **Obligations:** never a `CasStore`; raw chunks stay untrusted here;
  retries and redirects are decided by the semantic core, never the
  shell; `Scope` owns connections, response bodies, temporary spools,
  subscriptions, and cancellation.
- **Avoid:** exposing transport streams as store results; invisible
  shell-level retry or redirect-following; credentials crossing
  redirect hosts.

### Chunk tree
- **Kind:** model concept. **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Merkle/Chunk.lean` and `library/effects/archive/lean-model-0.3/Effects/Merkle/Tree.lean`
  (TypeScript pending the Merkle implementation slice).
- **Form:** chunking under a DECLARED recipe (a positive chunk size)
  is a lossless partition — rejoining restores the bytes, and the
  checked inverse accepts exactly the lists chunking produces. The
  tree root over the chunk list uses structural pre-images — a leaf
  carries its absolute index and bytes, a parent carries two child
  addresses — under the abstract address function, split at the
  largest power of two strictly below the count (the shared
  RFC 9162 / BLAKE3 split).
- **Obligations:** one root per recipe and content; domain
  separation and position binding are constructor-level at the model
  altitude — byte prefixes belong to the codec layer with exactness
  proofs; collision cases surface as explicit witnesses, never
  assumptions.
- **Avoid:** inferring a recipe from data; minting identity from a
  chunk list or encoding bytes; assuming the address function
  injective.

### Inclusion opening
- **Kind:** model concept. **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Merkle/Verify.lean`.
- **Form:** an index, a count, leaf bytes, a root-side-first sibling
  list, and an expected root. The verifier DERIVES the combination
  sides from the index and the count, so an adversary controls
  sibling values only — the discipline that makes binding provable.
- **Obligations:** reflection — the executable check accepts exactly
  the recomputation judgment; completeness — honest paths verify
  with no hypotheses beyond the index bound; binding — two accepted
  openings of one root and index agree or a computable collision
  walk exhibits two distinct pre-images with one address; position
  binding — accepted bytes equal the committed chunk at that index
  or a collision is exhibited.
- **Avoid:** side-carrying proof formats (adversary-chosen sides
  admit an injective-hash counterexample); reading more into
  acceptance than the stated judgment.

### Verified-streaming decoder
- **Kind:** machine. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Merkle/Decoder.lean`
  with its laws in `library/effects/archive/lean-model-0.3/Effects/Merkle/Laws.lean`.
- **Form:** a sans-io frame-stack machine over parsed nodes — parent
  pairs, chunks, and explicit skip tokens. The stack holds expected
  subtree addresses; consumption is pre-order, so verification order
  equals read order with no seeking; a slice range makes
  out-of-range subtrees skippable, their addresses already bound by
  their parents.
- **Obligations:** emission IS the verification branch, and against
  a committed list every emission matches or a collision witness
  exists in the consumed prefix — the decoder is not obliged to
  detect the collision; the length validates exactly at the final
  chunk; runs compose over input concatenation, which is what makes
  transport fragmentation semantically irrelevant; a completed
  full-range decode determines its root with no collision disjunct;
  slices agree with the whole decode filtered to the range.
- **Avoid:** exposing length or end-of-input before the final chunk
  validates; treating a skip token as verified content; any logic on
  wire chunk boundaries.

### Encoding-malleability boundary
- **Kind:** rule. **Code label:** standing review (the
  transport-never-identity row) with the model documentation.
- **Form:** slice and encoding bytes are transport carriers, never
  identities: distinct encodings may decode to one output under one
  root — trailing garbage, skipped parents — and this is documented,
  not fought. Only roots and decoded bytes are identity-bearing.
- **Obligations:** canonicality laws apply to NODE encodings, never
  to proof or slice carriers; the only valid way to learn anything
  about an encoding's content is to decode it.
- **Avoid:** byte-comparing encodings as an equality shortcut;
  minting identity from a proof carrier; extending the node codec's
  canonicality discipline to slices.

### Consistency proof
- **Kind:** judgment with executable verifier. **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Merkle/Consistency.lean`.
- **Form:** the RFC 9162 subproof shape over the standards split: a
  bare hash list relating the root of the first m chunks to the root
  of all n, consumed linearly down one spine — one sibling per level
  plus a terminal — with the WHOLE walk derived from the two sizes,
  so an adversary controls hash values only, never the shape. The
  anchored flag tracks whether the old tree is still a left spine of
  the new one; the mathematical heart is the shared split point:
  past the split, prefix and whole trees split at the same power of
  two.
- **Obligations:** the executable verifier accepts exactly the
  judgment (reflection); honestly generated proofs relate the
  committed prefix root to the whole root; an accepted proof against
  an honest new tree forces the old root to BE the committed
  prefix's root or exhibits a computable collision — never a
  collision-resistance axiom.
- **Avoid:** side-carrying or shape-carrying proof formats; equal
  sizes needing a proof (root equality is definitional there); a
  verifier consulting anything beyond the sizes, the roots, and the
  hash list.

### Proof documents
- **Kind:** codecs. **Code label:** `library/effects/archive/lean-model-0.3/Effects/Merkle/ProofCodec.lean`
  over the shared field tools in `library/cas/Cas/Nat32.lean`.
- **Form:** byte realizations for the proof plane under the
  control-codec discipline. The opening document: index, count,
  length-prefixed leaf, sibling addresses root-side first — sides
  never encoded. The range-stream document: a twelve-byte echoed
  header, then items whose alphabet IS the verified-streaming
  decoder's input language — a bare skip tag (a skipped subtree's
  address was bound by its parent; carrying one would be a side
  channel), a length-prefixed chunk, a parent's two child addresses.
- **Obligations:** decoders are closed and exact — a successful
  decode's input is exactly the canonical encoding of its result;
  unknown tags and truncated items reject; the framings are
  self-delimiting, so a boundary truncation reads as a DIFFERENT
  document whose wrong content the verifier then rejects — transport
  length-delimits, verification decides.
- **Avoid:** JSON on the proof plane; a skip carrying a hash;
  treating prefix-decodability as a codec defect to be fought
  instead of a documented property the verifier backstops.

### Blob node graph
- **Kind:** refinement tie. **Code label:**
  `library/effects/archive/lean-model-0.3/Effects/Merkle/Blob.lean`.
- **Form:** a blob is a node graph, not a second store: leaves are
  ordinary nodes carrying index-prefixed chunk bytes, parents are
  ordinary two-reference nodes, and the Merkle root IS the address
  of the materialized root node — an ordinary content identifier.
  One declared blob kind tag serves both shapes because the
  pre-image carrier's parent holds child addresses only; the
  leaf/parent separation is STRUCTURAL (nonempty payload and no
  references versus empty payload and exactly two), turned into
  byte-level separation by codec non-malleability.
- **Obligations:** negotiation, closure-gated publish, and pull
  apply to blobs verbatim through the ordinary reference closure; a
  bounded pre-image collision under the instantiated address
  function transfers to a byte-level hash collision, keeping every
  Merkle collision disjunct meaningful; materialized nodes are
  byte-bound well-formed under the profile chunk bound; the chunk
  recipe is a profile constant, never a capability.
- **Avoid:** a parallel blob identity kind or storage plane;
  threshold-based silent chunking; server-declared chunk sizes;
  references smuggled through payloads where the closure machinery
  cannot see them.

### Service kit
- **Kind:** module. **Code label:** `library/effects/archive/replay-plane/src/replay/ServiceAdapter.ts`.
- **Form:** one kit constructor per described service, minting an internal live
  role tag and returning the record construction (requires the live role and
  the replay service) and the replay construction (requires the replay service
  only). A by-value overload builds on it.
- **Obligations:** wrapper bodies never resolve the public tag — a named defect
  with a must-fail fixture. Produced services carry a runtime string-keyed
  brand checked at construction; double wrapping is rejected with a typed
  error, never normalized.
- **Avoid:** type-level brands (ruled out by caller-facing type identity);
  reflection-derived wrapping.

### Conforming orchestration
- **Kind:** taxonomy (discipline class). **Code label:** none — a documented
  discipline, not a machine-checked judgment.
- **Form:** orchestration whose replay-relevant leaves are wrapped and which
  performs no ambient host effect and consults no default Clock, Random, or
  jittered Schedule except through a described leaf operation.
- **Obligations:** `R = never` is never treated as evidence of purity; the two
  leak counterexamples (direct `Date.now`; jittered retry through default
  services) are permanent fixtures; G2 traceability states the quantifier
  mismatch between Lean-reified programs and discipline-conforming TypeScript.
- **Avoid:** "admitted orchestration"; presenting model theorems as universal
  over ordinary TypeScript programs.

---

### Canonical schema
- **Kind:** schema. **Code label:** `src/cas/CanonicalSchema.ts` (runtime)
  and `library/cas/Cas/Schema/` (model: `Ast`, `El`, codec, `Described`,
  `SelfCodec`).
- **Form:** the plane's universe of codes: a first-class data value
  (`Null/Boolean/Integer/String/Literal/Array/Struct/Ref`) whose
  denotation is a type (`El`), whose generic codec carries the proved
  forward, exactness, and injectivity laws, and which is itself content:
  a code projects to a tagged JSON value, wraps in the revisioned
  schema-node envelope (kind tag `0x53`), and its canonical payload
  bytes are its identity — byte-pinned across runtimes
  (`lake exe schemas --check`, `CanonicalSchemaPin.test.ts`).
- **Obligations:** no canonical construct's identity lives in a
  function (the plane's standing law); struct fields strictly sorted
  (`WF`) — the only admissible spelling is the canonical one, and the
  encode image is proved canonically spelled (`encode_canonical`,
  `renderCompact_encode`); the self-projection is a proved round trip
  (`ofJson_toJson`), so one code per payload value; bytes are ALWAYS
  derived on read, never stored as authority.
- **Avoid:** Effect Schema (or any runtime carrier) read as the
  authority — carriers carry, the code is the identity; JSON Schema as
  anything but an export projection; extending the universe by
  convention (optional-as-struct, union-as-tag-string) instead of by a
  new ratified constructor.

### Materializer
- **Kind:** codec. **Code label:** `src/cas/CanonicalSchema.ts`
  (`fromAst` — the generative direction) and
  `library/cas/Cas/Schema/Described/`, `Deriving/`, `Notation.lean`
  (`Described`, `deriving Described`, `cas_struct`).
- **Form:** the generative direction of a described code: from a
  canonical schema, produce the fully typed runtime carrier it denotes
  (TS: `fromAst` compiles a code to its Effect Schema with the code
  attached by annotation; Lean: a `Described` instance pairs a native
  structure with its code and the two-sided equivalence, and the
  `cas_struct` notation mints structure, instance, and raw-schema
  surface from one declaration).
- **Obligations:** a materialized carrier always carries its source
  code (annotation on the TS side, the `Described.code` field on the
  Lean side) so identity is recoverable from the carrier; the
  carrier–code correspondence is two-sided with inverse laws
  (`ofEl_toEl`/`toEl_ofEl`), never a one-way projection; materializing
  never mints identity — the code is prior, and equal codes
  materialize interchangeable carriers.
- **Avoid:** hand-written carriers for described trees (the
  three-trees discipline: every described tree type arrives as `El` of
  a code); a materialized carrier drifting from its code without the
  byte pin going red; reading "materializer" as a persistence or view
  concept borrowed from event-sourcing systems — here it is strictly
  schema-to-carrier.

### TypeScript backend
- **Kind:** module. **Code label:** `library/cas/Cas/Backend/` (Lean,
  seeded by `Cas/Schema/Foreign.lean`) with generated surfaces landing
  in `library/effects`.
- **Form:** the store language's first compilation target: four layers —
  denotation (the language), target semantics (the pinned Effect surface
  as typed data), a closed TypeScript syntax fragment grown only with a
  real consumer, and rendering under the Substance/Denotation/Style
  split with `Style` as digested content. Design basis:
  [EFFECTS-BACKEND.md](../../library/cas/EFFECTS-BACKEND.md).
- **Obligations:** the backend generates hosts — interpreters, services,
  layers, typed surfaces — never the authoritative home of a program
  (rule: programs-are-content); generated output is deterministic,
  byte-identity-gated, provenance-stamped, and parse-back-checked by an
  independent admitted instrument; the target-semantics layer is pinned
  to the exact Effect version and drift is a red gate, not a silent
  regeneration.
- **Avoid:** string-template codegen; full-TypeScript AST ambition;
  external formatters on output; semantic choices inside the generator;
  self-comparison as verification.

### Program vector
- **Kind:** schema. **Code label:** owed with backend slice 2 (the
  conformance-vector registry is the pattern source).
- **Form:** a conformance vector whose content is a run: one store
  program, executed by the Lean interpreter and by a generated target
  host, each writing its word — the vector pins the program's
  presentation and the Lean-computed word, and the gate asserts the
  target host's word is identical, binding for binding.
- **Obligations:** word equality is the whole claim — byte-decidable
  because nondeterminism enters only as recorded content; a program
  vector never asserts semantic equivalence of programs (that is a
  certificate, never an identity); the replayed word passes the same
  admission gates as any word.
- **Avoid:** reading a green program vector as a theorem about the
  target runtime; comparing programs by anything other than
  presentation identity; vectors whose runs depend on unrecorded host
  state.

### Handler
- **Kind:** model. **Code label:** `library/cas/Cas/Lang/Handler.lean`.
- **Form:** one meaning per operation in a target monad; `interpret`
  is the induced monad morphism (`interpret_bind` proved once for
  every handler); handlers compose across signature sums
  (`Handler.sum`). The REFERENCE HANDLER — the admission judgment in
  `StateT Word (Except Refusal)` — is the store language's meaning;
  replay is the handler answering from a recorded word; the Effect
  adapter and every transport are handlers or handler compositions.
- **Obligations:** meaning lives only in the reference handler; a
  realization is claimed against it by the word observation, never by
  review; fuel belongs to the small-step presentation, never to the
  API.
- **Avoid:** reading any adapter as the semantics; comparing
  realizations by anything but the word; handler-specific behavior
  leaking into program identity.

### The tower
- **Kind:** model. **Code label:** `library/cas/Cas/Lang/Tower.lean`.
- **Form:** a service is a handler, and a handler may itself be a
  program over a lower signature; `Handler.through` composes and
  `interpret_through` (proved) collapses the strata. `ByteSig` mirrors
  the runtime's byte-plane seam; `casOverBytes` is the store service
  implemented in the language — admission re-derived at the seam,
  collision as byte disagreement, loads through the proved frame
  parser.
- **Obligations:** strata are free by theorem; trust exists only at
  the admitted seams at the bottom; every seam's own effects
  (transport failure, cancellation, backpressure) enter as operations
  of their own summed signature.
- **Avoid:** smuggling seam effects through request/reply commands;
  treating Effect Layers as anything other than the runtime image of
  `through`; a stratum claiming meaning.

### Representation strata
- **Kind:** model. **Code label:**
  `library/cas/Cas/Lang/Representation.lean`.
- **Form:** the four literal Lean representations of effectful
  computation and their equalities: (1) first-order content —
  decidable, hashable, addressable; the metaprogrammatic stratum; (2)
  `Prog` — the proof carrier, a proved `LawfulMonad`, INITIAL
  (`eq_of_forall_interpret`: agreement under every lawful
  interpretation is structural equality); (3) handler images —
  equated only by theorem (`SemEq`, `ObsEq`); (4) host IO — no
  equational theory. The stable effects API is strata 1–2.
- **Obligations:** metaprogramming reasons over stratum 1 only;
  proofs induct at stratum 2 under the named equations; stratum-3
  equalities are certificates; stratum 4 stops at trust statements.
- **Avoid:** claiming `DecidableEq` on `Prog`; positing any program
  equality finer than structural (initiality forbids it); equating
  handler images by inspection.

## Rules (each kind: adr; ratified in the M0 grilling, 2026-08-26)

### the-direction-law
Ratified 2026-08-28 (operator, in-session, the effects-backend
ratification). Three verbs, three directions, never crossed. HOOVER —
parsing pinned sources with admitted instruments — is ingestion: it
yields surface tables, cross-checks, and provenance, and never mints
an identity. EXECUTE — running the Lean model — is the only act that
mints fixtures, words, and payloads: model execution is strictly
stronger evidence than parsing a description of the model. MATERIALIZE
— generation — flows denotation → code only, byte-gated; a carrier is
never the authority, and generation never runs code → denotation. A
parse never mints a fixture.

### programs-are-content
Ratified 2026-08-28 (operator, in-session, the effects-backend design
session). Programs are content; hosts are code. A program lives in the
store and is loaded by address; generated target code materializes
interpreters, services, and surfaces around it. A generated static
projection of a program carries the address of the term it projects,
and parity between them is a digest check — the served-equals-derived
wall. Generated code that becomes a program's authoritative home is a
defect of the backend, not a style choice.

### history-is-an-underapproximation
Every recorded entry corresponds to a live action that occurred, in the
recorded order; the converse is never claimed. **Why:** the live-action/append
crash gap is unclosable from inside the library; the structural session abort
keeps histories prefix-truthful, and replaying a short prefix fail-closes on
its own (history exhausted). **Avoid:** exactly-once language; treating a
witness as proof of external completeness.

### no-live-fallback
A replay mismatch is terminal for the attempt; nothing falls through to a live
adapter. Replay-mode construction makes this structural: the live service is
absent from the environment, so fallback is unexpressible rather than merely
forbidden. **Avoid:** retry-with-live "resilience" inside replay mode;
capturing a live reference before replay construction.

### behavioral-compatibility-only
Replay compatibility compares emitted request streams against recorded
streams; program identity is absent, not inferred. Pure refactors replay old
histories; changed programs fail lazily at first divergence, harmlessly,
because replay performs no external effects. **Why:** program identity cannot
be retrofitted onto arbitrary TypeScript closures; it returns, if ever, as a
content-addressed reified program in a generator lane. **Avoid:** witness
wording that names a program; "replay passed, so the code is unchanged."

### reject-first-ambient-policy
The first slice rejects time, randomness, and jittered scheduling from
conforming orchestration rather than adjudicating per-combinator determinism.
Replay-mode tripwire defaults convert the Effect-mediated leak into a
`Violated` outcome; the raw-host channel stays discipline plus permanent
fixtures; deterministic overrides arrive only when a fixture demands one.
**Why:** the boundary between sequence-deterministic and
sequence-nondeterministic schedule use is subtle enough that drawing it is
later work; declining all of it is honest. **Avoid:** treating `R = never` as
purity; adjudicating individual combinators ad hoc.

### Byte-plane seam
- **Kind:** schema (service seam). **Code label:** `src/cas/Backend.ts`.
- **Form:** three capability services over one grow-only byte plane —
  the byte reader (bytes at an address, advisory presence), the byte
  writer (join one admitted node), and the root store (grow and list
  the published-roots registry). Each plane is a join-semilattice:
  re-insertion of identical bytes is the identity, publication grows a
  monotone set.
- **Obligations:** grow-only monotonicity — nothing removed, nothing
  replaced — is what makes check-then-insert admission sound without a
  lock. Backends stay dumb: admission and verification are laws above
  the seam, so a backend cannot weaken the store. Read-only is the
  absence of the writer capability, checked at compile time.
- **Avoid:** verification inside a backend; a backend that retracts;
  read-only expressed as a runtime refusal.

### Path reader
- **Kind:** schema (backend). **Code label:** `src/cas/PathReader.ts`.
- **Form:** the byte reader realized over one caller-supplied read
  capability: store-root-relative path in, optional bytes out — absence
  answers none; only a host that cannot answer fails, typed.
- **Obligations:** reads exactly the store-root layout the file backend
  writes, so publishing a store is committing a directory. The host is
  untrusted by construction: the load law re-verifies every byte, so a
  hostile or corrupt host is a typed refusal, never wrong data.
- **Avoid:** minting per-forge URL schemes into the library; conflating
  host failure with absence.

### Store-root layout
- **Kind:** rule. **Code label:** `src/cas/Backend.ts` (the relative
  path functions) and `src/cas/FileBackend.ts` (the writer of record).
- **Form:** `objects/<2 hex>/<62 hex>` holds canonical bytes — the
  address is the path — and `roots/<64 hex>` empty files, where
  presence is the publication.
- **Obligations:** shared verbatim by every path-shaped backend; writes
  publish by temp-file-then-rename so readers never observe a half
  object; no index or manifest lives beside the tree.
- **Avoid:** layout participating in identity; auxiliary index files;
  fan-out depth as a tunable.

### Typed-reference marker law
- **Kind:** rule (CAS-005). **Code label:** `src/internal/refMarkers.ts`
  (runtime walks) and `library/cas/Cas/Refs.lean` (model, guard-executed).
- **Form:** a value's typed references are positional markers: the k-th
  marker in canonical byte order carries index k into the node's
  reference array — indexes forced, sharing by repeated entries, and
  the reserved key refused outside the exact marker shape, at encode
  and at decode.
- **Obligations:** assignment and scan walk one canonical order
  (codepoint-sorted keys at every depth); collisions refuse, never
  escape — an escape would give one user value two spellings and split
  its content identity. The coherence law (scan of a lowering reads
  `0…n-1`) is guard-executed over the model fixtures; its general
  induction is a named follow-up.
- **Avoid:** escaping collisions; dedup laws over shared targets;
  assigning marker indexes in declaration order.

### Store loader
- **Kind:** schema. **Code label:** `src/cas/Store.ts` (`CasLoader`).
- **Form:** the load-only law as its own service — load and re-verify a
  node, requiring only the byte reader. Every store composition
  provides it beside the full store; a read-only composition provides
  it alone.
- **Obligations:** every typed read (value projections, graph walks)
  requires only the loader, so typed values decode over read-only
  hosts with no writer anywhere in the composition.
- **Avoid:** widening a read to require the full store; a loader that
  skips re-verification.

### Server plane
- **Kind:** schema. **Code label:** `src/Server.ts` with
  `src/server/Protocol.ts` (wire law as data), `src/server/Core.ts`
  (semantic core), and `src/server/HttpApp.ts` (the four-step shell).
- **Form:** the closed cas-http/0 request algebra, refusal vocabulary,
  and outcome vocabulary as tagged sums; one pure total wire law from
  gathered facts to a refusal or an authenticated decoded operation;
  the semantic core interpreting requests over the byte-plane seams —
  the same seams an embedded store stands on.
- **Obligations:** serve is total — every conclusion is a member of the
  closed outcome vocabulary, a backend that cannot answer included,
  mapped to the capacity class and never to an admission verdict. A new
  wire plane is new constructors and new table rows, never a reshaped
  pipeline.
- **Avoid:** transport knowledge in the core; opinions in the shell;
  rendering that consults policy instead of the outcome.

### Canonicalization method
- **Kind:** model. **Code label:**
  `library/cas/Cas/Core/Canonicalize.lean` (`Canonicalizer`, the
  induced quotient, the ladder) and
  `library/cas/Cas/Core/Canonicalize/Json.lean` (`canonJson`, the
  key-sorting instance).
- **Form:** an idempotent normalizer held as first-class data — one
  carrier admits many methods. A method induces a decidable
  equivalence (same representative) with its setoid form space;
  methods compare by refinement and compose under the
  ladder-coherence premise, with idempotence, preservation, and
  refinement inherited by the composite rather than re-proved.
- **Obligations:** idempotence is the admission bar; every further
  claim a method carries is a named preservation law against a named
  observation, with admissibility (equivalent values are
  observation-equal) the proved consequence. Completeness is
  instantiated only against decidable syntactic observations, only by
  proof — for semantic observations it is the permanently open bound:
  identity hashes presentations, never denotations. A method is
  normalize-side machinery (the acquisition loop's normalize verb):
  it reorders spellings and repairs nothing — duplicate keys and
  every other ambiguity remain admission refusals.
- **Avoid:** a typeclass-style "the" canonicalizer for a carrier;
  renormalize-on-read; a normalizer that dedups, drops, or otherwise
  repairs content; claiming completeness for a handler-image or word
  observation.

### Form address
- **Kind:** model (function with premises). **Code label:**
  `library/cas/Cas/Core/Canonicalize.lean`
  (`Canonicalizer.formAddress`).
- **Form:** the address of a value's canonical representative under a
  named method — the observed-form identity of the construct-ledger
  lane, defined over the abstract `H` exactly like every address.
- **Obligations:** the hash-hypothesis lattice, inherited: Level 0 —
  form addresses are well-defined on the method's quotient, and equal
  form addresses yield equivalence or an explicit collision witness
  on the representatives; Level 1 — reflection only under the named
  `hInj` premise. A recorded form address names the method that
  minted it, and the canonical encoder of record computes it — never
  a hoover-side instrument.
- **Avoid:** "form hash" (retired spelling); reading form-address
  equality as semantic equivalence; a form address whose method is
  unrecorded.
