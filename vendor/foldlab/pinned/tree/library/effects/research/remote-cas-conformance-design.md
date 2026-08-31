# Remote CAS conformance — design synthesis

Status: conception-mode design, 2026-08-27. G0/G1 hypotheses and
recommendations only; nothing here is promoted, no obligation is
minted, and no ratified rule changes. This is the coordinator's
first-hand synthesis over the four-sweep
[prior-art compendium](remote-cas-prior-art-compendium.md) and the
service-derivation survey's remote sections, written so the future
**remote Pass A** is a ratify-or-amend session rather than a blank
page. Every design element below traces to compendium findings; the
compendium's provenance standing (Part I pinned, Parts II–IV
pending-pin) applies transitively.

## The design question

The conformance workflow proved out because its tested seams are pure
data: a reducer, a codec, an admission function. A production remote
`CasStore` is effectful — network, retries, batches, auth, redirects,
interruption — and the question is how model-generated conformance
extends to it without faking coverage and without surrendering the
generated-vectors law.

## Architecture: three commitments

**A1 — the adapter core is sans-io.** The remote client is factored
into a pure decision machine — state and an incoming abstract event in;
wire commands, decisions, and outcomes out — with the Effect shell
(HttpClient, scopes, credentials, real sockets) owning all I/O. This is
the sans-io pattern the compendium's Part IV grounds (h11/hyper-h2;
git's own pure-protocol test tier), and it is the single move that
makes everything else follow: once the seam is made data, the existing
workflow — schemas, sentences, kits, manifests, mutants, the ledger —
applies to the remote component unchanged.

**A2 — the Lean model speaks an abstract exchange alphabet, never
HTTP.** Model events are of the kind: `ok(bytes)`, `absent`,
`truncated`, `reset`, `silence`, `unauthenticated`, `denied`,
`rateLimited(retryAfter)`, `capacity`, `redirected`,
`batchResult(perKeyStatus list)`, `capabilities(limits)`. The alphabet
is the model-side rendering of the taxonomy that every surveyed system
converged on (compendium convergence 4; Part I implication 9; Part III
implication 12): integrity, absence, transport, authorization in two
flavors, capacity, protocol-limit — with absence and corruption never
sharing a clause. HTTP syntax, TLS, header casing, connection pooling,
and redirect mechanics stay TypeScript-side obligations in the CTX
style; a Lean statement claiming them would fake coverage (the
workflow's own exclusion rationale).

**A3 — the fake-remote's schedule is fixture data inside the manifest
row.** A remote-family row has the shape

    { input:  { ops: [...], schedule: [...] },
      expect: { wireCommands: [...], decisions: [...], outcome: ... } }

where `schedule` is the ordered list of scripted server events (drawn
from the A2 alphabet, including declared interruption points), and the
expectations are computed by EXECUTING the Lean client machine against
the schedule. Prior art proves every piece separately — BoringSSL's
scripted misbehaving peer, git's one-shot mid-conversation fault
scripts, Smithy's model-carried vectors, RFC 8448's pinned transcripts
— but no surveyed project generates wire-level expectations by
executing a mechanized model. **This combination is novel ground**, and
therefore the manifest shape itself is a remote Pass A ratification
item, not something the lane may assume.

## The client-invariant catalog (candidate obligations)

Working labels only — identifiers are minted at the remote Pass A
through plan section 7, never here. Family fits are proposals; the two
rows marked NEW SHAPE are expected to force a WGR-2 catalog event,
which the workflow's stop conditions anticipate.

| Working label | Statement sketch | Proposed fit | Grounding |
| --- | --- | --- | --- |
| verify-on-receipt | Every remote-loaded node is admitted through the standard admission pipeline before caching or return; wire-supplied digests are routing hints and never identities | existing admission + TRACE-EXCLUDES (no admit-before-verify decision) | convergence 1; Part I impl. 1, 13 |
| size-budget-first | Declared sizes and counts are checked against declared budgets before any hashing or decoding | FAIL-CLOSED | Part I impl. 2; Part II impl. (hints-until-proven) |
| batch-accounting | A batch response accounts for every requested key with a per-key status; an unaccounted or misaligned key fails the batch closed with no cross-key substitution | FAIL-CLOSED + DISTINCTNESS-adjacent | Part I impl. 4; REAPI per-item status |
| integrity-terminal | An integrity failure (wrong bytes for address) is terminal for those bytes: no retry with unchanged content, ever | TRACE-EXCLUDES (no retry decision after integrity rejection) | Part I impl. 5; REAPI no-retry rule |
| duplicate-success | An already-present exact-digest upload resolves as success, never as an error and never as a second transfer | EXACT-STEP (wire-request count) | Part I impl. 5; REAPI early-termination |
| presence-advisory | No admission or publication decision is taken on a presence answer alone; presence may only skip work whose truth a later step re-establishes; absence is never negatively cached by default | TRACE-EXCLUDES + review rule | convergence 2; Part III impl. 2, 3 |
| resume-authoritative | Interrupted transfers resume only from a server-reported committed offset, re-queried, tolerating regression | FAIL-CLOSED over the resume step | Part I impl. 6 |
| closure-client-side | Children upload before parents and the root publishes last; server acceptance of a parent never implies closure | TRACE-EXCLUDES (no root-publish decision before closure) | convergence 3; Part I impl. 7 |
| interruption-clean | After an interruption at any schedule point, no partial node is admitted, no root is published, and resources are closed; the possibly-published set is exactly what upload order permits | FAIL-CLOSED + the crash-consistency analog | Part IV (ShardStore persistence); survey obligations |
| capability-probe | Server-declared limits are discovered at layer acquisition and honored by splitting or rerouting, never exceeded by construction | tsSide | Part I impl. 10 |
| retry-policy-trace | Retries are bounded, per-layer configured, server-informed where offered, and visible as decisions; no wire attempt for a non-idempotent operation is ever repeated | TRACE-EXCLUDES + EXACT-STEP | Part I impl. 12; Part III impl. 4, 5 |
| redirect-verification | Verification and credential scope are independent of transport origin; credentials never cross redirect hosts | tsSide + TRACE-EXCLUDES | Part I impl. 11 |
| namespace-scoped-presence | Presence-style operations carry a namespace; no global existence query exists on the surface | review rule + tsSide | convergence on the oracle; Part III impl. 13 |
| control-state-fail-closed | Batch framing, capability documents, and presence indexes parse fail-closed with the same posture as node bytes | FAIL-CLOSED | Part III impl. 11 (S3 2008) |
| remote-load-refinement | A successful remote load implements the logical admitted-node load | **NEW SHAPE** (refinement judgment) | survey obligation; Part IV family-fit analysis |
| cache-observation | A local admitted-node hit is observationally equivalent to a successful remote load for immutable nodes | **NEW SHAPE** (observation judgment) | survey obligation; Part IV family-fit analysis |

## The testing architecture: four lanes

**Lane 1 — schedule vectors (the conformance lane proper).** The Lean
client machine executes against schedule fixtures; per-family manifests
carry the rows; the TypeScript sans-io core consumes rows verbatim and
compares wire commands, decisions, and outcomes structurally.
Determinism follows the replay precedent exactly: tripwire services and
disabled tracer timing in the shell, retry/backoff rendered as decision
data (attempt numbers and chosen delays computed by the model, with
any jitter derived from a row-carried seed or excluded by the declared
normalization).

**Lane 2 — declared mutants, both directions.** Direction 1: a mutated
client model must move at least one ratified schedule's outputs.
Direction 2: a mutated TypeScript core must go red on ratified vectors.
The starter catalog writes itself from the invariants, one per
falsification case: cache-before-admission,
retry-non-idempotent-upload, accept-truncated-batch,
accept-permuted-batch, negative-cache-not-found,
renormalize-remote-response, publish-root-before-closure,
resume-from-local-offset — with wrong-bytes-for-address as the
canonical fault every family exercises.

**Lane 3 — property/state-machine evidence.** Generated, seeded,
shrinking operation sequences run the TypeScript adapter-over-
fake-remote against the in-memory store as the reference model — which
the estate already maintains as both model and mock, the ShardStore
lesson about why reference models stay alive. Flips rows only through
the declared-evidence mechanic, G4-labeled, never proof.

**Lane 4 — live-server evidence.** An OCI-conformance-shaped suite
against a real backend: env-configured endpoint, optional ordered
workflows, semantic HTTP-level assertions (the REAPI warning: never
workload-level pass/fail), reports with redacted transcripts.
Evidence, never contract; declared-evidence flips only. Recorded
transcripts from this lane are inputs the conformance lane may
transcribe into Lean fixtures — never fixtures themselves (the VCR
prohibition, already latent in the generated-vectors law).

**Regression discipline (all lanes):** every remote-adapter defect
ever found becomes a permanent named schedule vector tied to its
obligation — the etcd pattern, and the workflow's survivor rule already
points there.

## Staged slices (the R ladder — enters plan section 7 at the Pass A)

- **R1 — alphabet and machine.** Mint the exchange alphabet and the
  Lean client decision machine; ratify the schedule-vector manifest
  shape (the novel-ground item); first obligations: verify-on-receipt,
  size-budget-first, integrity-terminal.
- **R2 — single-op baseline.** Load and put over the fake-remote
  (schedules of length one to two); ContentNotFound alignment;
  duplicate-success; the TypeScript sans-io core and thin shell.
- **R3 — batching and closure.** find-missing, per-key accounting,
  children-first upload, root-last publication, interruption-clean
  schedules.
- **R4 — policy.** Capability probe, retry-policy traces, resume,
  redirects, namespace scoping.
- **R5 — property lane.** Lane 3 harness and its declared-evidence
  flips.
- **R6 — live lane and a real backend.** One HttpClient-backed store
  layer under scoped acquisition (the survey's design), the live
  suite, and the plan section 4 Scope-row amendment that slice already
  owes.

## Scope guards — deferred by name

Whole-node addressing stands; chunking enters as declared identity or
not at all, and the BLAKE3/bao fork is the named decision if a
large-payload kind ever arrives. RBSR-style set reconciliation is the
future anti-entropy transport shape — fetch plans, never evidence —
and is not in the R ladder. Hash agility posture is recorded as the
Git model (one function per admitted store; migration by explicit
mapping outside content identity; staged interop) and is not
scheduled. Mutable heads stay in their own compare-and-set service,
outside reconciliation and outside this design. Session dependency
manifests (replay observing fixed service roots) remain parked
exactly as the survey ruled. The Lean model never models HTTP, TLS,
wall-clock time, or server internals — the client machine and its
alphabet are the entire modeled surface.

## The remote Pass A docket skeleton

When the operator opens the remote Pass A, the docket is: (1) the
exchange alphabet as minted vocabulary; (2) the schedule-vector
manifest shape (novel ground — grill hardest here); (3) the candidate
obligation table above entering plan section 7 with real identifiers;
(4) the WGR-2 catalog event for the two new statement shapes;
(5) the four-lane evidence architecture with its flip mechanics;
(6) the mutant floor per falsification case; (7) the R-ladder
sequencing; (8) provenance promotion — which compendium sources get
byte receipts (Part I bytes are already preserved for minting).

## Source standing

Synthesis over the compendium (its provenance standing applies) and
the in-tree service-derivation survey and Xet note. No new sources.
No claim here exceeds G1, and every soundness-adjacent word above is a
design intention, not a judgment.
