/-!
# The obligation inventory

The plan's section-7 obligation ledger as typed data — the merge input the
ledger generator joins with the instance registry. Every row here mirrors
one plan row exactly; a new obligation enters the plan first, then this
inventory. SES-002, the reducer well-formedness obligation, was minted at
the M3 slice through exactly that route.
-/

namespace Effects.Conformance

/-- Where an obligation's evidence comes from, and when. -/
inductive Disposition where
  /-- A Lean schema-bundle instance of the named family, expected at the
  named milestone. -/
  | schema (family : String) (milestone : String)
  /-- Discharged by construction of the model carrier (for example,
  determinism of a total function), recorded at the named milestone. -/
  | carrier (milestone : String)
  /-- TypeScript-side evidence: typecheck, layer graph, integration
  fixtures. -/
  | tsSide (milestone : String)
  /-- Differential or conformance evidence across the manifest seam. -/
  | bridge (milestone : String)
  /-- A standing review rule; checked by reading, not by a theorem. -/
  | review
  /-- Deferred to a later extension milestone. -/
  | deferred (target : String)
  deriving Repr

/-- One obligation: its plan identifier, its plan statement (plain prose, no
markup), and its disposition. Instance sentences live on registry entries,
never here — the inventory carries statements, the instances carry the
ratified plain-meaning sentences. -/
structure Obligation where
  id : String
  statement : String
  disposition : Disposition
  deriving Repr

def inventory : List Obligation := [
  { id := "CAS-001"
    statement := "Project-owned canonical node encoding has one byte representation per admitted node."
    disposition := .schema "CODEC" "M2" },
  { id := "CAS-002"
    statement := "Graph admission rejects dangling or wrong-kind references."
    disposition := .schema "REJECTION-CLAUSE" "M2" },
  { id := "CAS-003"
    statement := "Every address law is assigned to hash Level 0 or carries an explicit Level-1 hInj premise; no theorem occupies Level 2."
    disposition := .review },
  { id := "CAS-004"
    statement := "A value's canonical encoding is the UTF-8 bytes of its compact JSON rendering — codepoint-sorted keys, integers only, JSON short-escape strings — one encoding per structure, language-neutral."
    disposition := .tsSide "E3" },
  { id := "RPL-001"
    statement := "Replay is deterministic for a fixed admitted state and request."
    disposition := .carrier "M3" },
  { id := "RPL-002"
    statement := "Replay-mode decision traces never select live delegation, and replay construction has no live-service requirement."
    disposition := .schema "TRACE-EXCLUDES" "M3" },
  { id := "RPL-003"
    statement := "Matching consumes exactly the permitted occurrence."
    disposition := .schema "EXACT-STEP" "M3" },
  { id := "RPL-004"
    statement := "Mismatch fails closed."
    disposition := .schema "FAIL-CLOSED" "M3" },
  { id := "RPL-005"
    statement := "Completion rejects unconsumed suffix entries; the rejection carries the program's terminal so far."
    disposition := .schema "FAIL-CLOSED" "M3" },
  { id := "SES-001"
    statement := "Record-mode append failure aborts the session through the transport seam; histories are truthful prefixes, never gapped subsequences."
    disposition := .schema "TRACE-EXCLUDES" "M3" },
  { id := "SES-002"
    statement := "Every reducer step preserves session-state well-formedness."
    disposition := .schema "WF-PRESERVE" "M3" },
  { id := "SES-003"
    statement := "Record-mode delegation is exclusive and outcome-solicited; unsolicited steps fail closed and lawful record runs append in invocation order."
    disposition := .schema "FAIL-CLOSED" "E3" },
  { id := "CMP-001"
    statement := "Sequential interpretation threads replay state compositionally across success and typed-failure outcomes."
    disposition := .schema "HOMOMORPHISM" "M5" },
  { id := "CMP-002"
    statement := "Identical requests remain separate occurrences."
    disposition := .schema "DISTINCTNESS" "M3" },
  { id := "CMP-003"
    statement := "Transparent and opaque policies have distinct, declared framed traces."
    disposition := .deferred "M7" },
  { id := "CTX-001"
    statement := "Wrapped service construction supplies the same caller-facing interface without recursive lookup."
    disposition := .tsSide "M4" },
  { id := "CTX-002"
    statement := "Conforming orchestration cannot consult default Clock/Random behavior; replay-mode tripwires surface ambient use as a Violated outcome."
    disposition := .tsSide "M4" },
  { id := "ADM-001"
    statement := "G2 traceability distinguishes reified Lean-program quantification from discipline-conforming TypeScript orchestration."
    disposition := .review },
  { id := "BRG-001"
    statement := "Model fixtures and the TypeScript reducer compare one declared normalized decision trace."
    disposition := .bridge "M3" },
  { id := "BRG-002"
    statement := "The pinned Effect integration agrees on the enumerated domain."
    disposition := .bridge "M6" },
  { id := "DUR-001"
    statement := "No exactly-once claim crosses the live-action/history-append crash gap."
    disposition := .review },
  { id := "PRJ-001"
    statement := "Value-descriptor identity is explicit and checked: kind tag and revision are declared, and reading verifies the expected root kind."
    disposition := .tsSide "E2" },
  { id := "PRJ-002"
    statement := "A value round-trips through its descriptor: get after put returns the declared domain canonicalization."
    disposition := .tsSide "E2" },
  { id := "PRJ-003"
    statement := "A payload failing the descriptor's schema is rejected with a typed projection error distinct from the CAS error family and the mismatch taxonomy."
    disposition := .tsSide "E2" },
  { id := "PRJ-004"
    statement := "Fixed-root hydration matches by-value construction: the layer builds the same caller-facing shape, construction errors stay on the layer, and method error unions never widen."
    disposition := .tsSide "E3" },
  { id := "PRJ-005"
    statement := "Hydrated record construction stays non-recursive and single-wrapped: layerAs targets the internal live role only, never resolves the public wrapper, and double wrapping stays rejected."
    disposition := .tsSide "E3" },
  { id := "PRJ-006"
    statement := "Equal roots imply no stronger value equality than the hash-hypothesis lattice permits."
    disposition := .review },
  { id := "RMT-001"
    statement := "No remote-loaded node reaches the cache or the caller without passing standard admission; a wire-supplied digest is a routing hint, never an identity."
    disposition := .schema "TRACE-EXCLUDES" "R1" },
  { id := "RMT-002"
    statement := "Declared sizes and counts are checked against declared budgets before any hashing or decoding."
    disposition := .schema "FAIL-CLOSED" "R1" },
  { id := "RMT-003"
    statement := "An integrity failure is terminal for those bytes: no wire attempt ever repeats unchanged content."
    disposition := .schema "TRACE-EXCLUDES" "R1" },
  { id := "RMT-004"
    statement := "An already-present exact-digest upload resolves as success with zero additional transfer commands."
    disposition := .schema "EXACT-STEP" "R2" },
  { id := "RMT-005"
    statement := "No admission or publication decision is taken on a presence answer alone, and absence is never negatively cached by default."
    disposition := .schema "TRACE-EXCLUDES" "R3" },
  { id := "RMT-006"
    statement := "A batch response accounts for every requested key per-key; an unaccounted or misaligned key fails the batch closed with no cross-key substitution."
    disposition := .schema "FAIL-CLOSED" "R3" },
  { id := "RMT-007"
    statement := "Children upload before parents and the root publishes last; server acceptance of a parent never implies closure."
    disposition := .schema "TRACE-EXCLUDES" "R3" },
  { id := "RMT-008"
    statement := "At any declared interruption point, no partial node is admitted, no root is published, and resources are closed."
    disposition := .schema "FAIL-CLOSED" "R3" },
  { id := "RMT-009"
    statement := "Interrupted transfers resume only from a re-queried, server-reported committed offset, tolerating regression."
    disposition := .schema "FAIL-CLOSED" "R4" },
  { id := "RMT-010"
    statement := "Retries are bounded by declared policy, rendered as decisions, and never repeat a non-idempotent wire attempt."
    disposition := .schema "TRACE-EXCLUDES" "R4" },
  { id := "RMT-011"
    statement := "Server-declared limits are discovered at layer acquisition and honored by splitting or rerouting."
    disposition := .tsSide "R4" },
  { id := "RMT-012"
    statement := "Verification and credential scope are independent of transport origin; credentials never cross redirect hosts."
    disposition := .tsSide "R4" },
  { id := "RMT-013"
    statement := "Presence-style operations carry a namespace; no global existence query exists on the surface."
    disposition := .review },
  { id := "RMT-014"
    statement := "Batch framing, capability documents, and presence indexes parse fail-closed with the same posture as node bytes."
    disposition := .schema "FAIL-CLOSED" "R3" },
  { id := "RMT-015"
    statement := "A successful remote load implements the logical admitted-node load."
    disposition := .schema "AGREEMENT" "R2" },
  { id := "RMT-016"
    statement := "A local admitted-node hit is observationally equivalent to a successful remote load for immutable nodes."
    disposition := .schema "AGREEMENT" "R4" },
  { id := "RMT-017"
    statement := "Attested presence confirms for publish: a key the peer reports present whose bytes the client holds and verifies locally enters the confirmed set; without the presence report or the local verification the attestation is refused, and attestation never admits to the cache."
    disposition := .schema "FAIL-CLOSED" "E3" },
  { id := "SRV-001"
    statement := "The server's semantic core is the interpretation of the model's finite request trees over the storage seam: for every scripted session, the implementation returns the model's outcomes and issues exactly the model's storage events, in order."
    disposition := .tsSide "SRV-1" },
  { id := "MRK-001"
    statement := "One chunk-tree root per declared recipe and content: chunking is a lossless declared partition, and the root is a function of the recipe parameters and the bytes."
    disposition := .schema "CODEC" "MRK-1" },
  { id := "MRK-002"
    statement := "The streaming decoder emits a chunk only after it verifies against its expected subtree address; against a committed chunk list, every emission matches, or a hash-collision witness exists in the consumed prefix."
    disposition := .schema "TRACE-EXCLUDES" "MRK-1" },
  { id := "MRK-003"
    statement := "No decoder run observes the length or end-of-input before the final chunk validates against the root."
    disposition := .schema "TRACE-EXCLUDES" "MRK-1" },
  { id := "MRK-004"
    statement := "A complete decode determines its root: the recomputed root of the emitted output equals the expected root, so no output completely decodes under two roots."
    disposition := .carrier "MRK-1" },
  { id := "MRK-005"
    statement := "Slice decoding agrees with the whole decode restricted to the requested range."
    disposition := .schema "AGREEMENT" "MRK-1" },
  { id := "MRK-006"
    statement := "The inclusion verifier accepts exactly the openings whose recomputed root matches; honestly generated paths verify; and two accepted openings of one root and index with different leaves yield a computable collision."
    disposition := .schema "AGREEMENT" "MRK-1" },
  { id := "MRK-007"
    statement := "The consistency verifier accepts exactly the related root pairs, and consistency forces prefix agreement or exhibits a collision."
    disposition := .schema "AGREEMENT" "MRK-2" },
  { id := "MRK-008"
    statement := "The decoder is a pure fold: runs compose over input concatenation, so transport fragmentation below the parser cannot change any emission, rejection, or terminal."
    disposition := .carrier "MRK-1" },
  { id := "MRK-009"
    statement := "Slice and encoding bytes are transport, never identity: only roots and decoded bytes are identity-bearing, and encoding malleability is documented rather than fought."
    disposition := .review },
  { id := "MRK-010"
    statement := "An accepted opening binds its index's committed chunk: bytes accepted at an index equal the chunk the tree commits at that index, or a collision is exhibited."
    disposition := .carrier "MRK-1" },
  { id := "MRK-011"
    statement := "Inclusion-opening documents parse fail-closed and exactly: sides are never encoded, truncation and malformed fields are rejected, and a successful decode's input is exactly the canonical encoding of its result."
    disposition := .schema "CODEC" "MRK-2" },
  { id := "MRK-012"
    statement := "Range-stream documents parse fail-closed and exactly over the decoder's input alphabet: unknown tags and truncated items are rejected, and a successful decode's input is exactly the canonical encoding of its result."
    disposition := .schema "CODEC" "MRK-2" },
  { id := "MRK-013"
    statement := "Ranged stream generation is complete: for any requested range the honest extractor's stream decodes to its done status and emits exactly the owed ranged emissions."
    disposition := .carrier "MRK-2" },
  { id := "MRK-014"
    statement := "The Merkle address function instantiated as the address of the canonical blob-node encoding makes a blob root an ordinary content identifier, and a bounded pre-image collision transfers to a byte-level hash collision."
    disposition := .carrier "MRK-2" },
  { id := "MRK-015"
    statement := "Byte-level frame parsing is incremental and fragmentation-invariant: all fragmentations of one complete body yield the same parsed inputs and terminal, and truncation never yields completion."
    disposition := .carrier "MRK-3" },
  { id := "MRK-016"
    statement := "Every input trace accepted for a root and range emits exactly the committed bytes at those positions or supplies a collision witness; honest-generator completeness is a separate theorem."
    disposition := .carrier "MRK-3" },
  { id := "MRK-017"
    statement := "Successful byte-range slicing equals the flattened whole restricted to the requested byte window under the declared bounds."
    disposition := .carrier "MRK-3" },
  { id := "MRK-018"
    statement := "A blob manifest commits recipe identity, total bytes, and leaf count; readers select semantics from the recipe id and unknown ids fail closed; changing any identity-affecting recipe parameter changes the manifest id."
    disposition := .schema "CODEC" "MRK-3" },
  { id := "MRK-019"
    statement := "A proof response is exactly one complete decode: trailing content after the machine's done status is rejected at the framer, and responses are bounded by declared output and proof-amplification budgets."
    disposition := .carrier "MRK-3" },
  { id := "MRK-020"
    statement := "A ranged blob read touches exactly the proof-necessary nodes: the manifest, the parents on intersecting paths, the intersecting leaves, and their chunk data — never a node outside the range's spine."
    disposition := .tsSide "E3" },
  { id := "SRV-001"
    statement := "A successful root-head transition implies the manifest and selected closure were admitted at that transition under its compare-and-set precondition, and no failed transition changes the visible head; crash survival is a distinct adapter property."
    disposition := .carrier "S-M1" },
  { id := "SRV-002"
    statement := "Server admission runs bounded receive, closed decode, address recomputation, and reference checks before write-if-absent, and loads revalidate bytes before crossing the semantic seam."
    disposition := .carrier "S-M1" },
  { id := "SRV-003"
    statement := "Write-if-absent distinguishes stored, already-present-identical, and same-address-different-bytes; the third is an integrity fault that fails, is observable, and blocks publication."
    disposition := .tsSide "S-M2" },
  { id := "SRV-004"
    statement := "Served capabilities are the intersection of implementation, principal policy, store properties, registry properties, and configured limits; a served capability never exceeds an enforced one."
    disposition := .carrier "S-M1" },
  { id := "SRV-005"
    statement := "Adapters declare a durability class and success claims never exceed the declaration; the memory adapter is volatile, and crash-persistent claims carry platform-pinned write, rename, and flush evidence."
    disposition := .tsSide "S-M2" },
  { id := "SRV-006"
    statement := "Root heads move only by compare-and-set; concurrent publishers serialize; stale expectations fail with the standard precondition semantics."
    disposition := .carrier "S-M2" }
]

end Effects.Conformance
