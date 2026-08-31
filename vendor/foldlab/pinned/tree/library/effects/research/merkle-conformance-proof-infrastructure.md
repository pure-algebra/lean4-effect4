# Merkle-structure conformance and proof infrastructure

Status: design preparation (G0), 2026-08-27, operator-directed: prepare
the conformance side to rigorously implement conformance and proof
infrastructure for Merkle structures, utilizing existing prior art for
proof verification. Sources are the streaming-sync receipt's pins
(`.reference/provenance/receipts/streaming-sync-cas-api-prior-art.json`),
worked through first-hand where they carry the load: the bao
verified-streaming specification read whole at its blob-verified pin
(`.reference/clones/bao/docs/spec.md`, blob `e06a2389...` = the
receipt's), and RFC 9162's Merkle definitions and verification
algorithms extracted from the pinned edition. Nothing here is ratified;
the closing docket lists every decision with a recommendation, and the
obligations are plan-section-7 candidates only.

## 1. Why this, why now

Three ratified hooks already point at this infrastructure:

- The R1-acceptance streaming rule: a public download stream emits
  early ONLY when each chunk is independently content-addressed or
  carries a valid Merkle proof. The proof infrastructure is the
  mathematical substrate of `CasTransfer` early emission and of the
  streaming survey's proposed `CasBlob`.
- The five streaming obligation candidates (fragmentation invariance,
  terminal completion before admission, interruption exclusion, budget
  enforcement, per-operation stream isolation) all reappear inside a
  verified-streaming decoder — this design gives several of them their
  natural carrier.
- The estate already owns half the ground: the CAS node graph IS a
  Merkle DAG (references sit in the digest pre-image; closure is a
  store judgment), domain separation in the pre-image is a ratified
  convergence, session histories and witnesses are hash chains (the
  future consistency-proof consumers), and the hash-lattice discipline
  (Level 0 abstract, Level 1 with explicit `hInj`, collision cases as
  explicit witnesses, never axioms) is exactly the posture the
  literature's mechanizations struggle toward.

## 2. The structures, as a scope ladder

- **S1 — chunk tree over a blob** (bao/BLAKE3 shape; XET's
  chunk/shard layout is the same family): leaves are chunks with
  position binding, parents combine child roots; the whole-content
  root is the blob identity under a DECLARED chunking recipe. This is
  `CasBlob` identity.
- **S2 — inclusion proofs and verified-slice decoding** (RFC 9162
  `PATH`; bao's slice format is the streaming-ordered equivalent —
  pre-order parents plus the in-range chunks, verification order
  equal to read order, no seeking). This is early emission.
- **S3 — consistency proofs** (RFC 9162 `SUBPROOF`) for append-only
  hash-chained structures: session histories, witness chains, any
  future event log. Second slice.
- **S4 — the Merkle DAG itself**: already modeled (admission,
  closure); this design adds documentation framing only, no new
  machinery.

## 3. What the worked sources fix

### 3.1 bao (read whole at the pin)

The specification's decoder section is a ready-made obligation list:

1. **Emission soundness** — "any output byte returned by the decoder
   matches the corresponding input byte from the original input."
2. **The final-chunk requirement** — the length is validated when and
   only when the final chunk validates, and the decoder must not
   expose the length (through reads, EOF, or seeks) before that. A
   temporal exclusion over the decoder's run — the same shape as the
   remote machine's trace laws.
3. **No decoding collisions** — a complete decode to EOF under root
   `r` of output `o` forces `r` to be the hash of `o`; two roots
   cannot both completely decode the same output.
4. **Malleability is a declared NON-guarantee** — distinct encodings
   (trailing garbage, skipped parents) may decode to one output. The
   boundary matters for the estate: canonicality laws apply to NODE
   encodings, never to proof or slice carriers; only the root and the
   decoded bytes are identity-bearing. Comparing encodings
   byte-for-byte is a documented defect pattern.
5. **An admitted incomplete argument** — the spec concedes (issue 41)
   that the tree-geometry argument for length tweaks is incomplete
   where growing or shrinking the tree preserves the right-edge parent
   count, and leans on the chunk counter. Position binding — a chunk
   verified at index `i` never verifies at `j ≠ i` — is therefore a
   theorem target the informal source could not close. Exactly where
   mechanization earns its keep.

### 3.2 RFC 9162 (pinned edition)

Standards-track declarative recursions and imperative verifiers:

- `MTH({}) = HASH()`, `MTH({d}) = HASH(0x00 || d)`,
  `MTH(D_n) = HASH(0x01 || MTH(D[0:k]) || MTH(D[k:n]))` with `k` the
  largest power of two below `n`; leaf/interior domain separation
  stated as required for second-preimage resistance.
- `PATH` (inclusion) and `SUBPROOF` (consistency) as recursions, plus
  bit-shifting verification algorithms over `(fn, sn)` index pairs,
  and the proof-size bound `ceil(log2(n)) + 1`.

The pair "declarative relation + executable verifier" is precisely the
estate's checker-reflection discipline (`check x = true ↔ Prop x`),
and the verification algorithms give the executable side verbatim.

### 3.3 The remaining pins, in one line each

Merkle's CRYPTO 1987 paper is the foundational citation; EverParse is
already the codec-taxonomy authority for the byte layer; XET, LBFS,
and FastCDC fix that chunking recipes are DECLARED PARAMETERS of an
identity, never identities themselves; RFC 6920 and RFC 9530 confirm
wire-carried digests are hints, never identity (already law as
RMT-001); proofs-of-ownership (CCS 2011) and message-locked encryption
(EUROCRYPT 2013) mark the security boundary of dedup-by-hash
(knowing a hash is not possessing content — a gloss for the presence
semantics of RMT-005, noted, not modeled); Abadi–Lamport and
Lynch–Vaandrager remain the refinement backdrop the transport survey
already adopted.

## 4. The Lean model architecture

New subtree `Effects/Merkle/` mirroring the layout discipline (one
concept per file):

- `Tree.lean` — the chunk tree over an ABSTRACT hash
  `H : Pre → Addr`, where `Pre` is a structural pre-image datatype:
  `leaf (index : Nat) (bytes : Bytes) | parent (left right : Addr)`.
  Domain separation and position binding are STRUCTURAL at the model
  altitude (constructor identity and the index field), so theorems
  never depend on prefix-byte encodings; the byte realization
  (0x00/0x01 prefixes, counters) lives in the codec layer with
  forward-correctness and exactness proofs, exactly like the node
  codec.
- `Proofs.lean` — declarative `Mth`, `Path`, `Subproof` relations
  mirroring RFC 9162's recursions, over the structural pre-image.
- `Verify.lean` — executable `verifyInclusion` / `verifyConsistency`
  mirroring the RFC's algorithms, each with its reflection iff.
- `Decoder.lean` — the verified-streaming decoder as a SANS-IO
  machine, the house pattern: state = expected root, declared length
  candidate, traversal position; inputs = parsed encoding nodes
  (parent pairs or chunks) arriving from an untrusted stream; outputs
  = verified chunk emissions and one terminal length validation.
  Temporal laws quantify over runs, like the remote machine's.
- `Laws.lean` — the obligations below.

Collision posture everywhere: the CONSTRUCTIVE disjunct. Statements
have the form "the good property holds, OR a hash collision is
exhibited" (two distinct pre-images with one digest, extractable from
the offending run) — the M2 ideal-or-collision-witness pattern.
Rows that need injectivity state Level 1 with an explicit `hInj`
hypothesis; no collision-resistance axiom exists anywhere.

## 5. Candidate obligations (enter plan §7 first, MRK family)

| ID | Obligation | Source | Family fit |
| --- | --- | --- | --- |
| MRK-001 | One root per (declared recipe, content): the chunk-tree root is a function of the recipe parameters and the bytes, and recipe parameters are declared, never inferred | XET/FastCDC/bao | CODEC / EXACT-STEP |
| MRK-002 | Decoder emission soundness: every emitted byte equals the committed byte at its offset, or a collision witness exists in the consumed prefix — the decoder is NOT obliged to detect or halt at a collision (LambdaAuth's mechanization-found correction) | bao guarantee 1 + LambdaAuth | TRACE-EXCLUDES over the decoder run + the disjunct |
| MRK-003 | Final-chunk-before-length: no run exposes length or EOF (read, seek, or empty-encoding) before the final chunk validates against the root | bao's final chunk requirement | TRACE-EXCLUDES (temporal) |
| MRK-004 | No decoding collisions: a complete decode to EOF under root `r` forces `r` to be the root of the output, or exhibits a collision | bao guarantee 3 | Level-1 row (`hInj`) or witness disjunct |
| MRK-005 | Slice–whole agreement: decoding a slice for a range agrees with the whole decode restricted to that range | bao slice format | AGREEMENT (relational) |
| MRK-006 | Inclusion verifier reflection: `verifyInclusion` accepts exactly the `Path`-related (leaf, index, root) triples | RFC 9162 2.1.3 | Reflected iff (+ soundness disjunct) |
| MRK-007 | Consistency verifier reflection + append-only corollary: `verifyConsistency` accepts exactly `Subproof`-related root pairs, and consistency forces prefix agreement or a collision witness | RFC 9162 2.1.4 | Reflected iff + corollary theorem |
| MRK-008 | Decoder fragmentation invariance: wire chunk boundaries of the encoding stream never change any emission, rejection, or terminal | ratified streaming candidate | TRACE-EXCLUDES / EXACT-STEP |
| MRK-009 | Chunking is transport, never identity: no operation mints an identity from a slice or encoding byte-form; only roots and decoded bytes are identity-bearing (encoding malleability is documented, not fought) | bao malleability discussion | standing review rule + negative fixtures |
| MRK-010 | Position binding: a chunk validating at index `i` never validates at `j ≠ i` under the same root, or a collision is exhibited | bao issue 41 (informally incomplete!) | Level-1 row; the mechanization target the source admits it lacks |

Proof-size bounds (`ceil(log2 n) + 1`) enter as lemmas, not
obligations. Vector families (schedule-style, generated by executing
the model per the generated-vectors law): tree-build vectors,
inclusion accept/reject vectors, slice-decode vectors with hostile
mutations (tweaked length, swapped siblings, reordered chunks,
trailing garbage — the last expecting ACCEPTANCE, per MRK-009's
boundary), consistency vectors. All over the declared toy digest on
structural pre-images, like the remote families; real-hash
realization stays implementation-side.

## 6. Mechanized prior art for proof verification

### 6.1 veri-auth — the anchor (operator-flagged, examined first-hand)

`jtassarotti/veri-auth` at commit
`24c41ec37e5f12f75a40b00c65b787dea63810b0` (MIT; study clone at
`.reference/clones/veri-auth`): the Rocq + Iris development
accompanying *Logical Relations for Formally Verified Authenticated
Data Structures* (Gregersen, Agarwal, Tassarotti; CCS 2025
submission), mechanizing Bob Atkey's **Authentikit**
(authenticated-data-structures-as-a-library) design. Facts verified in
the clone (README, PAPER.md mapping, sources):

- **The prover / ideal / verifier triad.** One generic authenticated
  computation is interpreted three ways: an ideal semantics (the
  spec), a prover producing proof streams, and a verifier consuming
  them. Security is a binary logical-relations refinement of the
  verifier against the ideal (`refines_adequacy`); correctness is the
  prover against the ideal. Every statement in this design maps onto
  that triad at conformance altitude: the ideal is the Lean model
  judgment, the verifier is the executable checker, and the
  security/correctness pair is a relational AGREEMENT instance plus
  the reflection iff — shapes the estate already ratified.
- **Collision handling is exactly the ratified discipline, at
  scale.** The development derives a "collision-free separation
  logic" from a generic **up-to-bad** program logic whose bad event
  is hash collision; the hash resource law is literally named
  `hashed_inj_or_coll` (hashed values are injective OR a collision is
  derivable), and the end-to-end adequacy (`heap_adequacy_strong`)
  discharges to: the property holds unless a collision occurred. No
  collision-resistance axiom anywhere. This is the strongest
  demonstrated precedent for K3's constructive-disjunct posture — the
  estate's `ideal-or-collision-witness` pattern is the first-order
  shallow analogue of their resource law.
- **An optimization ladder, each rung re-proved.** Naive proof
  streams, list-reverse, proof buffering, heterogeneous caching, and
  a stateful variant each carry their own security AND correctness
  proofs against the same interface. The lesson for the estate: proof
  -object codec optimizations (buffering, dedup, compression) are
  verified refinements with per-rung obligations, never transparent
  rewrites — the rule future proof-codec slices inherit.
- **Merkle retrieve is the flagship example**
  (`merkle.v`, `merkle_retrieve_security.v` /
  `_correctness.v`) — the exact structure S2 targets.

Utilization verdict: **technique prior art, restate-and-reprove in
Lean** (the Rocq-annex rule; the development could additionally be
admitted to the annex to be RUN during technique extraction, an
optional step K8 prices). What transfers is the statement
architecture — the triad, the security/correctness split, the
collision-event discipline, the per-optimization re-proof rule — not
the Iris machinery: the estate's conformance models are pure machines
and first-order theorems, where the up-to-bad logic collapses to the
constructive disjunct already in use. What deliberately does NOT
transfer at this slice: Authentikit's full genericity (authenticated
computation over arbitrary functors). K1 scopes concrete chunk trees
and proofs first; if the estate later generalizes to a generic
authenticated-computation layer, veri-auth is the named reference
shape for that grill.

### 6.2 The bounded sweep — load-bearing sources and absences

A bounded sweep of Lean-native, Isabelle/AFP, Rocq, Agda, Dafny, and
EasyCrypt mechanizations returned (citations pending-pin; receipts
mint at promotion, per the compendium precedent):

- **VCVio Merkle trees** (`Verified-zkEVM/VCVio` @ `76071037…`,
  Apache-2.0, **toolchain-identical Lean v4.33.1**, Mathlib-based;
  sorry-free in every inspected file): inductive and vector Merkle
  trees with functional completeness, **binding as a computable
  collision extractor** — a total `findCollision` returning the
  colliding pair, with its soundness lemma; no injectivity
  assumption, no probability — plus batch openings, uniqueness, and
  an `Addressed/` subtree mechanizing POSITION-DEPENDENT node hashing
  (the discipline BLAKE3's chunk counters and bao's issue-41 caveat
  require, with address-tagged collision witnesses). The
  probabilistic random-oracle layer sits strictly above an unchanged
  structural kernel — exactly the estate's Level-0/Level-1 split.
  Verdict: **restate-in-Lean, primary source** — the binding kernel
  uses little beyond indexed trees and vectors, so a Std-first port
  is bounded; adoption as a dependency would require accepting
  Mathlib, which the package's ratified posture refuses.
- **LambdaAuth** (AFP; Brun & Traytel, ITP 2019 — the receipt's named
  prior, first mechanization of Miller et al.'s λ•): opaque
  `typedecl hash`, no collision-resistance axiom, and the security
  theorem literally a disjunction — "everything worked out as
  planned, or a hash collision has occurred" — six years of precedent
  for K3. Two mechanization-found corrections to the original paper,
  one of which SHAPES OUR STATEMENTS: **the verifier cannot recognize
  that a collision occurred and may keep consuming proof-stream
  elements** — so streaming obligations must read "every emitted byte
  is correct, or a collision witness exists in the consumed prefix,"
  never "verification halts at the collision." Verdict: restate the
  statement discipline; the Nominal2 language machinery stays behind.
- **ADS_Functor** (AFP; Lochbihler & Marić, FMBC 2020): Merkle
  functors closed under sums, products, and least fixpoints, with a
  merge/blinding-order semilattice algebra for inclusion proofs
  ("reveals less" as the order, merge respecting hashes). The right
  COMPOSITIONAL skeleton for inclusion proofs over the estate's
  existing Merkle-DAG store judgment. Its posture is blanket
  injectivity ("we assume no hash collisions occur") — Level 1 done
  wholesale, which the estate isolates per-obligation instead.
  Verdict: restate the five interface laws over the abstract address
  function.
- **aaosl-agda** (Oracle, CPP 2021; UPL-1.0, archived): the ONLY
  mechanized consistency-style corpus — authenticated append-only
  skip lists with `AgreeOnCommon` already in disjunct form ("agree on
  every common index, or there is a hash collision") and a minimal
  "injectivity-modulo-collisions in data arguments" hypothesis — the
  template for S3 over the estate's hash-chained histories.
- **deposit-sc-dafny** (ConsenSys/Cassez, FM 2021): total correctness
  of incremental Merkle-root maintenance against the recursive spec —
  the algorithmic skeleton for maintaining and verifying roots while
  streaming leaves; proof decomposition (left/right path invariants)
  transfers.
- Cautionary datapoints: Toychain assumed injective hashing at CPP
  2018 and REMOVED it later at the cost of rewriting major proofs —
  the argument for Level-0-first ordering; FVIntmax axiomatizes
  computational infeasibility — the posture the estate forbids.
  hacl-star's F* Merkle tree (incremental, functionally correct, no
  binding claims, no license file) and risc0-lean4 (the earliest
  Lean-4 collision-extractor shape, unfinished, sorries) are
  pattern-only.

**Absence results (searched routes named in the sweep): no proof
assistant has mechanized bao/BLAKE3 verified streaming, and none has
mechanized RFC 9162's inclusion or consistency verification
algorithms.** The S1+S2 slice is therefore greenfield: a Lean
mechanization of the verified-streaming decoder and the RFC-shaped
verifiers would be both reusable and novel, with
`transparency-dev/merkle`'s Go reference test data available as an
independent cross-check source for the model-generated vectors.
Mathlib, Std, and Reservoir carry no Merkle content; AFP holds
exactly the two entries above.

Estate rules that bound any utilization: techniques from non-Lean
provers are restated and reproved in the estate's own judgment (the
Rocq-annex rule generalizes); Lean-native work may be adopted as a
dependency only through the ordinary admission path (TOOLS/Source
Lock), and the effects package's Std-first, Mathlib-free posture is a
ratified constraint any candidate dependency must answer to.

## 7. What this is not

- No TypeScript work is proposed here; `CasBlob`/`CasTransfer`
  consumption of verified chunks is a later implementation slice that
  CONSUMES the ratified families this design mints.
- No real hash function enters the model; BLAKE3/SHA-256 realization
  and their official test vectors are implementation-lane evidence.
- No wire protocol is designed; proof-object codecs get the same
  treatment as the node codec when their slice arrives.
- Set-reconciliation structures (rsync, cpisync, IBLT — pinned in the
  receipt) are OUT of this design; they are sync-planning machinery
  for a later `CasSync` conception, not authenticated structures.

## 8. Decision docket

| # | Decision | Recommendation |
| --- | --- | --- |
| K1 | First-slice scope | S1 + S2 (chunk tree, inclusion proofs, the verified-streaming decoder with MRK-001..006, 008..010); S3 consistency (MRK-007) as the second slice; S4 documentation only. |
| K2 | Model altitude | Abstract `H` over a STRUCTURAL pre-image datatype (constructor-level domain separation, index-field position binding); byte realization with exactness proofs at the codec layer, like the node codec. |
| K3 | Collision posture | Constructive collision-witness disjuncts everywhere; Level-1 `hInj` rows only where the statement needs injectivity; no collision-resistance axiom. |
| K4 | Decoder form | Sans-io machine with temporal trace laws — the house pattern shared with the remote machine, so the eventual TypeScript mirror and harness lanes need no new discipline. |
| K5 | Schema families | Reuse CODEC, TRACE-EXCLUDES, AGREEMENT, EXACT-STEP, Reflected; mint a new family ONLY if the soundness-with-witness disjunct resists composition from Reflected plus existing shapes — that question goes to the grill as a named WGR-2 stop condition, not a silent mint. |
| K6 | Vectors | Toy digest over structural pre-images, model-executed families (tree/inclusion/slice/consistency, hostile mutations included, malleability-acceptance included); real hashes implementation-side. |
| K7 | Sequencing | A dedicated conformance slice (MRK-1) lands BEFORE any CasBlob implementation work — conformance leads; relative order against R3 is the operator's call (the two are independent; R3 unblocks sync, MRK-1 unblocks streaming/blob). |
| K8 | Mechanized-prior utilization | Restate-and-reprove, source by source: VCVio's binding kernel and Addressed position-binding (the primary Lean-shaped source; Mathlib bars adoption under the package's ratified posture); LambdaAuth's statement discipline including the keeps-consuming correction; ADS_Functor's merge/blinding algebra for compositional inclusion proofs; aaosl-agda's consistency template for S3; deposit-sc-dafny's incremental-root skeleton; veri-auth per 6.1 (optional annex admission if running it aids extraction). The Go reference's test data cross-checks model-generated vectors. The absence results make S1+S2 greenfield — a publication-relevant novelty to be claimed only after the verifier passes, per the estate's splash discipline. |
| K9 | Statement architecture | Adopt the prover/ideal/verifier triad at conformance altitude: the Lean model judgment is the ideal, executable verifiers carry reflection iffs, security lands as relational AGREEMENT instances with the collision disjunct, correctness as the completeness half — and every future proof-stream optimization is a verified refinement re-proving both halves, never a transparent rewrite. |
