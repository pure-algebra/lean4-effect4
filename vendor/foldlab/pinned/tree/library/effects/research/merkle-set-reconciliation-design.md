# Merkle set reconciliation: survey and design record

Status: DESIGN RECORD, pre-ratification. Direction ratified by the
operator 2026-08-27 ("the direction I want to go is the merkle trees");
nothing below is normative until its slice is ruled. The mechanization
-gap claim in §2 is UNVERIFIED and must pass the survey discipline
before it is ever stated as fact.

## 1. The idea, in estate terms

Each authority maintains a deterministic, history-independent search
tree over its admitted addresses. The set determines the root: one
32-byte identifier names the entire store state, and two instances
agree exactly when their roots agree, up to the standing collision
disjunct. Find-missing today is linear (key lists in `maxBatchKeys`
batches); reconciliation over the tree is logarithmic rounds with
bytes moved proportional to the symmetric difference. The algebra is
the one the store already is: the admitted set is a join-semilattice,
the range fingerprint is a monoid homomorphism out of it, and the
reconciliation dialogue is correct because it computes along that
homomorphism.

The server foundation this record builds on landed first: the
byte-plane backend seam (`src/server/Backend.ts`) owns exactly the
admitted-address set the tree indexes, and the admission core
guarantees everything under the tree is canonical admitted content.

## 2. Prior art (surveyed 2026-08-27; formal receipts owed at papers-lock)

### 2a. Paper proofs — the theorems exist on paper, unmechanized

| Work | What it gives us | Status |
|---|---|---|
| Auvolat & Taïani, *Merkle Search Trees* (SRDS 2019) | The layered construction (layer = leading-zero count of the item hash, base B). READ IN FULL 2026-08-27: the paper contains NO theorems and NO proofs — unicity is one asserted paragraph, balance is "easy to see" probabilistic sketching, and the O(d·log_B n) comparison bound is stated bare. The central set-determines-tree theorem is unproved even on paper; determinism is credited "similarly to [20]" | read; pin owed |
| Crosby & Wallach, *Super-Efficient Aggregating History-Independent Persistent Authenticated Dictionaries* (ESORICS 2009) — the MST paper's [20] | The prior deterministic binary treap-Merkle construction; the place the treap-shape's history-independence arguments actually live. With AFP Treaps (mechanized structure) and CMT 2025, this is the treap-route's proof lineage | surveyed, pin owed |
| Meyer, *Range-Based Set Reconciliation* (arXiv 2212.13567; SRDS 2023) | READ IN FULL 2026-08-27 — the real formal core, transcribable almost mechanically: **Definition 7** (tree-friendly: f(S₀ ∪ S₁) = f(S₀) ⊕ f(S₁) when max S₀ ≺ min S₁ — exactly our range-homomorphism law); **Proposition 1** (the ascending monoid fold lift_f is tree-friendly — a fold-append lemma); **Proposition 2** (every tree-friendly g IS lift_f for f(u) = g{u}, by induction on |S|, with g(∅) = 0 forced). Protocol 1's three cases (equal fingerprints / recursion anchor mandatory at ≤1 item or empty-fp / recurse over a covering split with ≥2 nonempty parts); termination by the largest-subrange measure strictly decreasing; correctness by induction UNDER the no-collision assumption — our collision disjunct replaces it. Complexity: the run's fingerprints form a b-ary tree of height ≤ 2⌈log_b n_min⌉ − ⌊log_b t⌋, rounds ∈ O(log n), bits ∈ O(n△·log n) against the Ω(n△) lower bound (MTZ03); covering (not partitioning) already suffices for correctness | read; pin owed |
| *RBSR via Range-Summarizable Order-Statistics Stores* (arXiv 2603.19820); *Tree algorithms for set reconciliation* (arXiv 2509.02373) | The 2025–26 follow-up line: range summaries + subtree cardinalities as the store interface — close to our backend-seam framing | surveyed, pin owed |
| *Cartesian Merkle Tree* (arXiv 2504.10944, 2025) | Treap + heap + Merkle: a DETERMINISTIC authenticated set tree, O(log n) ops — the treap-shaped alternative to MST for the same set-determines-root goal. Paper only | surveyed, pin owed |
| Prolly trees (Noms, Dolt); Negentropy (nostr); Iroh; Willow | Production constructions and wire protocols; differential-test referents for the dialogue, as LeanServer and the hostile peers serve the wire families today | engineering lit |

### 2b. Mechanized — machine-checked artifacts to learn from (none is MST/RBSR)

| Artifact | Prover | What it proves |
|---|---|---|
| **LambdaAuth — Formalization of Generic Authenticated Data Structures** (AFP; ITP 2019) | Isabelle | Miller et al.'s λ• GENERICALLY: correctness and security of authenticated structures for ANY functor-defined type — the ADS-functor pattern our record adopted, mechanized |
| *Logical Relations for Formally Verified ADS* (CCS 2025) | Rocq + Iris | The modern generic-ADS security treatment; plus Agda authenticated append-only skip lists in the same line |
| Incremental Merkle tree (Cassez, FM 2021; Eth2 deposit contract) | Dafny (+ K end-to-end) | The sequence-Merkle incremental algorithm, machine-checked — our MRK lane's genus |
| Merkle Patricia tree library (arXiv 2106.04826) | F* | The MAP-indexed authenticated tree |
| EverCrypt/Everest Merkle tree (deployed in CCF) | F* | Production verified sequence Merkle tree |
| **Treaps** (AFP: Haslbeck, Eberl, Nipkow) | Isabelle | The structural treap fact — shape equals the BST of priority-order insertion — which IS the history-independence backbone for treap-shaped authenticated sets |
| **CRDT convergence framework** (Gomes, Kleppmann et al., OOPSLA 2017, AFP; δ-CRDT follow-up 2020) | Isabelle | Strong eventual consistency proved over an explicit network model — the mechanized precedent for exactly our reconciliation-join theorem class (MST's own paper positions the tree as CRDT anti-entropy) |

### 2c. The gap, now evidence-based

Targeted searches (AFP, arXiv, prover ecosystems) surfaced **no
mechanization of Merkle Search Trees, prolly trees, or range-based set
reconciliation in any proof assistant**. Adjacent genera are covered —
sequence Merkle (Dafny/F*), map Merkle (F*), generic ADS (Isabelle/
Rocq), treap structure (Isabelle), CRDT convergence (Isabelle) — but
the set-indexed history-independent tree and the reconciliation
dialogue themselves appear unmechanized. Stated per the survey
discipline: absence surfaced by search, not proved; receipts owed
before the claim is made outside this record.

### 2d. The fingerprint question, settled by the literature

Two layers, never to be conflated. The COMBINATORIAL join theorem — in
our Lean model — needs no cryptography: it is stated with the standing
collision disjunct (after the dialogue both stores equal the join, OR
an explicit fingerprint collision is exhibited), and the homomorphism
law is pure monoid algebra. The ADVERSARIAL layer can never be "XOR
proved secure" because it is false: hash-then-XOR (Bellare–Micciancio's
XHash) is trivially forgeable via Wagner's generalized-birthday attack
— linear algebra over GF(2) manufactures collisions. The constructions
with real security are the same framework's AdHash and LtHash, whose
collision resistance REDUCES to the Short Integer Solutions problem in
the random-oracle model (Bellare–Micciancio; Lewi et al.'s LtHash
practice paper, eprint 2019/227), and elliptic-curve multiset hash
(arXiv 1601.06502), reducing to discrete-log-class assumptions. Those
reductions are imported, pinned assumptions — the estate never proves
them, exactly as the abstract-hash posture already treats digests. So
the S3 ruling's shape is confirmed: model = abstract commutative-monoid
fingerprint with the collision disjunct; wire = a reduction-carrying
multiset hash, never bare XOR.

## 3. Division of labor (ruled: Effect maximal, Lean minimal)

The operator's standing directive for this program: use Effect to its
fullest so the Lean model stays as simple as possible. Concretely:

**Lean owns the batch semantics only, over a canonical set
representation.**

- A set of addresses is a STRICTLY SORTED LIST — Std-only, no Finset
  machinery, and canonicality of the representation makes
  set-determines-root free by construction. The theorem with content
  is agreement between incremental operation and batch rebuild.
- The MST layer function is a pure `rank : Addr → Nat` (leading-zero
  count over the address bytes) — a deterministic parameter, no
  randomness anywhere in the model.
- `build : SortedAddrs → Tree`, `root : Tree → Digest` through the
  existing canonical-encoding + toy-digest vector pattern.
- `fingerprint : Range → SortedAddrs → Fp` as a monoid fold.
- The reconciliation dialogue as a pure function over TWO sorted
  lists producing the transcript — no wire, no state, no IO.

Law families (the shape, pre-minting):

1. **History independence**: `build (insertSorted x s) = insert x
   (build s)` — incremental agrees with batch, so maintenance order
   never shows in the root.
2. **Fingerprint homomorphism**: for disjoint ranges,
   `fp (r₁ ⊔ r₂) = fp r₁ ⊕ fp r₂`.
3. **Reconciliation join**: after the dialogue both sides hold the
   join of the two sets, transfer is bounded by the symmetric
   difference — or a fingerprint-collision witness is exhibited (the
   standing collision-disjunct posture, stated constructively).

**Effect owns everything operational.**

- Incremental tree maintenance as a derived index over the backend
  seam (`SynchronizedRef`, or lock-free reads riding the grow-only
  monotonicity argument the admission core states).
- Streaming ranges (`Stream`), batching and budgets (config fields),
  deadlines and retry (the existing shell), spans (`Effect.fn`).
- The `/recon` transport as new routes on the server core — the
  dispatcher already factors as handler-over-backend, so the plane is
  additive.
- Differential harnesses: the dialogue run in-process between two
  backend interpretations is handler substitution, exactly the
  EffectPeer binding landed with the server slice.

The TS mirror consumes model-minted vectors the same way every family
does today: the Lean batch semantics generates rows (build roots over
generated sets, fingerprints over ranges, dialogue transcripts over
set pairs), and the TS incremental implementation must reproduce them
byte-for-byte — the incremental-equals-batch law is the conformance
suite, not just a theorem.

## 4. Wire sketch (planned-planes only — never a packet guess)

A `/recon` plane enters PROFILE-CAS-HTTP-0 §13 as planned, ratified
separately: a root-fingerprint read, a range-fingerprint exchange, and
a range-items transfer, all closed binary framings in the house style.
The fingerprint construction on the wire is a RULING (cryptographic
multiset hash, never bare XOR) before any framing is drafted.

## 4b. The four trees, and whether the relationship is defined

The estate now carries four tree structures; the survey makes their
relationship precise, and it IS definable — three of them are one
pattern, and the fourth consumes it.

1. **The chunk tree** (MRK lane, Lean, laws landed): authenticates a
   SEQUENCE — the query algebra is position.
2. **The blob recipe-1 graph** (store-carried): the chunk tree
   realized as CAS nodes — same genus, different carrier.
3. **The set tree** (S2 target, MST or treap-shaped): authenticates a
   SET — the query algebra is membership, and history independence is
   its defining law. (The map-indexed sibling — Patricia-style — is
   the genus the F* MPT work covers; it is the natural fourth ADS
   index if the estate ever wants authenticated maps.)
4. **The interaction tree** (`Effects.Server.Prog`): NOT an
   authenticated structure at all — the free computation tree that
   QUERIES the others through handlers.

The unifying statement for 1–3 is the ADS-functor pattern the record
already adopted, and the survey shows it MECHANIZED: LambdaAuth (AFP,
Isabelle) proves correctness and security once, generically, for
hash-annotated fixpoints of any functor-defined type — sequence, set,
and map trees differ only in the functor and the query algebra, and
each inherits the generic theorem. Our Lean development can state the
same factoring: one Merkle-annotation construction, three
instantiations, laws proved at the functor level where they truly live
(the MRK lane's per-family proofs remain the concrete anchors).

The fourth tree composes rather than instantiates: reconciliation is a
`Prog` over the dialogue signature run against two set-tree handlers,
so its join theorem is an `interp` equation — and the mechanized
precedent for exactly that statement class is the Isabelle CRDT
convergence framework, which proved strong eventual consistency over
an explicit network model. Our seam is strictly simpler: two lawful
handlers and a finite dialogue, no network nondeterminism until the
transport slice.

One S2 design input the survey adds: the treap-shaped construction
(Cartesian Merkle Tree) reaches set-determines-root with a BINARY node
structure whose structural backbone (treap shape = priority-order BST)
is already mechanized in the AFP — while the MST's B-tree-ish layered
nodes have the production referents. Both satisfy the laws; the S2
grill should choose the node shape with eyes open.

## 5. Proposed slice order (for ratification)

- **S1 — survey verification**: SEARCH PASS DONE (2026-08-27, §2);
  remaining: mint provenance receipts for the pinned works, and read
  Meyer's proofs in full so the Lean statements mirror his induction.
- **S2 — the Lean first bite**: canonical sorted-list sets, `rank`,
  `build`, `root`; the history-independence family minted
  plan-§7-first with generated vectors; TS incremental index over the
  backend seam bound to those vectors.
- **S3 — the fingerprint ruling + monoid**: choose the multiset-hash
  construction; homomorphism family.
- **S4 — the dialogue**: pure reconciliation model + join theorem;
  differential against a production referent under the adopted-tools
  discipline.
- **S5 — the `/recon` plane**: profile ratification, server routes,
  adapter surface.

Context mints owed when S2 lands: the search-tree term, the range
fingerprint, the reconciliation dialogue — through the owning
CONTEXT.md, with obligations and avoid-lists, at ratification.

## 6. The demo (operator-directed): foldkit front end, real reactive state

The visual demo is a real app, not an artifact. Front end = foldkit
(foldkit.dev): the Elm architecture over Effect — one Model, Messages
as facts, a pure `update : (Model, Message) → (Model, Commands)`, a
pure `view`, Commands for one-shot effects, Subscriptions as scoped
Streams. The mapping is exact and pleasingly honest to the theory:

- **Model** = two replica set trees (persistent, digest-injected) plus
  the dialogue's in-flight state.
- **Messages** = `Inserted(replica, item)`, `SyncRequested`,
  `DialogueStepped(message-part)` — the reconciliation protocol's own
  range-fingerprint/range-item-set messages ARE app Messages, so the
  demo literally plays Protocol 1 step by step, visibly.
- **update** = the pure dialogue step (the same function the Lean
  model states); **view** = the trees rendered with subtree-hash-keyed
  coloring so shared structure is visibly shared, plus the round and
  bytes-moved counters against the O(n△·log n) bound.

Production referent for the tree side: domodwyer's Rust
`merkle-search-tree` crate (upsert / root_hash / serialise_page_ranges
/ diff over page ranges; fuzz + property testing) — both an API shape
to learn from and a differential target later. API source for the
front end: foldkit's llms-full.txt / per-page markdown. The demo's
tree core lives with the demo under `experiments/` until the S2 grill
promotes it into the package beside its Lean family.
