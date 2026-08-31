# CAS soundness and round-trip proof references

Status: research note, 2026-08-27. No Foldlab claim is promoted by this
document. In particular, every use of *correctness*, *security*, *integrity*,
or *round trip* below names the source's own judgment; none transfers a theorem
to the Effects CAS.

## Provenance and scope

The exact publication bytes and inspected proof-repository objects are recorded
in the [resolution receipt](../../../.reference/provenance/receipts/cas-soundness-roundtrip-sources.json).
The paper-lock generator is not amended here: this host already contains
unrelated PDFs awaiting corpus-wide cluster assignment, so silently regenerating
from only this survey's subset would violate the ledger's partition rule.

This survey asks which proof shapes can support five separate obligations:

1. **Codec round trip and exact image:** decoding an encoded admitted value
   returns that value; successful decoding also proves that the bytes are the
   encoder's canonical image.
2. **CAS store algebra:** a successful fresh insertion is retrievable at the
   returned address, repeated insertion is idempotent, and collisions have an
   explicit semantics rather than being erased by an unstated injectivity axiom.
3. **Structural preservation:** insertion and reachability preserve address
   consistency, reference closure, expected-kind agreement, and acyclicity.
4. **Fail-closed observation:** corrupted, dangling, wrong-kind, or
   non-canonical objects are rejected at the boundary that observes them.
5. **Persistence and recovery:** a durable implementation refines the pure
   store across writes, crashes, and recovery. This is a different theorem from
   the in-memory CAS algebra.

The literature does not package these as one standard theorem called “CAS
soundness.” The strongest reusable design lesson is to keep the five judgments
separate and state the hash premise at the point where it is first needed.

## Foldlab baseline

The ratified Effects plan already separates codec, addressing, admission, and
persistence concerns. The machine design records the analogous obligations as
O4 (codec), O8–O16 (store algebra), O17 (typed reachability), and O18
(decidable admission). The working Effects CAS codec currently sharpens O4 into
three Level-0 statements:

```text
decode (encodeNode n) = some n                         when n.WF
decode b = some n  ->  b = encodeNode n and n.WF
encodeNode n = encodeNode m  ->  n = m                 when n.WF and m.WF
```

These are the right shape for canonical content addressing: forward round trip
alone is insufficient because a decoder may accept multiple byte strings for
one value. No source below proves the later Effects store, address, admission,
or persistence judgments.

## Primary reference matrix

| Reference | Mechanized judgment | Assumptions and trust boundary | Supports here | Does not support here |
| --- | --- | --- | --- | --- |
| [EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats](https://www.usenix.org/system/files/sec19-ramananandro_0.pdf) | In F*/LowParse, parser correctness is `p(s(m)) = m`; exactness is `p⁻¹(V) = s(V)`; non-malleability says equal successful results imply the same consumed prefix; completeness covers all admitted values; the strong-prefix property controls parsers that leave a remainder. | F* checking plus its SMT/toolchain; the generated C path additionally crosses extraction and the C compiler. The QuackyDucky frontend is untrusted but emits F* specifications and implementations that are checked. | The closest vocabulary for `decode_encodeNode`, `decode_exact`, `encodeNode_injOn`, trailing-byte rejection, and the distinction between round trip, exact image, and uniqueness. | Hash addressing, store mutation, reference closure, crash recovery, or any theorem about Foldlab's codec. |
| [Narcissus: Deriving Correct-By-Construction Decoders and Encoders from Binary Formats](https://arxiv.org/abs/1803.04870v3) | Coq Theorem 2.3, **Decode Inverts Encode**, and Theorem 2.4, **Encode Inverts Decode**, connect a relational format to correct encoders and decoders. The artifact's `CorrectDecodeEncode` proves the forward round trip under source and cache invariants. `CorrectDecoder` also returns an accepted prefix plus remainder and witnesses membership in the format relation. | Coq kernel plus the extraction/runtime path for deployed code. Laws quantify over an explicit format relation, source predicate, cache relation, and decoder invariant. | A strong pattern for deriving the encoder and decoder from one relation and for threading well-formedness and parser state through compositional proofs. | Canonical bytes by default. Its own examples intentionally admit arbitrary unused bits, so multiple encodings may be valid unless uniqueness/exactness is separately proved. It does not prove CAS store or hash properties. |
| [Verification of a Merkle Patricia Tree Library Using F*](https://arxiv.org/abs/2106.04826v1) | The inspected F* `goal` commits a node, loads it at the produced index, and ensures `equivalent_nodes` plus the modeled storage invariant. `commit_node` and `load_node` separately refine ghost specifications; tree operations preserve structural invariants and nested key-value behavior. The paper also gives a conditional reduction from a Merkle-hash collision to a primitive-hash failure. | Preconditions include correctly indexed nodes, enough fuel, model-storage invariants, and several F* interfaces/assumptions. The verified F* modules are manually ported and extracted into an otherwise unverified OCaml library. The collision reduction's complexity argument is not formalized. | The closest single precedent for a store write/read round trip, bottom-up persistence, structural invariant preservation, and an explicit conditional hash claim. | A byte-keyed CAS map, canonical codec exactness, typed DAG closure, adversarial collision semantics for insertion, or crash recovery. “Equivalent node” is its own tree judgment, not Foldlab equality. |
| [Generic Authenticated Data Structures, Formally](https://doi.org/10.4230/LIPIcs.ITP.2019.10) | Nominal Isabelle Theorem 23 relates ideal, prover, and verifier evaluations. Theorem 24 says an accepting verifier corresponds to an ideal/prover execution **or** yields explicit distinct closed terms with equal hashes. | Isabelle/HOL and Nominal Isabelle. Collision resistance is not formalized probabilistically; the theorem exposes the collision as a disjunct and the cryptographic interpretation remains a meta-argument. | The best precedent for Foldlab's hash lattice: prove all deterministic laws without hash injectivity, then isolate the exact theorem that needs either a collision witness or a collision-resistance assumption. | Encoder/decoder exactness, `put`/`get`, durable storage, or direct proofs of a Merkle DAG representation. |
| [Logical Relations for Formally Verified Authenticated Data Structures](https://doi.org/10.1145/3719027.3744801) | Rocq/Iris Theorem 4.1 (`authentikit_security_syntactic`) gives verifier-to-ideal security up to hash collision; Theorem 5.1 (`authentikit_correctness_syntactic`) relates prover, ideal, and verifier behavior. The artifact also proves security/correctness refinements for optimized Merkle retrieval. | Rocq kernel, Iris, the CF-SL “up-to-bad” logic, and the source language/operational semantics. The paper and repository explicitly map theorem numbers to proof names. | A modern implementation-refinement pattern for linking an optimized retrieval routine to an ideal authenticated-data-structure semantics while keeping collision failure explicit. | A CAS object's canonical bytes, storage closure, insertion algebra, persistence, or the OCaml compiler/runtime path as a verified whole. |
| [Implementing and reasoning about hash-consed data structures in Coq](https://arxiv.org/abs/1311.2959v4) | Coq developments compare hash-consing implementations and abstraction techniques so that physical sharing/identifiers do not leak into client reasoning; correctness is expressed through abstract structural equality and representation invariants. | The guarantee varies by implementation technique; extraction, weak tables, and runtime identity can sit outside the purely functional proof boundary. | The existing Foldlab pin is useful for choosing an abstraction barrier around deduplication and physical sharing: the address/index should not become semantic equality by accident. | Cryptographic collision resistance, durable CAS behavior, byte-codec round trips, reference closure, or adversarial reads. |
| [The Design and Implementation of a Verified File System with End-to-End Data Integrity](https://arxiv.org/abs/2012.07917v1) | IFSCQ extends FSCQ's Crash Hoare Logic: operations carry pre-, post-, and crash conditions; after recovery the disk refines a consistent state. Its malicious-disk model proves that a bad block read causes fail-stop behavior when the Merkle check fails, while a trusted persistent root anchors rollback detection within the stated crash model. | Coq plus extracted Haskell, compiler/runtime, Linux FUSE, cryptographic assumptions, trusted hardware/OS, and modeled TPM state. The threat model permits rollback indistinguishable from a crash to the previous stable state. | The right later reference for a persistence theorem: put the Merkle metadata above the transaction/log layer, update data and authentication state atomically, and make corruption an explicit failed observation. | Current pure CAS algebra, codec exactness, object-level closure, or a proof that a content address alone supplies freshness/durability. |

## What to borrow

### 1. Name the codec laws separately

EverParse supplies the cleanest taxonomy for the current M2 work:

- **forward correctness:** `decode (encode n) = some n`;
- **image exactness:** `decode b = some n -> b = encode n`;
- **non-malleability / uniqueness:** one admitted value has one accepted byte
  representation;
- **completeness:** every admitted value is encodable/decodable;
- **strong prefix or closed-input discipline:** success identifies exactly which
  bytes were consumed.

The current `parseNode` stage lemmas plus closed `decode` are a direct local
specialization of this decomposition. Narcissus is the useful counterexample:
deriving both directions from one relation does not make the relation canonical.
Foldlab should continue to prove exact image rather than infer it from the
forward round trip.

### 2. Factor store round trip through a transition judgment

Plebeia's strongest reusable shape is not simply `load(commit(x)) = x`; it is:

```text
precondition(store, x)
commit(store, x) = (store', location)
load(store', location) = x'          and equivalent(x, x')
invariant(store')
```

For Foldlab, the analogous theorem should quantify over the actual insertion
transition and distinguish fresh from occupied addresses. A candidate shape is:

```text
PutFresh H S n S' a
-> a = H (encode n)
-> get S' a = some n
-> StoreWF H S'
```

The collision case should be a separate theorem characterizing the occupied
address no-op or conflict result. It must not be discharged by globally assuming
`Injective H`.

### 3. Use an explicit collision outcome, not an ambient axiom

Both Isabelle's generic ADS proof and Rocq/Iris's CF-SL make the desirable
structure precise:

```text
verified observation refines ideal observation
OR
there exist x != y with H x = H y
```

This aligns with the machine design's Level 0 / Level 1 split. Address
construction, insertion idempotence, closure, and acyclicity should remain
Level 0 wherever possible. Faithfulness from equal addresses back to equal
canonical nodes is the first place for a named injectivity premise; deployment
security needs a different probabilistic/adversarial judgment and should not be
smuggled into a functional theorem.

### 4. Keep admission stronger than byte decoding

Codec success proves only that bytes denote a well-formed node in the codec's
image. It does not prove that:

- the requested address equals the hash of those canonical bytes;
- every reference resolves;
- the resolved node has the expected kind;
- the reachable graph is acyclic; or
- the durable medium will preserve the write.

The external work reinforces the existing Foldlab split: decoding, address
verification, reference admission, and persistence need separate judgments and
separate failure constructors. A single `get : Address -> Option Node` is too
weak to state which boundary failed.

### 5. Defer crash claims to a refinement layer

IFSCQ/FSCQ show why a pure `get-after-put` proof cannot justify persistence.
Once a filesystem, database, packfile, or remote object service is in scope, the
required statement needs traces or a crash logic: data bytes and authentication
metadata commit atomically; recovery returns a previously committed state; and
reads either refine that state or report corruption. This should be a later
implementation/refinement theorem, not an extra premise on the pure store.

## Recommended reading order

1. **EverParse** for the exact codec law vocabulary now applicable to M2.
2. **Plebeia** for a concrete commit/load refinement and invariant-preservation
   pattern over Merkle storage.
3. **Generic Authenticated Data Structures, Formally** for explicit collision
   disjunctions without a global injective-hash axiom.
4. **Narcissus** for relational format specifications and mechanically derived
   compositional codecs, read together with its non-canonical examples.
5. **VeriAuth** for modern Rocq/Iris refinement from optimized authenticated
   retrieval to an ideal semantics.
6. **IFSCQ/FSCQ** only when a durable backend and crash model enter scope.
7. **Hash-consed data structures in Coq** when deciding how physical sharing
   and deduplication remain hidden behind the semantic store interface.

## Result for the current project

The research supports the existing direction and suggests no contract change.
The immediate proof target should remain the four-layer stack:

1. codec forward round trip plus exact image;
2. pure store transition laws, with fresh and collision cases separated;
3. decidable admission and preservation of closure/kind/acyclicity;
4. implementation refinement for corruption, concurrency, and crash recovery.

The current codec work already occupies the first layer. The highest-value next
external pattern is Plebeia's transition-indexed commit/load theorem, but adapted
to Foldlab's canonical bytes and typed references. The hash-security layer should
follow the Isabelle/Rocq “ideal behavior or collision witness” shape. No surveyed
source supports calling the Effects CAS, its TypeScript implementation, or a
future durable backend sound or verified today.
