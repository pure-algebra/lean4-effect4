import Effects.Cas.Codec
import Effects.Merkle.Tree
import Effects.Wire.Nat32

/-!
# The blob refinement tie — a blob is a node graph, not a second store

The abstract Merkle address function instantiated as the CAS address
of a canonical node encoding: leaves become ordinary nodes carrying
the index-prefixed chunk bytes, parents become ordinary two-reference
nodes, and the blob's identity is the root node's address — an
ordinary content identifier, so negotiation, closure-gated publish,
and pull apply to blobs verbatim.

One declared blob kind tag serves both shapes, because the ratified
pre-image carrier's parent holds child ADDRESSES only — no child
kinds — so a per-child expected-tag cannot be derived at this
altitude. The leaf/parent separation is STRUCTURAL instead: a leaf
node carries a nonempty index-prefixed payload and no references, a
parent node carries an empty payload and exactly two references, the
node mapping is injective on bounded pre-images, and the codec's
non-malleability turns that into byte-level separation — so a
pre-image collision under the instantiated address function yields a
genuine byte-level hash collision, keeping every collision disjunct
of the Merkle laws meaningful for blobs.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes Addr32 Node Ref encodeNode encodeNode_injOn)
open Effects.Wire

/-- The declared blob kind tag: one tag for both shapes, separation
structural. -/
def blobTag : UInt8 := 7

/-- The node a pre-image materializes as. A leaf's payload is its
index-prefixed chunk bytes with no references; a parent's payload is
empty with the two child references in order. -/
def preNode : Pre Addr32 → Node
  | .leaf index bytes =>
      { version := 0, tag := blobTag, payload := nat32 index ++ bytes
        refs := [] }
  | .parent l r =>
      { version := 0, tag := blobTag, payload := []
        refs := [⟨blobTag, l⟩, ⟨blobTag, r⟩] }

/-- The instantiated Merkle address function: the CAS address of the
canonical node encoding. -/
def blobHP (H : Bytes → Addr32) : HP Addr32 :=
  ⟨fun p => H (encodeNode (preNode p))⟩

/-- Bounded pre-images: the domain on which the node mapping is
injective and the materialized nodes are byte-bound well-formed. The
index bound is the profile's chunk-count bound; the byte bound leaves
room for the four-byte index prefix. -/
def PreWF : Pre Addr32 → Prop
  | .leaf index bytes =>
      index < 4294967296 ∧ bytes.length < 4294967292
  | .parent _ _ => True

/-- The materialized node of a bounded pre-image is byte-bound
well-formed. -/
theorem preNode_wf (p : Pre Addr32) (hp : PreWF p) : (preNode p).WF := by
  cases p with
  | leaf index bytes =>
    obtain ⟨hi, hb⟩ := hp
    constructor
    · simp only [preNode, List.length_append, nat32, List.length_cons,
        List.length_nil]
      omega
    · simp [preNode]
  | parent l r =>
    constructor
    · simp [preNode]
    · simp [preNode]

/-- The node mapping is injective on bounded pre-images. -/
theorem preNode_inj (p q : Pre Addr32) (hp : PreWF p) (hq : PreWF q)
    (h : preNode p = preNode q) : p = q := by
  cases p with
  | leaf ip bp =>
    cases q with
    | leaf iq bq =>
      obtain ⟨hip, -⟩ := hp
      obtain ⟨hiq, -⟩ := hq
      have hpay := congrArg Node.payload h
      simp only [preNode] at hpay
      have hrp := readNat32_nat32 ip hip bp
      rw [hpay, readNat32_nat32 iq hiq bq] at hrp
      injection hrp with hrp
      injection hrp with hi hb
      rw [hi, hb]
    | parent lq rq =>
      exfalso
      have hpay := congrArg Node.payload h
      simp only [preNode] at hpay
      have := congrArg List.length hpay
      simp only [List.length_append, nat32, List.length_cons,
        List.length_nil] at this
      omega
  | parent lp rp =>
    cases q with
    | leaf iq bq =>
      exfalso
      have hpay := congrArg Node.payload h
      simp only [preNode] at hpay
      have := congrArg List.length hpay
      simp only [List.length_append, nat32, List.length_cons,
        List.length_nil] at this
      omega
    | parent lq rq =>
      have hrefs := congrArg Node.refs h
      simp only [preNode] at hrefs
      injection hrefs with h1 h2
      injection h1 with _ hl
      injection h2 with h3 _
      injection h3 with _ hr
      rw [hl, hr]

/-- A pre-image collision under the instantiated address function is a
genuine byte-level hash collision on distinct canonical encodings. -/
theorem blob_collision_bytes (H : Bytes → Addr32) (p q : Pre Addr32)
    (hp : PreWF p) (hq : PreWF q) (hne : p ≠ q)
    (hcol : (blobHP H).H p = (blobHP H).H q) :
    encodeNode (preNode p) ≠ encodeNode (preNode q) ∧
      H (encodeNode (preNode p)) = H (encodeNode (preNode q)) := by
  refine ⟨?_, hcol⟩
  intro henc
  exact hne (preNode_inj p q hp hq
    (encodeNode_injOn (preNode_wf p hp) (preNode_wf q hq) henc))

/-! ## The materialized root -/

/-- The root node a chunk list materializes as: its address is the
Merkle root. -/
def blobNodeOf (H : Bytes → Addr32) (base : Nat) (chunks : List Bytes) :
    Node :=
  if chunks.length ≤ 1 then preNode (.leaf base (chunks.headD []))
  else
    preNode (.parent
      (root (blobHP H) base (chunks.take (pow2Below chunks.length)))
      (root (blobHP H) (base + pow2Below chunks.length)
        (chunks.drop (pow2Below chunks.length))))

/-- Q4, the tie: the Merkle root IS the address of the materialized
root node — an ordinary content identifier, so the sync machinery's
reference closure over the materialized graph is exactly the blob's
tree. -/
theorem blob_root_addr (H : Bytes → Addr32) (base : Nat)
    (chunks : List Bytes) :
    root (blobHP H) base chunks =
      H (encodeNode (blobNodeOf H base chunks)) := by
  by_cases h : chunks.length ≤ 1
  · conv => lhs; rw [root.eq_def]
    rw [dif_pos h]
    simp only [blobNodeOf, if_pos h]
    rfl
  · rw [root_split (blobHP H) base chunks h]
    simp only [blobNodeOf, if_neg h]
    rfl

/-- The materialized root node is byte-bound well-formed whenever the
chunk bytes respect the profile bound (the leaf case; parents are
well-formed unconditionally). -/
theorem blobNodeOf_wf (H : Bytes → Addr32) (base : Nat)
    (chunks : List Bytes) (hbase : base < 4294967296)
    (hc : ∀ c ∈ chunks, c.length < 4294967292) :
    (blobNodeOf H base chunks).WF := by
  by_cases h : chunks.length ≤ 1
  · simp only [blobNodeOf, if_pos h]
    refine preNode_wf _ ⟨hbase, ?_⟩
    cases chunks with
    | nil => simp
    | cons c cs =>
      simp only [List.headD_cons]
      exact hc c (by simp)
  · simp only [blobNodeOf, if_neg h]
    exact preNode_wf _ trivial

end Effects.Merkle
