import Effects.Cas.Codec
import Effects.Merkle.Tree
import Effects.Wire.Nat32

/-!
# The blob manifest graph — the headline recipe

The ratified four-kind blob representation: a manifest node committing
the recipe identity, total byte length, and leaf count over the tree
root; parents with two tree references; leaves carrying the absolute
index and chunk length over a chunk-data reference; and chunk-data
nodes holding the raw bytes. All four are ordinary canonical CAS
nodes and the blob's identity is the manifest node's ordinary
address. Raw chunks are content-addressed WITHOUT position, so equal
chunks deduplicate across positions and blobs; position binding lives
in the leaf, exactly the separation the prior-art review adopted from
the XET aggregation design.

Chunk data and the manifest carry their own kind tags. Parents and
leaves share ONE tree tag with STRUCTURAL separation (an eight-byte
payload and one chunk reference versus an empty payload and two tree
references) for the reason recorded at the second Merkle slice: the
pre-image carrier's parent holds child addresses only, so a per-child
kind cannot be derived at the abstraction the tree laws live at; the
node mapping is injective on bounded pre-images and the codec's
non-malleability turns the structural separation into byte-level
separation.

The manifest-content codec is closed, exact, and RECIPE-GATED: an
unknown recipe identifier fails closed at decode, so a reader never
guesses semantics — the recipe-evolution obligation's carrier.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes Addr32 Node Ref encodeNode encodeNode_injOn)
open Effects.Wire

/-! ## Kinds and recipes -/

/-- The chunk-data kind tag. -/
def chunkTag : UInt8 := 8

/-- The tree kind tag, shared by parents and leaves. -/
def treeTag : UInt8 := 9

/-- The manifest kind tag. -/
def manifestTag : UInt8 := 10

/-- The first frozen recipe: the inline-leaf tie landed at the second
Merkle slice. -/
def recipeInlineLeaf : Nat := 0

/-- The headline recipe: referenced content chunks under this
manifest graph. -/
def recipeReferencedChunk : Nat := 1

/-- The registered recipe identifiers; unknown identifiers fail
closed. -/
def knownRecipes : List Nat := [recipeInlineLeaf, recipeReferencedChunk]

/-! ## The node materializations -/

/-- A raw chunk as an ordinary node: content without position. -/
def chunkDataNode (bytes : Bytes) : Node :=
  { version := 0, tag := chunkTag, payload := bytes, refs := [] }

/-- A leaf: the absolute index and chunk length over the chunk-data
reference — position binding without forfeiting chunk dedup. -/
def leafRefNode (index len : Nat) (chunk : Addr32) : Node :=
  { version := 0, tag := treeTag, payload := nat32 index ++ nat32 len
    refs := [⟨chunkTag, chunk⟩] }

/-- A parent: two tree references, empty payload. -/
def parentRefNode (l r : Addr32) : Node :=
  { version := 0, tag := treeTag, payload := []
    refs := [⟨treeTag, l⟩, ⟨treeTag, r⟩] }

/-- The manifest: recipe identity, total bytes, and leaf count over
the tree root. -/
def manifestNode (recipeId totalBytes leafCount : Nat)
    (treeRoot : Addr32) : Node :=
  { version := 0, tag := manifestTag
    payload := nat32 recipeId ++ nat64 totalBytes ++ nat32 leafCount
    refs := [⟨treeTag, treeRoot⟩] }

/-- The composed Merkle address function for the referenced-chunk
recipe: a leaf's address is the address of its leaf node, whose one
reference is the address of the chunk-data node holding the bytes. -/
def refHP (H : Bytes → Addr32) : HP Addr32 :=
  ⟨fun p => match p with
    | .leaf index bytes =>
        H (encodeNode (leafRefNode index bytes.length
          (H (encodeNode (chunkDataNode bytes)))))
    | .parent l r => H (encodeNode (parentRefNode l r))⟩

/-! ## Well-formedness and separation -/

/-- Bounded pre-images for this recipe. -/
def RefPreWF : Pre Addr32 → Prop
  | .leaf index bytes =>
      index < 4294967296 ∧ bytes.length < 4294967296
  | .parent _ _ => True

theorem chunkDataNode_wf (bytes : Bytes)
    (hb : bytes.length < 4294967296) : (chunkDataNode bytes).WF := by
  constructor
  · simpa [chunkDataNode] using hb
  · simp [chunkDataNode]

theorem leafRefNode_wf (index len : Nat) (chunk : Addr32) :
    (leafRefNode index len chunk).WF := by
  constructor
  · simp only [leafRefNode, List.length_append, nat32, List.length_cons,
      List.length_nil]
    omega
  · simp [leafRefNode]

theorem parentRefNode_wf (l r : Addr32) : (parentRefNode l r).WF := by
  constructor
  · simp [parentRefNode]
  · simp [parentRefNode]

theorem manifestNode_wf (recipeId totalBytes leafCount : Nat)
    (treeRoot : Addr32) :
    (manifestNode recipeId totalBytes leafCount treeRoot).WF := by
  constructor
  · simp only [manifestNode, List.length_append, nat32, nat64,
      List.length_cons, List.length_nil]
    omega
  · simp [manifestNode]

/-- A pre-image collision under the composed address function yields a
byte-level hash collision at the tree layer or the chunk layer. -/
theorem ref_collision_bytes (H : Bytes → Addr32) (p q : Pre Addr32)
    (hp : RefPreWF p) (hq : RefPreWF q) (hne : p ≠ q)
    (hcol : (refHP H).H p = (refHP H).H q) :
    ∃ b₁ b₂, b₁ ≠ b₂ ∧ H b₁ = H b₂ := by
  cases p with
  | leaf ip bp =>
    cases q with
    | leaf iq bq =>
      obtain ⟨hip, hbp⟩ := hp
      obtain ⟨hiq, hbq⟩ := hq
      by_cases henc : encodeNode (leafRefNode ip bp.length
            (H (encodeNode (chunkDataNode bp)))) =
          encodeNode (leafRefNode iq bq.length
            (H (encodeNode (chunkDataNode bq))))
      · have hnodes := encodeNode_injOn (leafRefNode_wf ..)
          (leafRefNode_wf ..) henc
        have hpay := congrArg Node.payload hnodes
        have hrefs := congrArg Node.refs hnodes
        simp only [leafRefNode] at hpay hrefs
        have hidx : iq = ip := by
          have hr := readNat32_nat32 ip hip (nat32 bp.length)
          rw [hpay, readNat32_nat32 iq hiq (nat32 bq.length)] at hr
          injection hr with hr
          exact congrArg Prod.fst hr
        injection hrefs with hhead htail
        injection hhead with htag hchunk
        by_cases hbytes : bp = bq
        · exact absurd (by rw [hidx.symm, hbytes]) hne
        · refine ⟨encodeNode (chunkDataNode bp),
            encodeNode (chunkDataNode bq), ?_, hchunk⟩
          intro hce
          exact hbytes (congrArg Node.payload
            (encodeNode_injOn (chunkDataNode_wf bp hbp)
              (chunkDataNode_wf bq hbq) hce))
      · exact ⟨_, _, henc, hcol⟩
    | parent lq rq =>
      refine ⟨encodeNode (leafRefNode ip bp.length
          (H (encodeNode (chunkDataNode bp)))),
        encodeNode (parentRefNode lq rq), ?_, hcol⟩
      intro henc
      have hnodes := encodeNode_injOn (leafRefNode_wf ..)
        (parentRefNode_wf ..) henc
      have := congrArg (fun n => n.payload.length) hnodes
      simp only [leafRefNode, parentRefNode, List.length_append, nat32,
        List.length_cons, List.length_nil] at this
      omega
  | parent lp rp =>
    cases q with
    | leaf iq bq =>
      refine ⟨encodeNode (parentRefNode lp rp),
        encodeNode (leafRefNode iq bq.length
          (H (encodeNode (chunkDataNode bq)))), ?_, hcol⟩
      intro henc
      have hnodes := encodeNode_injOn (parentRefNode_wf ..)
        (leafRefNode_wf ..) henc
      have := congrArg (fun n => n.payload.length) hnodes
      simp only [leafRefNode, parentRefNode, List.length_append, nat32,
        List.length_cons, List.length_nil] at this
      omega
    | parent lq rq =>
      refine ⟨encodeNode (parentRefNode lp rp),
        encodeNode (parentRefNode lq rq), ?_, hcol⟩
      intro henc
      have hnodes := encodeNode_injOn (parentRefNode_wf ..)
        (parentRefNode_wf ..) henc
      have hrefs := congrArg Node.refs hnodes
      simp only [parentRefNode] at hrefs
      injection hrefs with h1 h2
      injection h1 with htag1 hl
      injection h2 with h3 htail
      injection h3 with htag2 hr
      exact hne (by rw [hl, hr])

/-! ## The materialized root and the manifest identity -/

/-- The tree-root node a chunk list materializes as under this
recipe. -/
def refNodeOf (H : Bytes → Addr32) (base : Nat) (chunks : List Bytes) :
    Node :=
  if chunks.length ≤ 1 then
    leafRefNode base (chunks.headD []).length
      (H (encodeNode (chunkDataNode (chunks.headD []))))
  else
    parentRefNode
      (root (refHP H) base (chunks.take (pow2Below chunks.length)))
      (root (refHP H) (base + pow2Below chunks.length)
        (chunks.drop (pow2Below chunks.length)))

/-- The tie for the referenced-chunk recipe: the Merkle root IS the
address of the materialized tree-root node. -/
theorem ref_root_addr (H : Bytes → Addr32) (base : Nat)
    (chunks : List Bytes) :
    root (refHP H) base chunks =
      H (encodeNode (refNodeOf H base chunks)) := by
  by_cases h : chunks.length ≤ 1
  · conv => lhs; rw [root.eq_def]
    rw [dif_pos h]
    simp only [refNodeOf, if_pos h]
    rfl
  · rw [root_split (refHP H) base chunks h]
    simp only [refNodeOf, if_neg h]
    rfl

/-- The blob identity: the manifest node's address over the tree
root — an ordinary content identifier committing the recipe, the
total bytes, and the leaf count. -/
def blobManifestAddr (H : Bytes → Addr32) (totalBytes : Nat)
    (chunks : List Bytes) : Addr32 :=
  H (encodeNode (manifestNode recipeReferencedChunk totalBytes
    chunks.length (root (refHP H) 0 chunks)))

/-! ## The manifest-content codec (closed, exact, recipe-gated) -/

/-- The manifest payload fields. -/
structure ManifestContent where
  recipeId : Nat
  totalBytes : Nat
  leafCount : Nat
  deriving DecidableEq

/-- The canonical sixteen-byte manifest payload. -/
def encodeManifest (m : ManifestContent) : List UInt8 :=
  nat32 m.recipeId ++ nat64 m.totalBytes ++ nat32 m.leafCount

/-- The closed, recipe-gated decoder: exactly sixteen bytes, no
trailing content, and only REGISTERED recipe identifiers — an unknown
recipe fails closed, never guesses. -/
def decodeManifest? (bytes : List UInt8) : Option ManifestContent :=
  match readNat32 bytes with
  | none => none
  | some (recipeId, r1) =>
    if knownRecipes.contains recipeId then
      match readNat64 r1 with
      | none => none
      | some (totalBytes, r2) =>
        match readNat32 r2 with
        | some (leafCount, []) => some ⟨recipeId, totalBytes, leafCount⟩
        | _ => none
    else none

/-- Forward correctness on representable, registered contents. -/
theorem decodeManifest_encodeManifest (m : ManifestContent)
    (hr : knownRecipes.contains m.recipeId)
    (hrb : m.recipeId < 4294967296)
    (ht : m.totalBytes < 18446744073709551616)
    (hl : m.leafCount < 4294967296) :
    decodeManifest? (encodeManifest m) = some m := by
  unfold decodeManifest? encodeManifest
  rw [List.append_assoc, readNat32_nat32 m.recipeId hrb]
  dsimp only
  rw [if_pos hr]
  rw [readNat64_nat64 m.totalBytes ht]
  dsimp only
  rw [readNat32_nat32_nil m.leafCount hl]

/-- Exactness: a successful decode's input IS the canonical encoding
of its result, fields representable and the recipe registered. -/
theorem decodeManifest_exact (bytes : List UInt8) (m : ManifestContent)
    (h : decodeManifest? bytes = some m) :
    bytes = encodeManifest m ∧ knownRecipes.contains m.recipeId ∧
      m.recipeId < 4294967296 ∧
      m.totalBytes < 18446744073709551616 ∧ m.leafCount < 4294967296 := by
  unfold decodeManifest? at h
  split at h
  · exact nomatch h
  · rename_i recipeId r1 hr1
    split at h
    · rename_i hknown
      split at h
      · exact nomatch h
      · rename_i totalBytes r2 hr2
        split at h
        · rename_i leafCount hr3
          injection h with h
          obtain ⟨hb1, hlt1⟩ := readNat32_some bytes recipeId r1 hr1
          obtain ⟨hb2, hlt2⟩ := readNat64_some r1 totalBytes r2 hr2
          obtain ⟨hb3, hlt3⟩ := readNat32_some r2 leafCount [] hr3
          subst h
          refine ⟨?_, hknown, hlt1, hlt2, hlt3⟩
          rw [hb1, hb2, hb3]
          simp [encodeManifest]
        · exact nomatch h
    · exact nomatch h

end Effects.Merkle
