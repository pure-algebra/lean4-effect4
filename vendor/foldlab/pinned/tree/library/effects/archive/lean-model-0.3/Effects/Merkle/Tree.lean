import Effects.Merkle.Chunk

/-!
# The chunk tree — structural pre-images over an abstract address

Domain separation and position binding are STRUCTURAL at this altitude:
a pre-image is either a leaf carrying its absolute chunk index and bytes,
or a parent carrying two child addresses — constructor identity separates
the domains, the index field binds the position. Byte-prefix realization
(the 0x00/0x01 discipline) belongs to the codec layer with exactness
proofs, exactly like the node codec.

The root recursion is the standards split: the left subtree takes the
largest power of two strictly below the chunk count (RFC 9162's `k`,
which is also the BLAKE3/bao split), so one tree shape serves both the
proof formats and the streaming layout. The hash is an abstract
function of pre-images; no theorem anywhere assumes it collision-free —
collision cases surface as explicit witnesses.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

/-- A structural pre-image: a leaf with its absolute index and bytes, or
a parent with two child addresses. Constructor identity IS the domain
separation; the index field IS the position binding. -/
inductive Pre (A : Type) where
  | leaf (index : Nat) (bytes : Bytes)
  | parent (left right : A)
  deriving DecidableEq

/-- The abstract address function over pre-images. -/
structure HP (A : Type) where
  H : Pre A → A

/-- A hash collision: two distinct pre-images with one address. Every
law that would need collision resistance carries this as an explicit
disjunct instead. -/
def Collision {A : Type} (P : HP A) : Prop :=
  ∃ p q : Pre A, p ≠ q ∧ P.H p = P.H q

/-- The largest power of two strictly below `n`, for `n ≥ 2` (returns 1
below that): the standards split point. -/
def pow2Below (n : Nat) : Nat :=
  if n ≤ 2 then 1 else 2 * pow2Below ((n + 1) / 2)
termination_by n
decreasing_by omega

theorem pow2Below_pos (n : Nat) : 0 < pow2Below n := by
  unfold pow2Below
  split
  · exact Nat.one_pos
  · have := pow2Below_pos ((n + 1) / 2)
    omega
termination_by n
decreasing_by omega

theorem pow2Below_lt (n : Nat) (h : 2 ≤ n) : pow2Below n < n := by
  unfold pow2Below
  split
  · omega
  · rename_i hgt
    have hrec : pow2Below ((n + 1) / 2) < (n + 1) / 2 :=
      pow2Below_lt ((n + 1) / 2) (by omega)
    omega
termination_by n
decreasing_by omega

variable {A : Type}

/-- The chunk-tree root over a chunk list, with `base` the absolute
index of the first chunk. A single (or empty) list is a leaf; otherwise
the standards split. -/
def root (P : HP A) (base : Nat) (chunks : List Bytes) : A :=
  if _h : chunks.length ≤ 1 then P.H (.leaf base (chunks.headD []))
  else
    P.H (.parent (root P base (chunks.take (pow2Below chunks.length)))
                 (root P (base + pow2Below chunks.length)
                        (chunks.drop (pow2Below chunks.length))))
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

/-- One-sided split equation for the root at two or more chunks. -/
theorem root_split (P : HP A) (base : Nat) (chunks : List Bytes)
    (h : ¬ chunks.length ≤ 1) :
    root P base chunks =
      P.H (.parent (root P base (chunks.take (pow2Below chunks.length)))
                   (root P (base + pow2Below chunks.length)
                          (chunks.drop (pow2Below chunks.length)))) := by
  conv => lhs; rw [root.eq_def]
  rw [dif_neg h]

/-- The inclusion path for index `m`, root-side sibling first. Sides are
NOT stored: the verifier derives them from the index and the count, so
an adversary controls sibling values only — the discipline that makes
binding provable. -/
def genPath (P : HP A) (base m : Nat) (chunks : List Bytes) : List A :=
  if _h : chunks.length ≤ 1 then []
  else
    if m < pow2Below chunks.length then
      root P (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) ::
        genPath P base m (chunks.take (pow2Below chunks.length))
    else
      root P base (chunks.take (pow2Below chunks.length)) ::
        genPath P (base + pow2Below chunks.length)
          (m - pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length))
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

/-- One-sided split equations for the path at two or more chunks. -/
theorem genPath_split_pos (P : HP A) (base m : Nat) (chunks : List Bytes)
    (h : ¬ chunks.length ≤ 1) (hm : m < pow2Below chunks.length) :
    genPath P base m chunks =
      root P (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) ::
        genPath P base m (chunks.take (pow2Below chunks.length)) := by
  conv => lhs; rw [genPath.eq_def]
  rw [dif_neg h, if_pos hm]

theorem genPath_split_neg (P : HP A) (base m : Nat) (chunks : List Bytes)
    (h : ¬ chunks.length ≤ 1) (hm : ¬ m < pow2Below chunks.length) :
    genPath P base m chunks =
      root P base (chunks.take (pow2Below chunks.length)) ::
        genPath P (base + pow2Below chunks.length)
          (m - pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) := by
  conv => lhs; rw [genPath.eq_def]
  rw [dif_neg h, if_neg hm]

end Effects.Merkle
