import Effects.Merkle.Tree

/-!
# The inclusion verifier

The verifier receives the index, the total chunk count, the leaf bytes,
the sibling list (root-side first), and the expected root. Sides are
DERIVED from the index and the count by the same standards split the
tree uses — the adversary controls sibling values only, which is what
makes binding provable: two accepted openings of one root and index
walk the same spine, so their pre-images can be compared level by
level, and the first disagreement is a hash collision.

Three theorems, per the ratified statement architecture: the reflection
iff (the executable check accepts exactly the recomputation judgment),
completeness (honestly generated paths verify — no hypotheses beyond
index bounds), and binding extraction (two accepted openings agree on
their bytes or exhibit a collision; composed with completeness this
binds every accepted opening to the committed chunk at its index —
LambdaAuth's lesson stands: nothing here claims the verifier DETECTS a
collision).
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

variable {A : Type}

/-- Recompute the root from an opening, deriving sides from the index
and the count. Root-side sibling first; `none` when the sibling count
disagrees with the tree geometry. -/
def branchRoot (P : HP A) (base m n : Nat) (bytes : Bytes) :
    List A → Option A
  | [] => if n ≤ 1 then some (P.H (.leaf base bytes)) else none
  | s :: rest =>
    if n ≤ 1 then none
    else
      if m < pow2Below n then
        (branchRoot P base m (pow2Below n) bytes rest).map
          (fun v => P.H (.parent v s))
      else
        (branchRoot P (base + pow2Below n) (m - pow2Below n)
            (n - pow2Below n) bytes rest).map
          (fun v => P.H (.parent s v))

/-- The inclusion judgment: the index is in range and the recomputed
root is exactly the expected one. -/
def InclusionOk (P : HP A) (m n : Nat) (bytes : Bytes)
    (sibs : List A) (r : A) : Prop :=
  m < n ∧ branchRoot P 0 m n bytes sibs = some r

instance [DecidableEq A] (P : HP A) (m n : Nat) (bytes : Bytes)
    (sibs : List A) (r : A) : Decidable (InclusionOk P m n bytes sibs r) := by
  unfold InclusionOk
  infer_instance

/-- The executable inclusion verifier. -/
def verifyInclusion [DecidableEq A] (P : HP A) (m n : Nat) (bytes : Bytes)
    (sibs : List A) (r : A) : Bool :=
  decide (m < n) && decide (branchRoot P 0 m n bytes sibs = some r)

/-- Reflection: the executable check accepts exactly the judgment. -/
theorem verifyInclusion_iff [DecidableEq A] (P : HP A) (m n : Nat)
    (bytes : Bytes) (sibs : List A) (r : A) :
    verifyInclusion P m n bytes sibs r = true ↔
      InclusionOk P m n bytes sibs r := by
  simp [verifyInclusion, InclusionOk]

/-- Completeness: an honestly generated path verifies — the recomputed
root of `(chunks[m], genPath m)` is the tree root, with no hypotheses
beyond the index bound. -/
theorem branchRoot_genPath (P : HP A) (base m : Nat) (chunks : List Bytes)
    (hm : m < chunks.length) :
    branchRoot P base m chunks.length chunks[m]
      (genPath P base m chunks) = some (root P base chunks) := by
  match chunks, hm with
  | [c], hm =>
    simp [genPath, branchRoot, root]
  | c₁ :: c₂ :: cs, hm =>
    have h1 : ¬ (c₁ :: c₂ :: cs).length ≤ 1 := by simp
    have h2 : 2 ≤ (c₁ :: c₂ :: cs).length := by simp
    have hk_lt := pow2Below_lt (c₁ :: c₂ :: cs).length h2
    have hk_pos := pow2Below_pos (c₁ :: c₂ :: cs).length
    by_cases hmk : m < pow2Below (c₁ :: c₂ :: cs).length
    · rw [genPath_split_pos P base m _ h1 hmk, root_split P base _ h1]
      have hm_take :
          m < ((c₁ :: c₂ :: cs).take (pow2Below (c₁ :: c₂ :: cs).length)).length := by
        simp only [List.length_take]
        omega
      have ih := branchRoot_genPath P base m
        ((c₁ :: c₂ :: cs).take (pow2Below (c₁ :: c₂ :: cs).length)) hm_take
      have htake_len :
          ((c₁ :: c₂ :: cs).take (pow2Below (c₁ :: c₂ :: cs).length)).length =
            pow2Below (c₁ :: c₂ :: cs).length := by
        simp only [List.length_take]
        omega
      have hgetTake :
          ((c₁ :: c₂ :: cs).take (pow2Below (c₁ :: c₂ :: cs).length))[m]'hm_take =
            (c₁ :: c₂ :: cs)[m] := by
        simp
      rw [htake_len, hgetTake] at ih
      simp only [branchRoot, if_neg h1, if_pos hmk, ih, Option.map_some]
    · rw [genPath_split_neg P base m _ h1 hmk, root_split P base _ h1]
      have hm_drop :
          m - pow2Below (c₁ :: c₂ :: cs).length <
            ((c₁ :: c₂ :: cs).drop (pow2Below (c₁ :: c₂ :: cs).length)).length := by
        simp only [List.length_drop]
        omega
      have ih := branchRoot_genPath P (base + pow2Below (c₁ :: c₂ :: cs).length)
        (m - pow2Below (c₁ :: c₂ :: cs).length)
        ((c₁ :: c₂ :: cs).drop (pow2Below (c₁ :: c₂ :: cs).length)) hm_drop
      have hdrop_len :
          ((c₁ :: c₂ :: cs).drop (pow2Below (c₁ :: c₂ :: cs).length)).length =
            (c₁ :: c₂ :: cs).length - pow2Below (c₁ :: c₂ :: cs).length := by
        simp only [List.length_drop]
      have hgetDrop :
          ((c₁ :: c₂ :: cs).drop (pow2Below (c₁ :: c₂ :: cs).length))[
              m - pow2Below (c₁ :: c₂ :: cs).length]'hm_drop =
            (c₁ :: c₂ :: cs)[m] := by
        rw [List.getElem_drop]
        congr 1
        omega
      rw [hdrop_len, hgetDrop] at ih
      simp only [branchRoot, if_neg h1, if_neg hmk, ih, Option.map_some]
termination_by chunks.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- Binding extraction: two accepted openings of one root at one index
carry the same bytes, or two distinct pre-images with one address are
exhibited. Constructive: the proof walks both spines from the root and
compares pre-images level by level. -/
theorem branchRoot_bind [DecidableEq A] (P : HP A) :
    ∀ (s₁ s₂ : List A) (base m n : Nat) (b₁ b₂ : Bytes) (r : A),
      branchRoot P base m n b₁ s₁ = some r →
      branchRoot P base m n b₂ s₂ = some r →
      b₁ = b₂ ∨ Collision P
  | [], [], base, m, n, b₁, b₂, r, h₁, h₂ => by
    simp only [branchRoot] at h₁ h₂
    split at h₁
    · rename_i hn
      rw [if_pos hn] at h₂
      injection h₁ with h₁
      injection h₂ with h₂
      by_cases hb : b₁ = b₂
      · exact Or.inl hb
      · exact Or.inr ⟨.leaf base b₁, .leaf base b₂,
          by simp [hb], h₁.trans h₂.symm⟩
    · exact nomatch h₁
  | [], s :: rest, base, m, n, b₁, b₂, r, h₁, h₂ => by
    simp only [branchRoot] at h₁ h₂
    split at h₁
    · rename_i hn
      rw [if_pos hn] at h₂
      exact nomatch h₂
    · exact nomatch h₁
  | s :: rest, [], base, m, n, b₁, b₂, r, h₁, h₂ => by
    simp only [branchRoot] at h₁ h₂
    split at h₂
    · rename_i hn
      rw [if_pos hn] at h₁
      exact nomatch h₁
    · exact nomatch h₂
  | a :: r₁, c :: r₂, base, m, n, b₁, b₂, r, h₁, h₂ => by
    simp only [branchRoot] at h₁ h₂
    split at h₁
    · exact nomatch h₁
    · rename_i hn
      rw [if_neg hn] at h₂
      by_cases hmk : m < pow2Below n
      · rw [if_pos hmk] at h₁ h₂
        obtain ⟨v₁, hv₁, hr₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨v₂, hv₂, hr₂⟩ := Option.map_eq_some_iff.mp h₂
        by_cases hpre : (Pre.parent v₁ a : Pre A) = .parent v₂ c
        · injection hpre with hv hc
          subst hv
          exact branchRoot_bind P r₁ r₂ base m (pow2Below n) b₁ b₂ v₁ hv₁ hv₂
        · exact Or.inr ⟨.parent v₁ a, .parent v₂ c, hpre,
            hr₁.trans hr₂.symm⟩
      · rw [if_neg hmk] at h₁ h₂
        obtain ⟨v₁, hv₁, hr₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨v₂, hv₂, hr₂⟩ := Option.map_eq_some_iff.mp h₂
        by_cases hpre : (Pre.parent a v₁ : Pre A) = .parent c v₂
        · injection hpre with hc hv
          subst hv
          exact branchRoot_bind P r₁ r₂ (base + pow2Below n) (m - pow2Below n)
            (n - pow2Below n) b₁ b₂ v₁ hv₁ hv₂
        · exact Or.inr ⟨.parent a v₁, .parent c v₂, hpre,
            hr₁.trans hr₂.symm⟩

/-- Every accepted opening binds its index's committed chunk: the
accepted bytes equal the chunk the tree commits at that index, or a
collision is exhibited. Composed from completeness and binding; this is
the position-binding law — a proof replayed at another index can never
make a position serve bytes its leaf does not hold. -/
theorem opening_binds_committed [DecidableEq A] (P : HP A)
    (chunks : List Bytes) (m : Nat) (hm : m < chunks.length)
    (b : Bytes) (sibs : List A) (r : A)
    (hacc : branchRoot P 0 m chunks.length b sibs = some r)
    (hroot : root P 0 chunks = r) :
    b = chunks[m] ∨ Collision P :=
  branchRoot_bind P sibs (genPath P 0 m chunks) 0 m chunks.length b chunks[m]
    r hacc (by rw [branchRoot_genPath P 0 m chunks hm, hroot])

end Effects.Merkle
