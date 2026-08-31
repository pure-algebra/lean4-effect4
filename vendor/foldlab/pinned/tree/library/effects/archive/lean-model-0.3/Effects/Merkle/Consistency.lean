import Effects.Merkle.Verify

/-!
# The consistency verifier

RFC 9162's subproof shape over the standards split: a consistency
proof relates the root of the first `m` chunks to the root of all `n`,
`1 ≤ m < n`. The verifier DERIVES the whole walk from the two sizes —
the proof is a bare hash list consumed linearly down one spine, one
sibling per level plus a terminal, so an adversary controls hash
values only, never the shape, exactly as the inclusion verifier's
discipline demands.

The anchored flag is RFC 9162's `b`: while the descent stays on left
subtrees the old tree is a left spine of the new one and its root is
the caller's input, not a proof element; the first rightward step
clears the flag and the old root is thereafter reconstructed from
proof hashes and checked. The mathematical heart is the shared split
point: when the old size exceeds the new tree's split, both trees
split at the SAME power of two (`pow2Below_between`), which is what
lets one proof serve both recomputations.

Three theorems, per the ratified statement architecture: the
reflection iff, completeness (an honestly generated proof relates the
committed prefix root to the whole root, no hypotheses beyond the
bounds), and the prefix-agreement corollary (an accepted proof
against an honest new tree forces the old root to BE the committed
prefix's root, or two distinct pre-images with one address are
exhibited — never a collision-resistance axiom).
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

variable {A : Type}

private theorem list_take_take {α : Type _} :
    ∀ (xs : List α) (m n : Nat), m ≤ n → (xs.take n).take m = xs.take m
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | x :: xs, m + 1, n + 1, h => by
    simp only [List.take_succ_cons, List.cons.injEq, true_and]
    exact list_take_take xs m n (by omega)

private theorem list_drop_take {α : Type _} :
    ∀ (xs : List α) (n m : Nat), (xs.take n).drop m = (xs.drop m).take (n - m)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: _, n + 1, 0 => by simp
  | _ :: xs, n + 1, m + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons,
      Nat.add_sub_add_right]
    exact list_drop_take xs n m

/-! ## The shared split point -/

/-- One-sided recursion equation for the split point. -/
theorem pow2Below_rec (n : Nat) (h : ¬ n ≤ 2) :
    pow2Below n = 2 * pow2Below ((n + 1) / 2) := by
  conv => lhs; rw [pow2Below.eq_def]
  rw [if_neg h]

/-- Between the split point and the total, the split point is stable:
both the prefix tree and the whole tree split at the same power of
two. RFC 9162's consistency algorithm is built on exactly this. -/
theorem pow2Below_between : ∀ n m : Nat, pow2Below n < m → m < n →
    pow2Below m = pow2Below n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m h1 h2
    have hp := pow2Below_pos n
    have hn3 : 3 ≤ n := by omega
    have hrecn : pow2Below n = 2 * pow2Below ((n + 1) / 2) :=
      pow2Below_rec n (by omega)
    have hp2 : 2 ≤ pow2Below n := by
      rw [hrecn]
      have := pow2Below_pos ((n + 1) / 2)
      omega
    have hrecm : pow2Below m = 2 * pow2Below ((m + 1) / 2) :=
      pow2Below_rec m (by omega)
    rw [hrecm, hrecn]
    by_cases heq : (m + 1) / 2 = (n + 1) / 2
    · rw [heq]
    · have hgt : pow2Below ((n + 1) / 2) < (m + 1) / 2 := by
        rw [hrecn] at h1
        omega
      have := ih ((n + 1) / 2) (by omega) ((m + 1) / 2) hgt (by omega)
      rw [this]

/-- The characterization the split point's name promises and the
RFC 9162/BLAKE3 interop claim rests on: it is a power of two,
strictly below the total, with the total at most its double. -/
theorem pow2Below_spec : ∀ n : Nat, 2 ≤ n →
    ∃ k, pow2Below n = 2 ^ k ∧ 2 ^ k < n ∧ n ≤ 2 ^ (k + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h2
    by_cases hle : n ≤ 2
    · refine ⟨0, ?_, ?_, ?_⟩
      · rw [pow2Below.eq_def, if_pos hle]
      · have h1 : (2 : Nat) ^ 0 = 1 := rfl
        omega
      · have h1 : (2 : Nat) ^ 1 = 2 := rfl
        omega
    · have hrec := pow2Below_rec n hle
      obtain ⟨k, hk, hlt, hup⟩ := ih ((n + 1) / 2) (by omega) (by omega)
      have hp1 : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hp2 : (2 : Nat) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      refine ⟨k + 1, ?_, ?_, ?_⟩
      · rw [hrec, hk, hp1]
      · omega
      · omega

/-- The prefix tree's split equation: past the shared split point, the
prefix root is the parent of the shared left subtree and the prefix of
the right subtree. -/
theorem root_take_split (P : HP A) (base m : Nat) (chunks : List Bytes)
    (hk : pow2Below chunks.length < m) (hm : m < chunks.length) :
    root P base (chunks.take m) =
      P.H (.parent
        (root P base (chunks.take (pow2Below chunks.length)))
        (root P (base + pow2Below chunks.length)
          ((chunks.drop (pow2Below chunks.length)).take
            (m - pow2Below chunks.length)))) := by
  have hp := pow2Below_pos chunks.length
  have hlen : (chunks.take m).length = m := by
    simp only [List.length_take]
    omega
  have h2 : ¬ (chunks.take m).length ≤ 1 := by omega
  rw [root_split P base (chunks.take m) h2]
  rw [hlen, pow2Below_between chunks.length m hk hm]
  rw [list_take_take chunks (pow2Below chunks.length) m (by omega)]
  rw [list_drop_take chunks m (pow2Below chunks.length)]

/-! ## The verifier -/

/-- Rebuild the old and new roots from a consistency proof, root-side
sibling first, the whole walk derived from the sizes. `anchored` is
RFC 9162's `b`: while true, the old root is `oldAnchor` and no proof
element carries it; the first rightward step clears it. The list is
consumed exactly — a missing or trailing element is `none`. -/
def consRebuild (P : HP A) (oldAnchor : A) (m n : Nat) (anchored : Bool)
    (hs : List A) : Option (A × A) :=
  if n ≤ m then
    match anchored, hs with
    | true, [] => some (oldAnchor, oldAnchor)
    | false, [h] => some (h, h)
    | _, _ => none
  else if n ≤ 1 then none
  else
    match hs with
    | [] => none
    | h :: rest =>
      if m ≤ pow2Below n then
        (consRebuild P oldAnchor m (pow2Below n) anchored rest).map
          (fun p => (p.1, P.H (.parent p.2 h)))
      else
        (consRebuild P oldAnchor (m - pow2Below n) (n - pow2Below n) false
            rest).map
          (fun p => (P.H (.parent h p.1), P.H (.parent h p.2)))
termination_by n
decreasing_by
  · exact pow2Below_lt n (by omega)
  · have := pow2Below_pos n
    omega

/-- One-sided terminal equation. -/
theorem consRebuild_terminal (P : HP A) (oldAnchor : A) (m n : Nat)
    (anchored : Bool) (hs : List A) (h : n ≤ m) :
    consRebuild P oldAnchor m n anchored hs =
      match anchored, hs with
      | true, [] => some (oldAnchor, oldAnchor)
      | false, [h] => some (h, h)
      | _, _ => none := by
  conv => lhs; rw [consRebuild.eq_def]
  rw [if_pos h]

/-- One-sided equation: a parent level with no proof element left. -/
theorem consRebuild_nil (P : HP A) (oldAnchor : A) (m n : Nat)
    (anchored : Bool) (h1 : ¬ n ≤ m) (h2 : ¬ n ≤ 1) :
    consRebuild P oldAnchor m n anchored [] = none := by
  conv => lhs; rw [consRebuild.eq_def]
  rw [if_neg h1, if_neg h2]

/-- One-sided equation for the left descent. -/
theorem consRebuild_left (P : HP A) (oldAnchor : A) (m n : Nat)
    (anchored : Bool) (h : A) (rest : List A)
    (h1 : ¬ n ≤ m) (h2 : ¬ n ≤ 1) (hm : m ≤ pow2Below n) :
    consRebuild P oldAnchor m n anchored (h :: rest) =
      (consRebuild P oldAnchor m (pow2Below n) anchored rest).map
        (fun p => (p.1, P.H (.parent p.2 h))) := by
  conv => lhs; rw [consRebuild.eq_def]
  rw [if_neg h1, if_neg h2]
  dsimp only
  rw [if_pos hm]

/-- One-sided equation for the right descent. -/
theorem consRebuild_right (P : HP A) (oldAnchor : A) (m n : Nat)
    (anchored : Bool) (h : A) (rest : List A)
    (h1 : ¬ n ≤ m) (h2 : ¬ n ≤ 1) (hm : ¬ m ≤ pow2Below n) :
    consRebuild P oldAnchor m n anchored (h :: rest) =
      (consRebuild P oldAnchor (m - pow2Below n) (n - pow2Below n) false
          rest).map
        (fun p => (P.H (.parent h p.1), P.H (.parent h p.2))) := by
  conv => lhs; rw [consRebuild.eq_def]
  rw [if_neg h1, if_neg h2]
  dsimp only
  rw [if_neg hm]

/-- The consistency judgment: the sizes are in range and the rebuild
reproduces exactly the two expected roots with the proof exactly
consumed. Equal sizes need no proof — root equality is definitional —
so the judgment covers `1 ≤ m < n`. -/
def ConsistencyOk (P : HP A) (m n : Nat) (oldRoot newRoot : A)
    (proof : List A) : Prop :=
  1 ≤ m ∧ m < n ∧
    consRebuild P oldRoot m n true proof = some (oldRoot, newRoot)

instance [DecidableEq A] (P : HP A) (m n : Nat) (oldRoot newRoot : A)
    (proof : List A) : Decidable (ConsistencyOk P m n oldRoot newRoot proof) := by
  unfold ConsistencyOk
  infer_instance

/-- The executable consistency verifier. -/
def verifyConsistency [DecidableEq A] (P : HP A) (m n : Nat)
    (oldRoot newRoot : A) (proof : List A) : Bool :=
  decide (1 ≤ m) && decide (m < n) &&
    decide (consRebuild P oldRoot m n true proof = some (oldRoot, newRoot))

/-- Reflection: the executable check accepts exactly the judgment. -/
theorem verifyConsistency_iff [DecidableEq A] (P : HP A) (m n : Nat)
    (oldRoot newRoot : A) (proof : List A) :
    verifyConsistency P m n oldRoot newRoot proof = true ↔
      ConsistencyOk P m n oldRoot newRoot proof := by
  simp [verifyConsistency, ConsistencyOk, and_assoc]

/-! ## The honest generator and completeness -/

/-- Generate the consistency proof from the new chunk list, root-side
sibling first, mirroring the rebuild's walk. -/
def genConsProof (P : HP A) (base m : Nat) (chunks : List Bytes)
    (anchored : Bool) : List A :=
  if chunks.length ≤ m then
    if anchored then [] else [root P base chunks]
  else if chunks.length ≤ 1 then []
  else
    if m ≤ pow2Below chunks.length then
      root P (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) ::
        genConsProof P base m (chunks.take (pow2Below chunks.length))
          anchored
    else
      root P base (chunks.take (pow2Below chunks.length)) ::
        genConsProof P (base + pow2Below chunks.length)
          (m - pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) false
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

theorem genConsProof_terminal (P : HP A) (base m : Nat)
    (chunks : List Bytes) (anchored : Bool) (h : chunks.length ≤ m) :
    genConsProof P base m chunks anchored =
      if anchored then [] else [root P base chunks] := by
  conv => lhs; rw [genConsProof.eq_def]
  rw [if_pos h]

theorem genConsProof_left (P : HP A) (base m : Nat) (chunks : List Bytes)
    (anchored : Bool) (h1 : ¬ chunks.length ≤ m)
    (h2 : ¬ chunks.length ≤ 1) (hm : m ≤ pow2Below chunks.length) :
    genConsProof P base m chunks anchored =
      root P (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) ::
        genConsProof P base m (chunks.take (pow2Below chunks.length))
          anchored := by
  conv => lhs; rw [genConsProof.eq_def]
  rw [if_neg h1, if_neg h2, if_pos hm]

theorem genConsProof_right (P : HP A) (base m : Nat) (chunks : List Bytes)
    (anchored : Bool) (h1 : ¬ chunks.length ≤ m)
    (h2 : ¬ chunks.length ≤ 1) (hm : ¬ m ≤ pow2Below chunks.length) :
    genConsProof P base m chunks anchored =
      root P base (chunks.take (pow2Below chunks.length)) ::
        genConsProof P (base + pow2Below chunks.length)
          (m - pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) false := by
  conv => lhs; rw [genConsProof.eq_def]
  rw [if_neg h1, if_neg h2, if_neg hm]

/-- Completeness of the rebuild against the honest generator: the
reconstruction yields exactly the prefix root and the whole root. -/
theorem consRebuild_genConsProof (P : HP A) :
    ∀ (chunks : List Bytes) (base m : Nat) (anchored : Bool)
      (oldAnchor : A),
      1 ≤ m → m ≤ chunks.length →
      (anchored = true → oldAnchor = root P base (chunks.take m)) →
      consRebuild P oldAnchor m chunks.length anchored
          (genConsProof P base m chunks anchored) =
        some (root P base (chunks.take m), root P base chunks) := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro base m anchored oldAnchor hm hmle hanch
  subst hn
  by_cases hnm : chunks.length ≤ m
  · have htake : chunks.take m = chunks := List.take_of_length_le hnm
    rw [genConsProof_terminal P base m chunks anchored hnm]
    cases anchored with
    | true =>
      rw [if_pos rfl,
        consRebuild_terminal P oldAnchor m chunks.length true [] hnm]
      rw [hanch rfl, htake]
    | false =>
      rw [if_neg (by simp),
        consRebuild_terminal P oldAnchor m chunks.length false _ hnm]
      rw [htake]
  · have hlt : m < chunks.length := by omega
    have h2 : ¬ chunks.length ≤ 1 := by omega
    have hk_lt := pow2Below_lt chunks.length (by omega)
    have hk_pos := pow2Below_pos chunks.length
    have htake_len :
        (chunks.take (pow2Below chunks.length)).length =
          pow2Below chunks.length := by
      simp only [List.length_take]
      omega
    have hdrop_len :
        (chunks.drop (pow2Below chunks.length)).length =
          chunks.length - pow2Below chunks.length := by
      simp only [List.length_drop]
    by_cases hmk : m ≤ pow2Below chunks.length
    · rw [genConsProof_left P base m chunks anchored hnm h2 hmk,
        consRebuild_left P oldAnchor m chunks.length anchored _ _ hnm h2 hmk]
      have hih := ih (pow2Below chunks.length) (by omega)
        (chunks.take (pow2Below chunks.length)) htake_len base m anchored
        oldAnchor hm (by omega)
        (by
          intro ha
          rw [hanch ha,
            list_take_take chunks m (pow2Below chunks.length) hmk])
      rw [hih]
      simp only [Option.map_some]
      rw [list_take_take chunks m (pow2Below chunks.length) hmk,
        root_split P base chunks (by omega)]
    · rw [genConsProof_right P base m chunks anchored hnm h2 hmk,
        consRebuild_right P oldAnchor m chunks.length anchored _ _ hnm h2 hmk]
      have hih := ih (chunks.length - pow2Below chunks.length) (by omega)
        (chunks.drop (pow2Below chunks.length)) hdrop_len
        (base + pow2Below chunks.length) (m - pow2Below chunks.length)
        false oldAnchor (by omega) (by omega)
        (by intro ha; exact absurd ha (by simp))
      rw [hih]
      simp only [Option.map_some]
      rw [root_take_split P base m chunks (by omega) hlt,
        root_split P base chunks (by omega)]

/-- Completeness at the judgment: an honestly generated proof relates
the committed prefix root to the whole root. -/
theorem consistency_complete (P : HP A) (chunks : List Bytes) (m : Nat)
    (hm : 1 ≤ m) (hlt : m < chunks.length) :
    ConsistencyOk P m chunks.length (root P 0 (chunks.take m))
      (root P 0 chunks) (genConsProof P 0 m chunks true) :=
  ⟨hm, hlt,
    consRebuild_genConsProof P chunks 0 m true _ hm (by omega)
      (fun _ => rfl)⟩

/-! ## The prefix-agreement corollary -/

/-- Binding: any rebuild that reproduces an honest whole root pins its
old component to the committed prefix root, or two distinct pre-images
with one address are exhibited. The proof walks the rebuild's spine
against the tree, comparing pre-images level by level. -/
theorem consRebuild_bind (P : HP A) :
    ∀ (chunks : List Bytes) (hs : List A) (base m : Nat) (anchored : Bool)
      (oldAnchor o : A),
      1 ≤ m → m ≤ chunks.length →
      consRebuild P oldAnchor m chunks.length anchored hs =
        some (o, root P base chunks) →
      o = root P base (chunks.take m) ∨ Collision P := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro hs base m anchored oldAnchor o hm hmle hreb
  subst hn
  by_cases hnm : chunks.length ≤ m
  · have htake : chunks.take m = chunks := List.take_of_length_le hnm
    rw [consRebuild_terminal P oldAnchor m chunks.length anchored hs hnm]
      at hreb
    cases anchored with
    | true =>
      cases hs with
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hreb
        rw [htake]
        exact Or.inl (hreb.1.symm.trans hreb.2)
      | cons h t => exact nomatch hreb
    | false =>
      cases hs with
      | nil => exact nomatch hreb
      | cons h t =>
        cases t with
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hreb
          rw [htake]
          exact Or.inl (hreb.1.symm.trans hreb.2)
        | cons h' t' => exact nomatch hreb
  · have hlt : m < chunks.length := by omega
    have h2 : ¬ chunks.length ≤ 1 := by omega
    have hk_lt := pow2Below_lt chunks.length (by omega)
    have hk_pos := pow2Below_pos chunks.length
    have htake_len :
        (chunks.take (pow2Below chunks.length)).length =
          pow2Below chunks.length := by
      simp only [List.length_take]
      omega
    have hdrop_len :
        (chunks.drop (pow2Below chunks.length)).length =
          chunks.length - pow2Below chunks.length := by
      simp only [List.length_drop]
    cases hs with
    | nil =>
      rw [consRebuild_nil P oldAnchor m chunks.length anchored hnm h2] at hreb
      exact nomatch hreb
    | cons h rest =>
      by_cases hmk : m ≤ pow2Below chunks.length
      · rw [consRebuild_left P oldAnchor m chunks.length anchored h rest
          hnm h2 hmk] at hreb
        obtain ⟨p, hp, hpair⟩ := Option.map_eq_some_iff.mp hreb
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨ho, hnew⟩ := hpair
        rw [root_split P base chunks (by omega)] at hnew
        by_cases hpre : (Pre.parent p.2 h : Pre A) =
            .parent (root P base (chunks.take (pow2Below chunks.length)))
              (root P (base + pow2Below chunks.length)
                (chunks.drop (pow2Below chunks.length)))
        · injection hpre with hl hr
          have hp' : consRebuild P oldAnchor m (pow2Below chunks.length)
              anchored rest =
                some (p.1, root P base
                  (chunks.take (pow2Below chunks.length))) := by
            rw [hp, ← hl]
          have := ih (pow2Below chunks.length) (by omega)
            (chunks.take (pow2Below chunks.length)) htake_len rest base m
            anchored oldAnchor p.1 hm (by omega) hp'
          rw [list_take_take chunks m (pow2Below chunks.length) hmk] at this
          rcases this with heq | hc
          · exact Or.inl (ho ▸ heq)
          · exact Or.inr hc
        · exact Or.inr ⟨_, _, hpre, hnew⟩
      · rw [consRebuild_right P oldAnchor m chunks.length anchored h rest
          hnm h2 hmk] at hreb
        obtain ⟨p, hp, hpair⟩ := Option.map_eq_some_iff.mp hreb
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨ho, hnew⟩ := hpair
        rw [root_split P base chunks (by omega)] at hnew
        by_cases hpre : (Pre.parent h p.2 : Pre A) =
            .parent (root P base (chunks.take (pow2Below chunks.length)))
              (root P (base + pow2Below chunks.length)
                (chunks.drop (pow2Below chunks.length)))
        · injection hpre with hl hr
          have hp' : consRebuild P oldAnchor (m - pow2Below chunks.length)
              (chunks.length - pow2Below chunks.length) false rest =
                some (p.1, root P (base + pow2Below chunks.length)
                  (chunks.drop (pow2Below chunks.length))) := by
            rw [hp, ← hr]
          have := ih (chunks.length - pow2Below chunks.length) (by omega)
            (chunks.drop (pow2Below chunks.length)) hdrop_len rest
            (base + pow2Below chunks.length) (m - pow2Below chunks.length)
            false oldAnchor p.1 (by omega) (by omega) hp'
          rcases this with heq | hc
          · refine Or.inl ?_
            rw [← ho, hl, heq,
              root_take_split P base m chunks (by omega) hlt]
          · exact Or.inr hc
        · exact Or.inr ⟨_, _, hpre, hnew⟩

/-- Prefix agreement: an accepted consistency proof against an honest
new tree forces the old root to be the committed prefix's root, or
exhibits a collision. Composed with completeness this binds every
accepted old root to the prefix the new tree actually commits. -/
theorem consistency_binds_prefix (P : HP A) (chunks : List Bytes)
    (m : Nat) (oldRoot : A) (proof : List A)
    (hok : ConsistencyOk P m chunks.length oldRoot (root P 0 chunks)
      proof) :
    oldRoot = root P 0 (chunks.take m) ∨ Collision P :=
  consRebuild_bind P chunks proof 0 m true oldRoot oldRoot hok.1
    (Nat.le_of_lt hok.2.1) hok.2.2

end Effects.Merkle
