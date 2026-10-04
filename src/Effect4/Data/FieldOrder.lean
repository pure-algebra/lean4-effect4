module

public import Std
import all Init.Data.String.Defs

/-!
# The canonical field order (decisions rows 119, 157, 165; probe P, question 1)

A record's fields, a record value's names and every per-field table built over a record are
ordered by one function: `canonBy key fs` sorts a field list by `ltKey` on the key of each field's
name and keeps the first occurrence of a repeated name. It is payload-polymorphic, so one function
orders field types (`Ty.normalize`), field checkers (the membership fold), field values and field
schemas, and `canonBy_map` says the order never looks at the payload. Every law is proved once for
any key function, injective where the law reads names; the instance the tree uses is `bytesKey`,
the name's UTF-8 bytes (`Ty.canon`).

The order is lexicographic on the bytes (`ltKey`), never `String`'s own `<`, which reaches
`Classical.choice` on this toolchain (the red control in `Test/Program/FieldOrder.lean`).

The formation refusal is `firstRepeated`, located at the list level and complete against the
judgment (`firstRepeated_eq_none_iff`): permutation invariance holds exactly on distinct names
(`canonBy_perm`; with a repeat the written order matters, the test's red control).

Ported from `docs/research/2026-10-01-type-language-probe/P/probes/P1FieldOrder.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Field

/-! ## The order on keys -/

/-- Lexicographic order on keys, as a Boolean. -/
def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

theorem ltKey_iff_lex (a b : List Nat) :
    ltKey a b = true ↔ List.Lex (· < ·) a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [ltKey]
  | cons a as ih =>
    cases b with
    | nil => simp [ltKey]
    | cons b bs =>
      rw [List.cons_lex_cons_iff]
      by_cases hab : a < b
      · simp [ltKey, hab]
      · by_cases hba : b < a
        · have hne : a ≠ b := by omega
          simp [ltKey, hab, hba, hne]
        · have he : a = b := by omega
          subst b
          simp [ltKey, ih]

theorem lex_trichotomy (a b : List Nat) :
    List.Lex (· < ·) a b ∨ a = b ∨ List.Lex (· < ·) b a := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b bs => exact Or.inl List.Lex.nil
  | cons a as ih =>
    cases b with
    | nil => exact Or.inr (Or.inr List.Lex.nil)
    | cons b bs =>
      by_cases hab : a < b
      · exact Or.inl (List.Lex.rel hab)
      · by_cases hba : b < a
        · exact Or.inr (Or.inr (List.Lex.rel hba))
        · have he : a = b := by omega
          subst b
          rcases ih bs with hab | he | hba
          · exact Or.inl (List.Lex.cons hab)
          · exact Or.inr (Or.inl (congrArg (List.cons a) he))
          · exact Or.inr (Or.inr (List.Lex.cons hba))

theorem ltKey_irrefl (a : List Nat) : ltKey a a = false := by
  cases h : ltKey a a with
  | false => rfl
  | true => exact absurd ((ltKey_iff_lex a a).mp h) (List.lex_irrefl Nat.lt_irrefl a)

theorem ltKey_trans {a b c : List Nat} (hab : ltKey a b = true) (hbc : ltKey b c = true) :
    ltKey a c = true :=
  (ltKey_iff_lex a c).mpr
    (List.lex_trans Nat.lt_trans ((ltKey_iff_lex a b).mp hab) ((ltKey_iff_lex b c).mp hbc))

theorem ltKey_asymm {a b : List Nat} (hab : ltKey a b = true) : ltKey b a = false := by
  cases h : ltKey b a with
  | false => rfl
  | true =>
    have := ltKey_trans hab h
    rw [ltKey_irrefl] at this
    exact Bool.noConfusion this

theorem ltKey_total {a b : List Nat} (hne : a ≠ b) (hab : ltKey a b = false) :
    ltKey b a = true := by
  rcases lex_trichotomy a b with h | h | h
  · rw [(ltKey_iff_lex a b).mpr h] at hab
    exact Bool.noConfusion hab
  · exact absurd h hne
  · exact (ltKey_iff_lex b a).mpr h

/-! ## The byte key -/

/-- A name's UTF-8 bytes: the key of the field order, and the bytes `Ty.key` reads for a string. -/
def bytesKey (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

theorem bytesKey_injective (a b : String) (h : bytesKey a = bytesKey b) : a = b := by
  have bytes : a.toUTF8.data.toList = b.toUTF8.data.toList :=
    List.map_inj_right (fun _ _ he => UInt8.toNat_inj.mp he) |>.mp h
  have arrays : a.toUTF8.data = b.toUTF8.data := Array.toList_inj.mp bytes
  apply String.toByteArray_inj.mp
  exact ByteArray.ext arrays

/-! ## The canonicalizer -/

section Canon

variable (key : String → List Nat)

/-- Insert a field by its name's key. A field whose name is already present stays, so a left
fold keeps the first occurrence of a repeated name. -/
def insertBy {β : Type} (p : String × β) : List (String × β) → List (String × β)
  | [] => [p]
  | q :: qs =>
    if ltKey (key p.1) (key q.1) = true then p :: q :: qs
    else if key p.1 = key q.1 then q :: qs
    else q :: insertBy p qs

/-- **The canonical field order**: ascending by the key of the name, the first occurrence of a
repeated name kept. Payload-polymorphic. -/
def canonBy {β : Type} (fs : List (String × β)) : List (String × β) :=
  fs.foldl (fun acc p => insertBy key p acc) []

/-- Strictly ascending by the key of the name. -/
def Ascending {β : Type} (l : List (String × β)) : Prop :=
  l.Pairwise (fun a b => ltKey (key a.1) (key b.1) = true)

variable {key}

theorem mem_insertBy {β : Type} {p x : String × β} {l : List (String × β)}
    (h : x ∈ insertBy key p l) : x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [insertBy, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    unfold insertBy at h
    by_cases h1 : ltKey (key p.1) (key q.1) = true
    · rw [if_pos h1] at h
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [if_neg h1] at h
      by_cases h2 : key p.1 = key q.1
      · rw [if_pos h2] at h
        exact Or.inr h
      · rw [if_neg h2] at h
        rcases List.mem_cons.mp h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem q h)

/-- Every key of an insertion is the inserted key or an old one. -/
theorem key_mem_insertBy {β : Type} {p x : String × β} {l : List (String × β)}
    (h : x ∈ insertBy key p l) : key x.1 = key p.1 ∨ ∃ y ∈ l, key x.1 = key y.1 := by
  rcases mem_insertBy h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨x, h, rfl⟩

theorem insertBy_ascending {β : Type} (p : String × β) {l : List (String × β)}
    (hl : Ascending key l) : Ascending key (insertBy key p l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ _
  | cons q qs ih =>
    have hq := List.pairwise_cons.mp hl
    unfold insertBy
    by_cases h1 : ltKey (key p.1) (key q.1) = true
    · rw [if_pos h1]
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hl⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact ltKey_trans h1 (hq.1 y hy)
    · rw [if_neg h1]
      by_cases h2 : key p.1 = key q.1
      · rw [if_pos h2]
        exact hl
      · rw [if_neg h2]
        have hqp : ltKey (key q.1) (key p.1) = true :=
          ltKey_total h2 (Bool.eq_false_iff.mpr h1)
        refine List.pairwise_cons.mpr ⟨fun y hy => ?_, ih hq.2⟩
        rcases key_mem_insertBy hy with hy | ⟨z, hz, hy⟩
        · rw [hy]; exact hqp
        · rw [hy]; exact hq.1 z hz

theorem foldl_insertBy_ascending {β : Type} (fs acc : List (String × β))
    (h : Ascending key acc) : Ascending key (fs.foldl (fun a p => insertBy key p a) acc) := by
  induction fs generalizing acc with
  | nil => exact h
  | cons p fs ih => exact ih (insertBy key p acc) (insertBy_ascending p h)

/-- **Sorted.** -/
theorem canonBy_ascending {β : Type} (fs : List (String × β)) : Ascending key (canonBy key fs) :=
  foldl_insertBy_ascending fs [] List.Pairwise.nil

/-- Ascending names are distinct names. -/
theorem names_nodup_of_ascending {β : Type} {l : List (String × β)} (h : Ascending key l) :
    (l.map Prod.fst).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons p ps ih =>
    have hp := List.pairwise_cons.mp h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih hp.2⟩
    obtain ⟨q, hq, hname⟩ := List.mem_map.mp hmem
    have hlt := hp.1 q hq
    rw [hname, ltKey_irrefl] at hlt
    exact Bool.noConfusion hlt

/-- **No repeated name survives.** -/
theorem canonBy_names_nodup {β : Type} (fs : List (String × β)) :
    ((canonBy key fs).map Prod.fst).Nodup :=
  names_nodup_of_ascending (canonBy_ascending fs)

/-! ### Payload maps commute with the order -/

theorem insertBy_map {β γ : Type} (f : β → γ) (p : String × β) (l : List (String × β)) :
    insertBy key (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) =
      (insertBy key p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    rw [List.map_cons]
    unfold insertBy
    by_cases h1 : ltKey (key p.1) (key q.1) = true
    · rw [if_pos h1, if_pos h1]
      rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : key p.1 = key q.1
      · rw [if_pos h2, if_pos h2]
        rfl
      · rw [if_neg h2, if_neg h2, ih]
        rfl

theorem foldl_insertBy_map {β γ : Type} (f : β → γ) (xs acc : List (String × β)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => insertBy key p a)
        (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => insertBy key p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [insertBy_map f x acc]
    exact ih (insertBy key x acc)

/-- **The order reads names only**: a payload map commutes with `canonBy`. -/
theorem canonBy_map {β γ : Type} (f : β → γ) (fs : List (String × β)) :
    canonBy key (fs.map (fun q => (q.1, f q.2))) = (canonBy key fs).map (fun q => (q.1, f q.2)) :=
  foldl_insertBy_map f fs []

/-- A payload map keeps a list ascending: the order reads names only. -/
theorem ascending_map {β γ : Type} (f : β → γ) {l : List (String × β)} (h : Ascending key l) :
    Ascending key (l.map (fun q => (q.1, f q.2))) := by
  unfold Ascending at h ⊢
  rw [List.pairwise_map]
  exact h

/-! ### Idempotence -/

theorem insertBy_last {β : Type} (p : String × β) (l : List (String × β))
    (h : ∀ q ∈ l, ltKey (key q.1) (key p.1) = true) : insertBy key p l = l ++ [p] := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    have hq : ltKey (key q.1) (key p.1) = true := h q List.mem_cons_self
    have h1 : ¬ ltKey (key p.1) (key q.1) = true := by
      rw [ltKey_asymm hq]
      exact Bool.false_ne_true
    have h2 : ¬ key p.1 = key q.1 := by
      intro he
      rw [he, ltKey_irrefl] at hq
      exact Bool.noConfusion hq
    unfold insertBy
    rw [if_neg h1, if_neg h2, ih (fun r hr => h r (List.mem_cons_of_mem q hr)), List.cons_append]

theorem foldl_insertBy_of_ascending {β : Type} (xs acc : List (String × β))
    (h : Ascending key (acc ++ xs)) :
    xs.foldl (fun a p => insertBy key p a) acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => rw [List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    have hx : ∀ q ∈ acc, ltKey (key q.1) (key x.1) = true := fun q hq =>
      (List.pairwise_append.mp h).2.2 q hq x List.mem_cons_self
    rw [List.foldl_cons, insertBy_last x acc hx]
    have h' : Ascending key ((acc ++ [x]) ++ xs) := by
      rw [List.append_assoc, List.singleton_append]
      exact h
    rw [ih (acc ++ [x]) h', List.append_assoc, List.singleton_append]

/-- An ascending list is its own canonical form. -/
theorem canonBy_of_ascending {β : Type} (l : List (String × β)) (h : Ascending key l) :
    canonBy key l = l :=
  foldl_insertBy_of_ascending l [] (by rw [List.nil_append]; exact h)

/-- **Idempotent.** -/
theorem canonBy_idem {β : Type} (fs : List (String × β)) :
    canonBy key (canonBy key fs) = canonBy key fs :=
  canonBy_of_ascending _ (canonBy_ascending fs)

/-! ### Membership: nothing new, and the first occurrence is the one kept -/

theorem mem_foldl_insertBy {β : Type} {x : String × β} (xs acc : List (String × β))
    (h : x ∈ xs.foldl (fun a p => insertBy key p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons p ps ih =>
    rw [List.foldl_cons] at h
    rcases ih (insertBy key p acc) h with h | h
    · rcases mem_insertBy h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem p h)

/-- **Nothing new**: a canonical field is a written field. -/
theorem mem_canonBy {β : Type} {x : String × β} {fs : List (String × β)}
    (h : x ∈ canonBy key fs) : x ∈ fs := by
  rcases mem_foldl_insertBy fs [] h with h | h
  · exact absurd h List.not_mem_nil
  · exact h

/-- The payload of the first field of a name. -/
def firstOf {β : Type} (n : String) : List (String × β) → Option β
  | [] => none
  | (m, b) :: rest => if m = n then some b else firstOf n rest

theorem firstOf_mem {β : Type} {n : String} {b : β} :
    ∀ {l : List (String × β)}, firstOf n l = some b → (n, b) ∈ l
  | [], h => nomatch h
  | (m, c) :: rest, h => by
    unfold firstOf at h
    by_cases hm : m = n
    · rw [if_pos hm] at h
      cases h
      rw [hm]
      exact List.mem_cons_self
    · rw [if_neg hm] at h
      exact List.mem_cons_of_mem _ (firstOf_mem h)

theorem firstOf_eq_none {β : Type} {n : String} :
    ∀ {l : List (String × β)}, (∀ p ∈ l, p.1 ≠ n) → firstOf n l = none
  | [], _ => rfl
  | (m, c) :: rest, h => by
    unfold firstOf
    rw [if_neg (h (m, c) List.mem_cons_self)]
    exact firstOf_eq_none (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem firstOf_of_nodup {β : Type} {n : String} {b : β} :
    ∀ {l : List (String × β)}, (l.map Prod.fst).Nodup → (n, b) ∈ l → firstOf n l = some b
  | [], _, h => absurd h List.not_mem_nil
  | (m, c) :: rest, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    unfold firstOf
    rcases List.mem_cons.mp h with h | h
    · cases h
      rw [if_pos rfl]
    · have hm : m ≠ n := by
        intro he
        subst he
        exact hnd.1 (List.mem_map.mpr ⟨(m, b), h, rfl⟩)
      rw [if_neg hm]
      exact firstOf_of_nodup hnd.2 h

/-- Two ascending lists with the same members are equal (the keyed `Row.ascending_list_ext`). -/
theorem ascending_ext {β : Type} {l1 l2 : List (String × β)} (h1 : Ascending key l1)
    (h2 : Ascending key l2) (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys => exact absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
  | cons x xs ih =>
    cases l2 with
    | nil => exact absurd ((hmem x).mp List.mem_cons_self) List.not_mem_nil
    | cons y ys =>
      have hx1 := List.pairwise_cons.mp h1
      have hy2 := List.pairwise_cons.mp h2
      -- the heads are each other's least element
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | hxys
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self) with h | hyxs
          · exact h.symm
          · have a := hy2.1 x hxys
            have b := hx1.1 y hyxs
            rw [ltKey_asymm a] at b
            exact absurd b Bool.false_ne_true
      subst hxy
      congr 1
      refine ih hx1.2 hy2.2 (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
      · rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem x hz)) with h | h
        · subst h
          have := hx1.1 z hz
          rw [ltKey_irrefl] at this
          exact absurd this Bool.false_ne_true
        · exact h
      · rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem x hz)) with h | h
        · subst h
          have := hy2.1 z hz
          rw [ltKey_irrefl] at this
          exact absurd this Bool.false_ne_true
        · exact h

/-- A name that occurs has a first occurrence. -/
theorem firstOf_ne_none_of_mem {β : Type} {n : String} {q : String × β} :
    ∀ {l : List (String × β)}, q ∈ l → q.1 = n → firstOf n l ≠ none
  | (m, c) :: rest, hq, hqn => by
    unfold firstOf
    by_cases hm : m = n
    · rw [if_pos hm]
      exact Option.some_ne_none c
    · rw [if_neg hm]
      rcases List.mem_cons.mp hq with h | h
      · subst h
        exact absurd hqn hm
      · exact firstOf_ne_none_of_mem h hqn

variable (hinj : ∀ a b, key a = key b → a = b)
include hinj

/-- Insertion: an entry already present wins, else the inserted one. -/
theorem firstOf_insertBy {β : Type} (n : String) (p : String × β) (l : List (String × β))
    (hl : Ascending key l) :
    firstOf n (insertBy key p l) = (firstOf n l).or (if p.1 = n then some p.2 else none) := by
  obtain ⟨pn, pb⟩ := p
  induction l with
  | nil =>
    show (if pn = n then some pb else firstOf n []) = (firstOf n []).or (if pn = n then some pb else none)
    by_cases hp : pn = n
    · rw [if_pos hp, if_pos hp]
      rfl
    · rw [if_neg hp, if_neg hp]
      rfl
  | cons q qs ih =>
    obtain ⟨qn, qb⟩ := q
    have hq := List.pairwise_cons.mp hl
    unfold insertBy
    by_cases h1 : ltKey (key pn) (key qn) = true
    · rw [if_pos h1]
      -- the inserted field goes first; a field named `n` in the old list sits above it
      by_cases hp : pn = n
      · have hnone : firstOf n ((qn, qb) :: qs) = none := by
          apply firstOf_eq_none
          intro r hr hrn
          have hlt : ltKey (key pn) (key r.1) = true := by
            rcases List.mem_cons.mp hr with rfl | hr
            · exact h1
            · exact ltKey_trans h1 (hq.1 r hr)
          rw [hp, ← hrn, ltKey_irrefl] at hlt
          exact Bool.noConfusion hlt
        rw [hnone]
        show (if pn = n then some pb else firstOf n ((qn, qb) :: qs)) = none.or (if pn = n then some pb else none)
        rw [if_pos hp, if_pos hp]
        rfl
      · show (if pn = n then some pb else firstOf n ((qn, qb) :: qs)) =
          (firstOf n ((qn, qb) :: qs)).or (if pn = n then some pb else none)
        rw [if_neg hp, if_neg hp, Option.or_none]
    · rw [if_neg h1]
      by_cases h2 : key pn = key qn
      · rw [if_pos h2]
        have hpq : pn = qn := hinj _ _ h2
        by_cases hp : pn = n
        · have hqn : qn = n := hpq ▸ hp
          show (if qn = n then some qb else firstOf n qs) =
            (if qn = n then some qb else firstOf n qs).or (if pn = n then some pb else none)
          rw [if_pos hqn, if_pos hp]
          rfl
        · show firstOf n ((qn, qb) :: qs) = (firstOf n ((qn, qb) :: qs)).or (if pn = n then some pb else none)
          rw [if_neg hp, Option.or_none]
      · rw [if_neg h2]
        show (if qn = n then some qb else firstOf n (insertBy key (pn, pb) qs)) =
          (if qn = n then some qb else firstOf n qs).or (if pn = n then some pb else none)
        by_cases hqn : qn = n
        · rw [if_pos hqn, if_pos hqn]
          rfl
        · rw [if_neg hqn, if_neg hqn, ih hq.2]

theorem firstOf_foldl_insertBy {β : Type} (n : String) (xs acc : List (String × β))
    (hacc : Ascending key acc) :
    firstOf n (xs.foldl (fun a p => insertBy key p a) acc) = (firstOf n acc).or (firstOf n xs) := by
  induction xs generalizing acc with
  | nil => rw [List.foldl_nil]; exact Option.or_none.symm
  | cons p ps ih =>
    obtain ⟨pn, pb⟩ := p
    rw [List.foldl_cons, ih (insertBy key (pn, pb) acc) (insertBy_ascending (pn, pb) hacc),
      firstOf_insertBy hinj n (pn, pb) acc hacc]
    show ((firstOf n acc).or (if pn = n then some pb else none)).or (firstOf n ps) =
      (firstOf n acc).or (if pn = n then some pb else firstOf n ps)
    by_cases hp : pn = n
    · rw [if_pos hp, if_pos hp, Option.or_assoc]
      rfl
    · rw [if_neg hp, if_neg hp, Option.or_none]

/-- **The first occurrence is the one kept**: on every name, the canonical list answers what
the written list answers first. -/
theorem firstOf_canonBy {β : Type} (n : String) (fs : List (String × β)) :
    firstOf n (canonBy key fs) = firstOf n fs := by
  rw [canonBy, firstOf_foldl_insertBy hinj n fs [] List.Pairwise.nil]
  rfl

/-- On distinct names nothing is dropped: the canonical list has the written members. -/
theorem mem_canonBy_iff {β : Type} {fs : List (String × β)} (hnd : (fs.map Prod.fst).Nodup)
    (x : String × β) : x ∈ canonBy key fs ↔ x ∈ fs := by
  constructor
  · exact mem_canonBy
  · intro hx
    have h := firstOf_of_nodup hnd hx
    rw [← firstOf_canonBy hinj x.1 fs] at h
    exact firstOf_mem h

/-- **Permutation-invariant on distinct names.** (A repeated name breaks it: the red control
`dup_order_matters` below; so formation refuses the repeat.) -/
theorem canonBy_perm {β : Type} {fs gs : List (String × β)} (hp : fs.Perm gs)
    (hnd : (fs.map Prod.fst).Nodup) : canonBy key fs = canonBy key gs := by
  have hnd' : (gs.map Prod.fst).Nodup := (hp.map Prod.fst).nodup_iff.mp hnd
  apply ascending_ext (canonBy_ascending fs) (canonBy_ascending gs)
  intro x
  rw [mem_canonBy_iff hinj hnd, mem_canonBy_iff hinj hnd']
  exact hp.mem_iff

/-- The written names, as a set, are the canonical names. -/
theorem mem_names_canonBy {β : Type} (fs : List (String × β)) (n : String) :
    n ∈ (canonBy key fs).map Prod.fst ↔ n ∈ fs.map Prod.fst := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact List.mem_map_of_mem (mem_canonBy hp)
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    -- some field of that name is first in the written list, hence kept
    cases hf : firstOf p.1 fs with
    | none => exact absurd hf (firstOf_ne_none_of_mem hp rfl)
    | some b =>
      rw [← firstOf_canonBy hinj p.1 fs] at hf
      exact List.mem_map.mpr ⟨(p.1, b), firstOf_mem hf, rfl⟩

omit hinj

/-! ### Emptiness -/

theorem insertBy_ne_nil {β : Type} (p : String × β) (l : List (String × β)) :
    insertBy key p l ≠ [] := by
  cases l with
  | nil => exact List.cons_ne_nil _ _
  | cons q qs =>
    unfold insertBy
    by_cases h1 : ltKey (key p.1) (key q.1) = true
    · rw [if_pos h1]; exact List.cons_ne_nil _ _
    · rw [if_neg h1]
      by_cases h2 : key p.1 = key q.1
      · rw [if_pos h2]; exact List.cons_ne_nil _ _
      · rw [if_neg h2]; exact List.cons_ne_nil _ _

theorem canonBy_eq_nil_iff {β : Type} (fs : List (String × β)) : canonBy key fs = [] ↔ fs = [] := by
  constructor
  · intro h
    cases fs with
    | nil => rfl
    | cons p ps =>
      exfalso
      have : ∀ (xs acc : List (String × β)), acc ≠ [] →
          xs.foldl (fun a p => insertBy key p a) acc ≠ [] := by
        intro xs
        induction xs with
        | nil => intro acc h; exact h
        | cons x xs ih => intro acc _; exact ih _ (insertBy_ne_nil x acc)
      exact this ps (insertBy key p []) (insertBy_ne_nil p []) h
  · rintro rfl; rfl

/-! ### The size bound a well-founded recursion through `canonBy` needs -/

theorem sizeOf_insertBy_le {β : Type} [SizeOf β] (p : String × β) (l : List (String × β)) :
    sizeOf (insertBy key p l) ≤ sizeOf p + 1 + sizeOf l := by
  induction l with
  | nil => simp only [insertBy, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
  | cons q qs ih =>
    unfold insertBy
    by_cases h1 : ltKey (key p.1) (key q.1) = true
    · rw [if_pos h1]; simp only [List.cons.sizeOf_spec]; omega
    · rw [if_neg h1]
      by_cases h2 : key p.1 = key q.1
      · rw [if_pos h2]; simp only [List.cons.sizeOf_spec]; omega
      · rw [if_neg h2]; simp only [List.cons.sizeOf_spec] at ih ⊢; omega

theorem sizeOf_foldl_insertBy_le {β : Type} [SizeOf β] (xs acc : List (String × β)) :
    sizeOf (xs.foldl (fun a p => insertBy key p a) acc) + 1 ≤ sizeOf acc + sizeOf xs := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.nil.sizeOf_spec]; omega
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h1 := ih (insertBy key x acc)
    have h2 := sizeOf_insertBy_le (key := key) x acc
    simp only [List.cons.sizeOf_spec]
    omega

/-- The canonical list is no larger than the written one. -/
theorem sizeOf_canonBy_le {β : Type} [SizeOf β] (fs : List (String × β)) :
    sizeOf (canonBy key fs) ≤ sizeOf fs := by
  have := sizeOf_foldl_insertBy_le (key := key) fs []
  simp only [List.nil.sizeOf_spec] at this
  unfold canonBy
  omega

end Canon

/-! ## The formation refusal: the first repeated name, located -/

/-- The first name that occurs a second time, scanning left to right (the refusal's witness). -/
def firstRepeated {β : Type} (fs : List (String × β)) : Option String :=
  go [] fs
where
  go (seen : List String) : List (String × β) → Option String
    | [] => none
    | (n, _) :: rest => if n ∈ seen then some n else go (n :: seen) rest

theorem firstRepeated_go_eq_none_iff {β : Type} :
    ∀ (seen : List String) (l : List (String × β)),
      firstRepeated.go seen l = none ↔ (l.map Prod.fst).Nodup ∧ ∀ n ∈ l.map Prod.fst, n ∉ seen
  | seen, [] => by
    simp only [firstRepeated.go, List.map_nil, List.nodup_nil, List.not_mem_nil,
      false_implies, implies_true, and_self]
  | seen, (n, b) :: rest => by
    unfold firstRepeated.go
    by_cases hn : n ∈ seen
    · rw [if_pos hn]
      constructor
      · intro h
        cases h
      · rintro ⟨_, hall⟩
        exact absurd hn (hall n List.mem_cons_self)
    · rw [if_neg hn, firstRepeated_go_eq_none_iff (n :: seen) rest, List.map_cons, List.nodup_cons]
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨⟨fun hmem => hall n hmem List.mem_cons_self, hnd⟩, fun m hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hn
        · exact fun hs => hall m hm (List.mem_cons_of_mem n hs)
      · rintro ⟨⟨hnotin, hnd⟩, hall⟩
        refine ⟨hnd, fun m hm hs => ?_⟩
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hnotin hm
        · exact hall m (List.mem_cons_of_mem n hm) hs

/-- **The refusal is complete against the judgment**: no witness exactly when the names are
distinct (the located-refusal shape, `explain = none ↔ wellTyped`). -/
theorem firstRepeated_eq_none_iff {β : Type} (fs : List (String × β)) :
    firstRepeated fs = none ↔ (fs.map Prod.fst).Nodup := by
  rw [firstRepeated, firstRepeated_go_eq_none_iff]
  simp only [List.not_mem_nil, not_false_eq_true, implies_true, and_true]

/-! ## The instance the tree uses, and finite controls -/

/-- The canonical field order: ascending by the name's UTF-8 bytes, the first occurrence of a
repeated name kept. -/
abbrev canon {β : Type} : List (String × β) → List (String × β) := canonBy bytesKey

#guard canon [("b", 1), ("a", 2)] = [("a", 2), ("b", 1)]
#guard canon [("ab", 1), ("a", 2), ("", 3)] = [("", 3), ("a", 2), ("ab", 1)]
-- UTF-8 byte order: an uppercase letter (0x41..0x5A) sorts before `_` (0x5F), lowercase after
#guard canon [("_tag", 1), ("X", 2), ("y", 3)] = [("X", 2), ("_tag", 1), ("y", 3)]
#guard canon [("_tag", 1), ("_id", 2)] = [("_id", 2), ("_tag", 1)]
-- non-ASCII: `é` (C3 A9) before `ê` (C3 AA)
#guard canon [("ê", 1), ("é", 2)] = [("é", 2), ("ê", 1)]
-- the first occurrence is kept
#guard canon [("a", 1), ("b", 2), ("a", 3)] = [("a", 1), ("b", 2)]
#guard firstRepeated [("a", 1), ("b", 2), ("a", 3)] = some "a"
#guard firstRepeated [("a", 1), ("b", 2)] = none

end Effect4.Field
