import Tools.Graph.Index

/-!
# A table by key, on the sparse index

The live view keeps three tables from one frame to the next: the organic strokes by what they read
(`Laid.StrokeCache`), each line's own text by its address (`Inc.Memo`), and a retained picture's
objects by their identities (`Retained.Scene`). Each answers a lookup in a frame, and each law of
those caches reads a lookup after an insert.

`Std.HashMap`'s lemmas reach `Classical.choice` on this toolchain (measured 2026-10-10: its
`getElem?_insert` walks to it). So the view's tables stand on the sparse index of
`Tools.Graph.Index`, whose laws stay within `[propext, Quot.sound]`. A key's hash, modulo
`SLOTS`, picks its bucket; a bucket holds each of its keys once, newest first.

- `get?_insert`: a lookup after an insert answers the inserted value at that key, and the old
  answer at every other key;
- `get?_erase`: a lookup after an erase answers nothing at that key, and the old answer at every
  other key;
- `get?_empty`: the empty table answers nothing.

They are tool laws, not registry claims (decisions row 334, point 3). They serve concept
`initial-algebras-folds` and R14's live authoring. Their consumers are the stroke cache's law
(`Connector.cached_valid`), the memo's law (`Inc.next_valid`) and the retained picture's laws
(`Retained.of_flatten`, `Retained.apply_diff`).
-/

namespace Tools.Graph.Index

/-- Replace the bucket at `k` by `f` of it, allocating only its sparse binary path; every other
bucket stands (`bucket_modifyBucket`). -/
def modifyBucket {E : Type} (k : Nat) (f : List E → List E) (index : Index E) : Index E :=
  match k with
  | 0 => .node (f index.values) index.left index.right
  | n + 1 =>
    if n % 2 = 0 then
      .node index.values (modifyBucket (n / 2) f index.left) index.right
    else .node index.values index.left (modifyBucket (n / 2) f index.right)
termination_by k

/-- A modified bucket reads `f` of the old one; every other bucket reads as before. A step of the
key table's laws (`Tools.View.KeyMap.get?_insert`, `Tools.View.KeyMap.get?_erase`). -/
theorem bucket_modifyBucket {E : Type} (k j : Nat) (f : List E → List E) (index : Index E) :
    (modifyBucket k f index).bucket j =
      if k = j then f (index.bucket j) else index.bucket j := by
  induction k using Nat.strongRecOn generalizing j index with
  | ind k ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp only [modifyBucket, bucket, values, if_true]
      | succ m => simp only [modifyBucket, bucket, values, left, right, Nat.zero_ne_add_one, if_false]
    | succ n =>
      cases j with
      | zero =>
        simp only [modifyBucket, bucket]
        split <;> rfl
      | succ m =>
        by_cases hn : n % 2 = 0
        · by_cases hm : m % 2 = 0
          · simp only [modifyBucket, bucket, hn, hm, if_true, left]
            rw [ih (n / 2) (by omega)]
            have same : n / 2 = m / 2 ↔ n = m :=
              ⟨(fun half => by omega), (fun equal => congrArg (· / 2) equal)⟩
            simp only [same, Nat.succ.injEq]
          · have different : n + 1 ≠ m + 1 := by omega
            simp only [modifyBucket, bucket, hn, hm, if_true, if_false, right, different]
        · by_cases hm : m % 2 = 0
          · have different : n + 1 ≠ m + 1 := by omega
            simp only [modifyBucket, bucket, hn, hm, if_true, if_false, left, different]
          · simp only [modifyBucket, bucket, hn, hm, if_false, right]
            rw [ih (n / 2) (by omega)]
            have same : n / 2 = m / 2 ↔ n = m :=
              ⟨(fun half => by omega), (fun equal => congrArg (· / 2) equal)⟩
            simp only [same, Nat.succ.injEq]

end Tools.Graph.Index

namespace Tools.View

/-- The buckets of a key table: a key's hash picks one of this many. -/
def SLOTS : Nat := 4096

/-- **A table by key**: each entry stands in the bucket of its key's slot, and a key stands once. -/
structure KeyMap (κ α : Type) where
  index : Tools.Graph.Index (κ × α) := .empty

namespace KeyMap

variable {κ α : Type} [DecidableEq κ] [Hashable κ]

/-- The bucket of a key. -/
def slot (k : κ) : Nat := (hash k).toNat % SLOTS

/-- The value at a key. -/
def get? (m : KeyMap κ α) (k : κ) : Option α :=
  ((m.index.bucket (slot k)).find? fun e => decide (e.1 = k)).map (·.2)

/-- The value at a key, or `d`. -/
def getD (m : KeyMap κ α) (k : κ) (d : α) : α := (m.get? k).getD d

/-- Whether a key has a value. -/
def contains (m : KeyMap κ α) (k : κ) : Bool := (m.get? k).isSome

/-- The table with `v` at `k`: the key's bucket keeps its other keys and puts this one first. -/
def insert (m : KeyMap κ α) (k : κ) (v : α) : KeyMap κ α :=
  ⟨m.index.modifyBucket (slot k) fun b => (k, v) :: b.filter fun e => !decide (e.1 = k)⟩

/-- The table with nothing at `k`. -/
def erase (m : KeyMap κ α) (k : κ) : KeyMap κ α :=
  ⟨m.index.modifyBucket (slot k) fun b => b.filter fun e => !decide (e.1 = k)⟩

/-- A list's first entry at a key, past a filter that keeps every entry at that key. -/
theorem find?_filter_keep {β : Type} (p q : β → Bool) (keep : ∀ e, p e = true → q e = true) :
    ∀ l : List β, (l.filter q).find? p = l.find? p
  | [] => rfl
  | e :: l => by
    cases hp : p e with
    | true => simp only [List.filter_cons, keep e hp, if_true, List.find?_cons, hp]
    | false =>
      cases hq : q e with
      | true => simp only [List.filter_cons, hq, if_true, List.find?_cons, hp, find?_filter_keep p q keep l]
      | false => simp only [List.filter_cons, hq, Bool.false_eq_true, if_false, List.find?_cons, hp,
          find?_filter_keep p q keep l]

/-- **The empty table answers nothing.** A step of the caches' laws. -/
theorem get?_empty (k : κ) : ({} : KeyMap κ α).get? k = none := by
  simp only [get?, Tools.Graph.Index.bucket_empty, List.find?_nil, Option.map_none]

/-- **A lookup after an insert** answers the value at the inserted key, and the old answer at
every other key. A tool law; its consumers are the stroke cache's, the memo's and the retained
picture's laws. Placement: concept `initial-algebras-folds`, R14's live authoring. -/
theorem get?_insert (m : KeyMap κ α) (k j : κ) (v : α) :
    (m.insert k v).get? j = if k = j then some v else m.get? j := by
  unfold get? insert
  rw [Tools.Graph.Index.bucket_modifyBucket]
  by_cases hkj : k = j
  · subst hkj
    simp only [if_true, List.find?_cons, decide_true, Option.map_some]
  · rw [if_neg hkj]
    by_cases hs : slot k = slot j
    · rw [if_pos hs, List.find?_cons]
      have hne : decide (k = j) = false := decide_eq_false hkj
      simp only [hne]
      rw [find?_filter_keep (fun e : κ × α => decide (e.1 = j)) (fun e => !decide (e.1 = k))
        (fun e he => by
          have h1 : e.1 = j := of_decide_eq_true he
          have h2 : decide (e.1 = k) = false := decide_eq_false (fun h => hkj (h.symm.trans h1))
          rw [h2]; rfl)]
    · rw [if_neg hs]

/-- **A lookup after an erase** answers nothing at the erased key, and the old answer at every
other key. A tool law; its consumer is the retained picture's law. Placement: concept
`initial-algebras-folds`, R14's live authoring. -/
theorem get?_erase (m : KeyMap κ α) (k j : κ) :
    (m.erase k).get? j = if k = j then none else m.get? j := by
  unfold get? erase
  rw [Tools.Graph.Index.bucket_modifyBucket]
  by_cases hkj : k = j
  · subst hkj
    simp only [if_true]
    rw [find?_none_of_filter]
  · rw [if_neg hkj]
    by_cases hs : slot k = slot j
    · rw [if_pos hs]
      rw [find?_filter_keep (fun e : κ × α => decide (e.1 = j)) (fun e => !decide (e.1 = k))
        (fun e he => by
          have h1 : e.1 = j := of_decide_eq_true he
          have h2 : decide (e.1 = k) = false := decide_eq_false (fun h => hkj (h.symm.trans h1))
          rw [h2]; rfl)]
    · rw [if_neg hs]
where
  /-- A filter that drops every entry at a key leaves no entry at that key to find. -/
  find?_none_of_filter : ∀ (l : List (κ × α)),
      Option.map (·.2) ((l.filter fun e => !decide (e.1 = k)).find? fun e => decide (e.1 = k)) = none
    | [] => rfl
    | e :: l => by
      by_cases he : e.1 = k
      · simp only [List.filter_cons, he, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        exact find?_none_of_filter l
      · have hd : decide (e.1 = k) = false := decide_eq_false he
        simp only [List.filter_cons, hd, Bool.not_false, if_true, List.find?_cons]
        exact find?_none_of_filter l

/-- A lookup with a default after an insert. A step of the retained picture's law. -/
theorem getD_insert (m : KeyMap κ α) (k j : κ) (v d : α) :
    (m.insert k v).getD j d = if k = j then v else m.getD j d := by
  unfold getD
  rw [get?_insert]
  by_cases h : k = j
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-- Whether a key has a value, after an insert. A step of the retained picture's law. -/
theorem contains_insert (m : KeyMap κ α) (k j : κ) (v : α) :
    (m.insert k v).contains j = (decide (k = j) || m.contains j) := by
  unfold contains
  rw [get?_insert]
  by_cases h : k = j
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

/-- Index a list by its first occurrence at each key. -/
def firstBy (key : α → κ) (xs : List α) : KeyMap κ α :=
  xs.foldr (fun a m => m.insert (key a) a) {}

/-- First-occurrence indexing agrees with list lookup, including duplicate keys.
Placement: graph-defects plan, concept 7, R14; consumed by the graph attachment index. -/
theorem get?_firstBy (key : α → κ) (xs : List α) (k : κ) :
    (firstBy key xs).get? k = xs.find? (fun a => decide (key a = k)) := by
  induction xs with
  | nil => exact get?_empty k
  | cons a xs ih =>
    simp only [firstBy, List.foldr_cons, get?_insert, List.find?_cons]
    by_cases h : key a = k
    · simp only [h, if_true, decide_true]
    · simp only [h, if_false, decide_false]
      exact ih

end KeyMap

end Tools.View
