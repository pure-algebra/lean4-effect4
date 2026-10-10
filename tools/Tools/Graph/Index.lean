import Lean.Elab.Tactic.Omega

/-!
# Stable sparse occurrence index

The index groups an existing alphabet by a natural key.
A bucket retains every occurrence in its original order, including duplicates.
The keys have no dense allocation bound.
No graph or program representation is introduced.

The named tool laws serve concept 7, `initial-algebras-folds`, and R14 navigation.
Decisions row 336, point 8, places them outside registry claims.
The five-point placement is in the index packet's `PLAN.md`.
Flow height assignment consumes the bucket's agreement with list filtering.
-/

namespace Tools.Graph

/-- Sparse binary buckets over an existing alphabet, retaining occurrence order.
Positive keys select a child by parity of their predecessor, then halve it. -/
inductive Index (E : Type) where
  | empty
  | node (here : List E) (left right : Index E)

namespace Index

/-- Values at the current node; an empty node holds no occurrences. -/
def values {E : Type} : Index E → List E
  | .empty => []
  | .node here _ _ => here

/-- The even branch; an absent branch is empty. -/
def left {E : Type} : Index E → Index E
  | .empty => .empty
  | .node _ l _ => l

/-- The odd branch; an absent branch is empty. -/
def right {E : Type} : Index E → Index E
  | .empty => .empty
  | .node _ _ r => r

/-- Prepend one occurrence at its key, allocating only its sparse binary path. -/
def push {E : Type} (k : Nat) (e : E) (index : Index E) : Index E :=
  match k with
  | 0 => .node (e :: index.values) index.left index.right
  | n + 1 =>
    if n % 2 = 0 then
      .node index.values (push (n / 2) e index.left) index.right
    else .node index.values index.left (push (n / 2) e index.right)
termination_by k

/-- Read the original occurrences at one key. Missing keys answer the empty list. -/
def bucket {E : Type} (index : Index E) (k : Nat) : List E :=
  match k with
  | 0 => index.values
  | n + 1 =>
    if n % 2 = 0 then bucket index.left (n / 2) else bucket index.right (n / 2)
termination_by k

/-- Group each occurrence by its key, without deduplication or a dense position bound. -/
def ofList {E : Type} (key : E → Nat) : List E → Index E
  | [] => .empty
  | e :: es => push (key e) e (ofList key es)

/-- Empty lookup serves insertion agreement at any sparse natural key. -/
theorem bucket_empty {E : Type} (k : Nat) : (Index.empty : Index E).bucket k = [] := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp only [bucket, values]
    | succ n =>
      simp only [bucket, left, right]
      split
      · exact ih (n / 2) (by omega)
      · exact ih (n / 2) (by omega)

/-- Insertion changes precisely one bucket and prepends its occurrence.
This helper serves stable list-filter agreement. -/
theorem bucket_push {E : Type} (k j : Nat) (e : E) (index : Index E) :
    (push k e index).bucket j =
      if k = j then e :: index.bucket j else index.bucket j := by
  induction k using Nat.strongRecOn generalizing j index with
  | ind k ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp only [push, bucket, values, if_true]
      | succ m => simp only [push, bucket, values, left, right, Nat.zero_ne_add_one, if_false]
    | succ n =>
      cases j with
      | zero =>
        simp only [push, bucket]
        split <;> rfl
      | succ m =>
        by_cases hn : n % 2 = 0
        · by_cases hm : m % 2 = 0
          · simp only [push, bucket, hn, hm, if_true, left]
            rw [ih (n / 2) (by omega)]
            have same : n / 2 = m / 2 ↔ n = m :=
              ⟨(fun half => by omega), (fun equal => congrArg (· / 2) equal)⟩
            simp only [same, Nat.succ.injEq]
          · have different : n + 1 ≠ m + 1 := by omega
            simp only [push, bucket, hn, hm, if_true, if_false, right, different]
        · by_cases hm : m % 2 = 0
          · have different : n + 1 ≠ m + 1 := by omega
            simp only [push, bucket, hn, hm, if_true, if_false, left, different]
          · simp only [push, bucket, hn, hm, if_false, right]
            rw [ih (n / 2) (by omega)]
            have same : n / 2 = m / 2 ↔ n = m :=
              ⟨(fun half => by omega), (fun equal => congrArg (· / 2) equal)⟩
            simp only [same, Nat.succ.injEq]

/-- Bucket agreement serves Flow's indexed relaxation, preserving occurrence order. -/
theorem bucket_ofList {E : Type} (key : E → Nat) (es : List E) (k : Nat) :
    (ofList key es).bucket k = es.filter (fun e => decide (key e = k)) := by
  induction es with
  | nil => exact bucket_empty k
  | cons e es ih =>
    simp only [ofList, bucket_push, List.filter_cons, decide_eq_true_eq, ih]

end Index
end Tools.Graph
