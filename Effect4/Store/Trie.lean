import Effect4.Store.Canonical

/-!
# Store.Trie

Owner: the path trie — names to values, keyed segment by segment.

A `Trie α` is a node with an optional value and children keyed by one segment
each. `lookup` walks a path; `insert` writes at a path, creating the nodes on
the way; `entries` lists every bound path in prefix order and `under` the ones
below a prefix. Children are an association list in first-insertion order, so
the trie is deterministic data with decidable equality, and `entries` is a
canonical listing.

The two lookup laws are the whole contract: writing at a path is read back at
that path (`lookup_insert_same`) and at no other (`lookup_insert_other`).
-/

namespace Effect4.Store

/-- A path trie: a value at this node, and children keyed by one segment. -/
inductive Trie (α : Type) : Type where
  | node (value : Option α) (children : List (String × Trie α))

namespace Trie

variable {α : Type}

/-- The empty trie. -/
def empty : Trie α := .node none []

def value : Trie α → Option α
  | .node v _ => v

def children : Trie α → List (String × Trie α)
  | .node _ cs => cs

/-- The child under one segment: the first entry with that key. -/
def child? (cs : List (String × Trie α)) (k : String) : Option (Trie α) :=
  match cs with
  | [] => none
  | (k', c) :: rest => if k' = k then some c else child? rest k

/-- The value at a path. -/
def lookup : Trie α → List String → Option α
  | .node v _, [] => v
  | .node _ cs, k :: ks =>
    match child? cs k with
    | some c => lookup c ks
    | none => none

/-- Replace the child under a segment, or append it. -/
def setChild (cs : List (String × Trie α)) (k : String) (c : Trie α) : List (String × Trie α) :=
  match cs with
  | [] => [(k, c)]
  | (k', c') :: rest => if k' = k then (k, c) :: rest else (k', c') :: setChild rest k c

/-- Write a value at a path, creating the nodes on the way. -/
def insert : Trie α → List String → α → Trie α
  | .node _ cs, [], a => .node (some a) cs
  | .node v cs, k :: ks, a =>
    let sub := (child? cs k).getD empty
    .node v (setChild cs k (insert sub ks a))

/-! `entries`: every bound path with its value, in prefix order — this node first,
then the children in their order. -/
mutual
  def entries : Trie α → List (List String × α)
    | .node v cs => (match v with | some a => [([], a)] | none => []) ++ entriesList cs
  termination_by structural t => t

  def entriesList : List (String × Trie α) → List (List String × α)
    | [] => []
    | (k, c) :: rest => (entries c).map (fun e => (k :: e.1, e.2)) ++ entriesList rest
  termination_by structural cs => cs
end

/-- The subtrie at a prefix, if any node is there. -/
def at? : Trie α → List String → Option (Trie α)
  | t, [] => some t
  | .node _ cs, k :: ks =>
    match child? cs k with
    | some c => at? c ks
    | none => none

/-- Every bound path below a prefix (the prefix itself included when bound),
spelled in full. -/
def under (t : Trie α) (prefix_ : List String) : List (List String × α) :=
  match t.at? prefix_ with
  | some sub => (entries sub).map (fun e => (prefix_ ++ e.1, e.2))
  | none => []

/-- The number of bound paths. -/
def size (t : Trie α) : Nat := (entries t).length

/-- Build a trie from bindings, later bindings winning. -/
def ofList (bindings : List (List String × α)) : Trie α :=
  bindings.foldl (fun t b => t.insert b.1 b.2) empty

/-! ## Laws -/

theorem lookup_empty : ∀ p : List String, (empty : Trie α).lookup p = none
  | [] => rfl
  | _ :: _ => rfl

theorem child?_setChild_same (cs : List (String × Trie α)) (k : String) (c : Trie α) :
    child? (setChild cs k c) k = some c := by
  induction cs with
  | nil => simp [setChild, child?]
  | cons e rest ih =>
    obtain ⟨k', c'⟩ := e
    by_cases h : k' = k
    · simp [setChild, child?, h]
    · simp [setChild, child?, h, ih]

theorem child?_setChild_other (cs : List (String × Trie α)) (k k' : String) (c : Trie α)
    (h : k' ≠ k) : child? (setChild cs k c) k' = child? cs k' := by
  induction cs with
  | nil =>
    have hne : ¬ k = k' := fun e => h e.symm
    simp [setChild, child?, hne]
  | cons e rest ih =>
    obtain ⟨k'', c'⟩ := e
    by_cases hk : k'' = k
    · subst hk
      have hne : ¬ k'' = k' := fun e => h e.symm
      simp [setChild, child?, hne]
    · simp [setChild, child?, hk, ih]

/-- Writing at a path is read back at that path. -/
theorem lookup_insert_same : ∀ (t : Trie α) (p : List String) (a : α),
    (t.insert p a).lookup p = some a
  | .node _ _, [], _ => rfl
  | .node v cs, k :: ks, a => by
    simp only [insert, lookup, child?_setChild_same]
    exact lookup_insert_same _ ks a

/-- Writing at a path changes no other path. -/
theorem lookup_insert_other : ∀ (t : Trie α) (p q : List String) (a : α), p ≠ q →
    (t.insert p a).lookup q = t.lookup q
  | .node _ _, [], [], _, h => absurd rfl h
  | .node _ _, [], _ :: _, _, _ => rfl
  | .node _ _, _ :: _, [], _, _ => rfl
  | .node v cs, k :: ks, k' :: ks', a, h => by
    by_cases hk : k' = k
    · subst hk
      have hne : ks ≠ ks' := fun e => h (by rw [e])
      simp only [insert, lookup, child?_setChild_same]
      rw [lookup_insert_other _ ks ks' a hne]
      cases child? cs k' with
      | some c => rfl
      | none => simp [Option.getD, lookup_empty]
    · simp only [insert, lookup, child?_setChild_other cs k k' _ hk]

end Trie

end Effect4.Store
