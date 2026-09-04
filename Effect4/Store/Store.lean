import Effect4.Store.Digest
import Effect4.Store.Trie

/-!
# Store.Store

Owner: the generic content-addressed store — values by address, ids by
insertion, names by path.

A `Store α` holds entries in insertion order; an entry's *id* is its position
and its *address* is the digest of its canonical bytes. `put` deduplicates by
address: putting a value whose address is already held answers the existing id
and leaves the store unchanged, so the id of a content is stable for the life
of the store. `name` binds a path to an id in the trie, and `resolve` reads a
path back to its id and value.

What a consumer models with it: a standard library (one entry per declaration,
named by its module path), a schema surface, a code blob and the syntax read
from it — anything with a canonical encoding. The store knows nothing about
any of them.

## Laws

Every law that would need "distinct values have distinct addresses" is stated
with the address's freshness as a hypothesis (`get_put_new`, `put_new`), never
by assuming SHA-256 has no collision. The name laws are the trie's.
-/

namespace Effect4.Store

/-- The store: entries in insertion order, and names over their ids. -/
structure Store (α : Type) where
  entries : List (Digest × α)
  names : Trie Nat

namespace Store

variable {α : Type}

def empty : Store α := ⟨[], Trie.empty⟩

/-- The number of entries; also the id the next new content receives. -/
def size (s : Store α) : Nat := s.entries.length

/-- The id holding an address, if any. -/
def find (s : Store α) (d : Digest) : Option Nat :=
  s.entries.findIdx? fun e => decide (e.1 = d)

/-- The value at an id. -/
def get (s : Store α) (id : Nat) : Option α :=
  (s.entries[id]?).map Prod.snd

/-- The address at an id. -/
def digestAt (s : Store α) (id : Nat) : Option Digest :=
  (s.entries[id]?).map Prod.fst

/-- Every value, in id order. -/
def values (s : Store α) : List α := s.entries.map Prod.snd

/-- Add a content: its id, and the store — unchanged when the address was already held. -/
def put [Canonical α] (s : Store α) (a : α) : Nat × Store α :=
  let d := digestOf a
  match s.find d with
  | some id => (id, s)
  | none => (s.size, { s with entries := s.entries ++ [(d, a)] })

/-- Bind a path to an id. -/
def name (s : Store α) (p : Path) (id : Nat) : Store α :=
  { s with names := s.names.insert p id }

/-- Add a content and name it in one step. -/
def putAt [Canonical α] (s : Store α) (p : Path) (a : α) : Nat × Store α :=
  let (id, s') := s.put a
  (id, s'.name p id)

/-- A path's id and value, when the path is bound and the id is held. -/
def resolve (s : Store α) (p : Path) : Option (Nat × α) :=
  match s.names.lookup p with
  | some id =>
    match s.get id with
    | some a => some (id, a)
    | none => none
  | none => none

/-- The id bound at a path. -/
def idOf (s : Store α) (p : Path) : Option Nat := s.names.lookup p

/-- Every bound path below a prefix, with its id. -/
def under (s : Store α) (prefix_ : Path) : List (Path × Nat) := s.names.under prefix_

/-- Every bound path, in the trie's prefix order. -/
def paths (s : Store α) : List (Path × Nat) := s.names.entries

/-! ## Laws -/

/-- A new content receives the next id and is read back at it. -/
theorem get_put_new [Canonical α] (s : Store α) (a : α) (h : s.find (digestOf a) = none) :
    (s.put a).2.get (s.put a).1 = some a := by
  simp [put, h, get, size]

/-- A new content's id is the size before the put. -/
theorem put_new [Canonical α] (s : Store α) (a : α) (h : s.find (digestOf a) = none) :
    (s.put a).1 = s.size := by
  simp [put, h]

/-- A held address answers its id and leaves the store as it was. -/
theorem put_held [Canonical α] (s : Store α) (a : α) (id : Nat)
    (h : s.find (digestOf a) = some id) : s.put a = (id, s) := by
  simp [put, h]

/-- A put grows the store by at most one entry. -/
theorem size_put [Canonical α] (s : Store α) (a : α) :
    (s.put a).2.size = s.size ∨ (s.put a).2.size = s.size + 1 := by
  cases h : s.find (digestOf a) with
  | some id =>
    left
    simp only [put, h]
  | none =>
    right
    simp only [put, h]
    show (s.entries ++ [(digestOf a, a)]).length = s.entries.length + 1
    rw [List.length_append, List.length_singleton]

/-- A name is resolved to the id it was bound to and that id's value. -/
theorem resolve_name (s : Store α) (p : Path) (id : Nat) :
    (s.name p id).resolve p =
      match s.get id with
      | some a => some (id, a)
      | none => none := by
  simp [name, resolve, get, Trie.lookup_insert_same]

/-- Naming one path leaves every other path's resolution alone. -/
theorem resolve_name_other (s : Store α) (p q : Path) (id : Nat) (h : p ≠ q) :
    (s.name p id).resolve q = s.resolve q := by
  simp [name, resolve, get, Trie.lookup_insert_other _ p q id h]

/-- Naming touches no entry. -/
theorem get_name (s : Store α) (p : Path) (id id' : Nat) : (s.name p id).get id' = s.get id' := rfl

end Store

end Effect4.Store
