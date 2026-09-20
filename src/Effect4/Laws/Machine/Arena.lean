import Effect4.Machine.Stores
import Effect4.Laws.Auto.Obligations

/-! Phase B statement skeleton; open obligations carry no proof admission. -/

set_option autoImplicit false
namespace Effect4.Machine

class Arena (σ : Type) (α : outParam Type) where
  empty : σ
  size : σ → Nat
  peek : σ → Nat → Option α
  poke : σ → Nat → α → σ
  alloc : σ → α → Nat × σ

class LawfulArena (σ : Type) (α : outParam Type) [Arena σ α] : Prop where
  size_empty : Arena.size (Arena.empty : σ) = 0
  dense : ∀ (s : σ) (i : Nat), (Arena.peek s i).isSome = true ↔ i < Arena.size s
  alloc_fresh : ∀ (s : σ) (v : α), (Arena.alloc s v).1 = Arena.size s
  size_alloc : ∀ (s : σ) (v : α), Arena.size (Arena.alloc s v).2 = Arena.size s + 1
  peek_alloc_new : ∀ (s : σ) (v : α),
    Arena.peek (Arena.alloc s v).2 (Arena.size s) = some v
  peek_alloc_old : ∀ (s : σ) (v : α) (i : Nat), i < Arena.size s →
    Arena.peek (Arena.alloc s v).2 i = Arena.peek s i
  size_poke : ∀ (s : σ) (i : Nat) (v : α), Arena.size (Arena.poke s i v) = Arena.size s
  peek_poke_same : ∀ (s : σ) (i : Nat) (v : α), i < Arena.size s →
    Arena.peek (Arena.poke s i v) i = some v
  peek_poke_other : ∀ (s : σ) (i j : Nat) (v : α), j ≠ i →
    Arena.peek (Arena.poke s i v) j = Arena.peek s j
  poke_absent : ∀ (s : σ) (i : Nat) (v : α), Arena.size s ≤ i → Arena.poke s i v = s

/-- One generic instance supplies both values and deferred cells. -/
instance instArenaList {α : Type} : Arena (List α) α where
  empty := []
  size := List.length
  peek := fun xs i => xs[i]?
  poke := List.set
  alloc := fun xs v => (xs.length, xs ++ [v])

namespace Arena

def toList {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) : List α :=
  (List.range (Arena.size s)).filterMap (Arena.peek s)

end Arena

namespace ArenaObligations

def list_lawful (α : Type) : ProofGraph.Obligation (LawfulArena (List α) α) := ⟨⟩
#proof_wanted list_lawful

def toList_empty {σ α : Type} [Arena σ α] [LawfulArena σ α] :
    ProofGraph.Obligation (Arena.toList (Arena.empty : σ) = []) := ⟨⟩
#proof_wanted toList_empty

def toList_list {α : Type} [LawfulArena (List α) α] (xs : List α) :
    ProofGraph.Obligation (Arena.toList xs = xs) := ⟨⟩
#proof_wanted toList_list

def toList_length {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) :
    ProofGraph.Obligation ((Arena.toList s).length = Arena.size s) := ⟨⟩
#proof_wanted toList_length

def peek_toList {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat) :
    ProofGraph.Obligation (Arena.peek s i = (Arena.toList s)[i]?) := ⟨⟩
#proof_wanted peek_toList

def toList_poke {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat) (v : α) :
    ProofGraph.Obligation (Arena.toList (Arena.poke s i v) = (Arena.toList s).set i v) := ⟨⟩
#proof_wanted toList_poke

def toList_alloc {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (v : α) :
    ProofGraph.Obligation (Arena.toList (Arena.alloc s v).2 = Arena.toList s ++ [v]) := ⟨⟩
#proof_wanted toList_alloc

def deferred_make {κ : Type} (d : DeferredStore κ) : ProofGraph.Obligation (
    d.make =
      (⟨(Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).1⟩,
       { d with cells := (Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).2 })) := ⟨⟩

def deferred_cellAt {κ : Type} (d : DeferredStore κ) (cell : DeferredKey) :
    ProofGraph.Obligation (d.cellAt cell = Arena.peek d.cells cell.index) := ⟨⟩

def deferred_setCell {κ : Type} (d : DeferredStore κ) (cell : DeferredKey)
    (value : DeferredCell κ) : ProofGraph.Obligation (
    d.setCell cell value = { d with cells := Arena.poke d.cells cell.index value }) := ⟨⟩

end ArenaObligations
end Effect4.Machine
