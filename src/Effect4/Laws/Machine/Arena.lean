import Effect4.Machine.Stores
import Effect4.Laws.Auto.Obligations

/-! Dense indexed arenas, their lawful list instance, and the list projection
that respects lookup, update, and allocation. Deferred-store adapters identify
the existing cell operations with this arena interface. -/

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

namespace ArenaSupportWanted

theorem map_some_filterMap {α β : Type} (xs : List α) (f : α → Option β)
    (_present : ∀ a ∈ xs, (f a).isSome = true) : ProofGraph.Obligation
    ((xs.filterMap f).map some = xs.map f) := ⟨⟩

theorem lookup_filterMap {α β : Type} (xs : List α) (f : α → Option β) (i : Nat) (a : α)
    (_present : ∀ x ∈ xs, (f x).isSome = true) (_lookup : xs[i]? = some a) :
    ProofGraph.Obligation ((xs.filterMap f)[i]? = f a) := ⟨⟩

theorem peek_none {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat)
    (_outside : Arena.size s ≤ i) : ProofGraph.Obligation (Arena.peek s i = none) := ⟨⟩

end ArenaSupportWanted

namespace ArenaObligations

theorem list_lawful (α : Type) : ProofGraph.Obligation (LawfulArena (List α) α) := ⟨⟩

theorem toList_empty {σ α : Type} [Arena σ α] [LawfulArena σ α] :
    ProofGraph.Obligation (Arena.toList (Arena.empty : σ) = []) := ⟨⟩

theorem toList_list {α : Type} [LawfulArena (List α) α] (xs : List α) :
    ProofGraph.Obligation (Arena.toList xs = xs) := ⟨⟩

theorem toList_length {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) :
    ProofGraph.Obligation ((Arena.toList s).length = Arena.size s) := ⟨⟩

theorem peek_toList {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat) :
    ProofGraph.Obligation (Arena.peek s i = (Arena.toList s)[i]?) := ⟨⟩

theorem toList_poke {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat) (v : α) :
    ProofGraph.Obligation (Arena.toList (Arena.poke s i v) = (Arena.toList s).set i v) := ⟨⟩

theorem toList_alloc {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (v : α) :
    ProofGraph.Obligation (Arena.toList (Arena.alloc s v).2 = Arena.toList s ++ [v]) := ⟨⟩

theorem deferred_make {κ : Type} (d : DeferredStore κ) : ProofGraph.Obligation (
    d.make =
      (⟨(Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).1⟩,
       { d with cells := (Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).2 })) := ⟨⟩

theorem deferred_cellAt {κ : Type} (d : DeferredStore κ) (cell : DeferredKey) :
    ProofGraph.Obligation (d.cellAt cell = Arena.peek d.cells cell.index) := ⟨⟩

theorem deferred_setCell {κ : Type} (d : DeferredStore κ) (cell : DeferredKey)
    (value : DeferredCell κ) : ProofGraph.Obligation (
    d.setCell cell value = { d with cells := Arena.poke d.cells cell.index value }) := ⟨⟩

end ArenaObligations

attribute [aesop norm simp (rule_sets := [Effect4.StoreKernel])]
  instArenaList Arena.empty Arena.size Arena.peek Arena.poke Arena.alloc

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  LawfulArena.size_empty LawfulArena.dense LawfulArena.alloc_fresh
  LawfulArena.size_alloc LawfulArena.peek_alloc_new LawfulArena.peek_alloc_old
  LawfulArena.size_poke LawfulArena.peek_poke_same LawfulArena.peek_poke_other
  LawfulArena.poke_absent
  List.getElem?_append_left List.set_eq_of_length_le

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] List.getElem?_set_ne

namespace Arena

theorem list_lawful (α : Type) : LawfulArena (List α) α := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add safe constructors [LawfulArena])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] list_lawful

instance instLawfulArenaList {α : Type} : LawfulArena (List α) α := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

theorem map_some_filterMap {α β : Type} (xs : List α) (f : α → Option β)
    (present : ∀ a ∈ xs, (f a).isSome = true) :
    (xs.filterMap f).map some = xs.map f := by
  rw [List.map_filterMap_some_eq_filter_map_isSome]
  apply List.filter_eq_self.mpr
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [List.forall_mem_map])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] map_some_filterMap

theorem lookup_filterMap {α β : Type} (xs : List α) (f : α → Option β) (i : Nat) (a : α)
    (present : ∀ x ∈ xs, (f x).isSome = true) (lookup : xs[i]? = some a) :
    (xs.filterMap f)[i]? = f a := by
  have mapped := congrArg (fun values : List (Option β) => values[i]?)
    (map_some_filterMap xs f present)
  simp only [List.getElem?_map, lookup, Option.map_some] at mapped
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] lookup_filterMap

theorem peek_none {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat)
    (outside : Arena.size s ≤ i) : Arena.peek s i = none := by
  rw [← Option.not_isSome_iff_eq_none, LawfulArena.dense]
  exact Nat.not_lt_of_ge outside

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] peek_none

theorem toList_empty {σ α : Type} [Arena σ α] [LawfulArena σ α] :
    Arena.toList (Arena.empty : σ) = [] := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Arena.toList])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_empty

theorem toList_length {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) :
    (Arena.toList s).length = Arena.size s := by
  have present : ∀ i ∈ List.range (Arena.size s), (Arena.peek s i).isSome = true := by
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [List.mem_range])
  have lengths := List.filterMap_length_eq_length.mpr present
  simpa only [Arena.toList, List.length_range] using lengths

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_length

theorem peek_toList {σ α : Type} [Arena σ α] [LawfulArena σ α] (s : σ) (i : Nat) :
    Arena.peek s i = (Arena.toList s)[i]? := by
  by_cases bound : i < Arena.size s
  · symm
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
      (add norm simp [Arena.toList, List.mem_range, List.getElem?_range])
  · aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add safe apply [List.getElem?_eq_none])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] peek_toList

theorem toList_list {α : Type} [LawfulArena (List α) α] (xs : List α) :
    Arena.toList xs = xs := by
  apply List.ext_getElem?
  intro i
  have lookup := peek_toList xs i
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_list

theorem toList_poke {σ α : Type} [Arena σ α] [LawfulArena σ α]
    (s : σ) (i : Nat) (v : α) :
    Arena.toList (Arena.poke s i v) = (Arena.toList s).set i v := by
  apply List.ext_getElem?
  intro j
  rw [← peek_toList]
  by_cases same : j = i
  · subst j
    by_cases bound : i < Arena.size s
    · have inside : i < (Arena.toList s).length := by
        simpa only [toList_length] using bound
      rw [List.getElem?_set_self inside]
      aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
    · have outside : Arena.size s ≤ i := Nat.le_of_not_gt bound
      have absent : (Arena.toList s).length ≤ i := by
        simpa only [toList_length] using outside
      rw [List.set_eq_of_length_le absent, ← peek_toList]
      aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  · rw [List.getElem?_set_ne (Ne.symm same), ← peek_toList]
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_poke

theorem toList_alloc {σ α : Type} [Arena σ α] [LawfulArena σ α]
    (s : σ) (v : α) :
    Arena.toList (Arena.alloc s v).2 = Arena.toList s ++ [v] := by
  apply List.ext_getElem
  · aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  · intro i leftBound rightBound
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem leftBound, ← List.getElem?_eq_getElem rightBound, ← peek_toList]
    have bound : i < Arena.size s + 1 := by
      simpa only [toList_length, LawfulArena.size_alloc] using leftBound
    rcases Nat.lt_add_one_iff_lt_or_eq.mp bound with old | fresh
    · have inside : i < (Arena.toList s).length := by
        simpa only [toList_length] using old
      rw [List.getElem?_append_left inside, ← peek_toList]
      aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
    · subst i
      have last : (Arena.toList s ++ [v])[Arena.size s]? = some v := by
        simpa only [toList_length] using
          (List.getElem?_concat_length (l := Arena.toList s) (a := v))
      rw [last]
      aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_alloc

theorem deferred_make {κ : Type} (d : DeferredStore κ) :
    d.make =
      (⟨(Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).1⟩,
       { d with cells := (Arena.alloc d.cells (⟨none, WakeList.empty⟩ : DeferredCell κ)).2 }) := by
  aesop

theorem deferred_cellAt {κ : Type} (d : DeferredStore κ) (cell : DeferredKey) :
    d.cellAt cell = Arena.peek d.cells cell.index := by
  aesop

theorem deferred_setCell {κ : Type} (d : DeferredStore κ) (cell : DeferredKey)
    (value : DeferredCell κ) :
    d.setCell cell value = { d with cells := Arena.poke d.cells cell.index value } := by
  aesop

attribute [aesop norm simp (rule_sets := [Effect4.StoreKernel])]
  deferred_make deferred_cellAt deferred_setCell

end Arena

#typed_state_obligations Effect4.Machine.ArenaObligations ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

#typed_state_obligations Effect4.Machine.ArenaSupportWanted ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

end Effect4.Machine
