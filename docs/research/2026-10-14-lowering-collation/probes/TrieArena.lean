import Effect4.Laws.Machine.RefKernel

/-!
# Probe B: a dense arena over a persistent trie, lawful at the trust ceiling

Concept: `store-typing`, the storage interfaces of `docs/core/machine-state.md` §7 (the dense arena,
row 101). Question: can the engine's hand carrier of the Ref heap (`E4_store` over
`Map.Make(Int)`, `ocaml/engine/e4_store.ml`) be replaced by a Lean definition that carries the
arena laws, so that the OCaml carrier is made from LCNF? Consumer: the proposed carrier slice of
`docs/research/2026-10-14-lowering-collation/README.md` §8, through `toList_refStepOf`
(`src/Effect4/Laws/Machine/RefKernel.lean`).

Reach: every value of `Dense α`, every index and every value. The laws are the ten fields of
`LawfulArena` (`src/Effect4/Laws/Machine/Arena.lean`), so every law stated over that class holds of
this carrier with no new proof.

Not established: the cost of the trie against `Map.Make(Int)` (nothing measured), the lowering of
this file through LCNF (probe C runs the generator on it), and any machine run over the carrier.

Evidence: proved, audited by `#axiom_audit` in `AuditTrie.lean`.
-/

set_option autoImplicit false

namespace LoweringCollation

/-- A persistent binary trie over natural keys. Key `0` is the root's slot; key `n + 1` goes to the
`even` child at `n / 2` when `n` is even, and to the `odd` child otherwise. A path has about
`log₂ n` nodes, and a write copies only its path. -/
inductive Trie (α : Type) where
  | leaf : Trie α
  | node (here : Option α) (even odd : Trie α) : Trie α

namespace Trie

/-- The value at a key. Structural on the trie. -/
def get {α : Type} : Trie α → Nat → Option α
  | .leaf, _ => none
  | .node here _ _, 0 => here
  | .node _ even odd, n + 1 => if n % 2 = 0 then get even (n / 2) else get odd (n / 2)

/-- The trie with one key written. It copies the key's path and keeps every other node. -/
def set {α : Type} : Trie α → Nat → α → Trie α
  | .leaf, 0, v => .node (some v) .leaf .leaf
  | .node _ even odd, 0, v => .node (some v) even odd
  | .leaf, n + 1, v =>
    if n % 2 = 0 then .node none (set .leaf (n / 2) v) .leaf
    else .node none .leaf (set .leaf (n / 2) v)
  | .node here even odd, n + 1, v =>
    if n % 2 = 0 then .node here (set even (n / 2) v) odd
    else .node here even (set odd (n / 2) v)
termination_by _ n => n

theorem get_leaf {α : Type} (i : Nat) : get (.leaf : Trie α) i = none := by
  cases i <;> rfl

/-- Two keys of one parity and one half are one key. A step of `get_set_other`. -/
theorem half_ne {m n : Nat} (h : m ≠ n) (hp : m % 2 = n % 2) : m / 2 ≠ n / 2 := by
  omega

/-- A written key reads back its value. -/
theorem get_set_same {α : Type} (t : Trie α) (i : Nat) (v : α) : get (set t i v) i = some v := by
  fun_induction set t i v with
  | case1 v => rfl
  | case2 here even odd v => rfl
  | case3 n v even ih =>
    rw [get]
    rw [if_pos even]
    exact ih
  | case4 n v odd ih =>
    rw [get]
    rw [if_neg odd]
    exact ih
  | case5 here even odd n v parity ih =>
    rw [get]
    rw [if_pos parity]
    exact ih
  | case6 here even odd n v parity ih =>
    rw [get]
    rw [if_neg parity]
    exact ih

/-- A write leaves every other key alone. -/
theorem get_set_other {α : Type} (t : Trie α) (i : Nat) (v : α) :
    ∀ j, j ≠ i → get (set t i v) j = get t j := by
  fun_induction set t i v with
  | case1 v =>
    intro j hj
    cases j with
    | zero => exact absurd rfl hj
    | succ m =>
      show (if m % 2 = 0 then get (.leaf : Trie _) (m / 2) else get .leaf (m / 2)) = get .leaf (m + 1)
      rw [get_leaf, get_leaf]
      exact ite_self none
  | case2 here even odd v =>
    intro j hj
    cases j with
    | zero => exact absurd rfl hj
    | succ m => rfl
  | case3 n v parity ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ m =>
      show (if m % 2 = 0 then get (set .leaf (n / 2) v) (m / 2) else get .leaf (m / 2)) =
        get .leaf (m + 1)
      rw [get_leaf (m + 1)]
      by_cases hm : m % 2 = 0
      · rw [if_pos hm]
        rw [ih (m / 2) (half_ne (fun e => hj (congrArg (· + 1) e)) (by omega))]
        exact get_leaf _
      · rw [if_neg hm]
        exact get_leaf _
  | case4 n v parity ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ m =>
      show (if m % 2 = 0 then get (.leaf : Trie _) (m / 2) else get (set .leaf (n / 2) v) (m / 2)) =
        get .leaf (m + 1)
      rw [get_leaf (m + 1)]
      by_cases hm : m % 2 = 0
      · rw [if_pos hm]
        exact get_leaf _
      · rw [if_neg hm]
        rw [ih (m / 2) (half_ne (fun e => hj (congrArg (· + 1) e)) (by omega))]
        exact get_leaf _
  | case5 here even odd n v parity ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ m =>
      show (if m % 2 = 0 then get (set even (n / 2) v) (m / 2) else get odd (m / 2)) =
        (if m % 2 = 0 then get even (m / 2) else get odd (m / 2))
      by_cases hm : m % 2 = 0
      · rw [if_pos hm, if_pos hm]
        exact ih (m / 2) (half_ne (fun e => hj (congrArg (· + 1) e)) (by omega))
      · rw [if_neg hm, if_neg hm]
  | case6 here even odd n v parity ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ m =>
      show (if m % 2 = 0 then get even (m / 2) else get (set odd (n / 2) v) (m / 2)) =
        (if m % 2 = 0 then get even (m / 2) else get odd (m / 2))
      by_cases hm : m % 2 = 0
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm]
        exact ih (m / 2) (half_ne (fun e => hj (congrArg (· + 1) e)) (by omega))

end Trie

/-- A dense arena: a trie whose keys below `size` are exactly its present keys. The invariant is a
proof field, so the compiler erases it and the carrier is the trie and the count. -/
structure Dense (α : Type) where
  trie : Trie α
  size : Nat
  dense : ∀ i, (trie.get i).isSome = true ↔ i < size

namespace Dense

/-- The empty arena. -/
def empty {α : Type} : Dense α :=
  ⟨.leaf, 0, fun i => by rw [Trie.get_leaf]; exact ⟨nofun, nofun⟩⟩

/-- The arena with a present key replaced. An absent key leaves it unchanged, as `List.set`
does. -/
def poke {α : Type} (s : Dense α) (i : Nat) (v : α) : Dense α :=
  if h : i < s.size then
    ⟨s.trie.set i v, s.size, fun j => by
      by_cases hj : j = i
      · subst hj
        rw [Trie.get_set_same]
        exact ⟨fun _ => h, fun _ => rfl⟩
      · rw [Trie.get_set_other s.trie i v j hj]
        exact s.dense j⟩
  else s

/-- The arena with one more value, at the old size. -/
def alloc {α : Type} (s : Dense α) (v : α) : Nat × Dense α :=
  (s.size, ⟨s.trie.set s.size v, s.size + 1, fun j => by
    by_cases hj : j = s.size
    · subst hj
      rw [Trie.get_set_same]
      exact ⟨fun _ => Nat.lt_succ_self _, fun _ => rfl⟩
    · rw [Trie.get_set_other s.trie s.size v j hj, s.dense j]
      exact ⟨Nat.lt_succ_of_lt, fun h => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hj⟩⟩)

end Dense

open Effect4.Machine

instance instArenaDense {α : Type} : Arena (Dense α) α where
  empty := Dense.empty
  size := Dense.size
  peek := fun s i => s.trie.get i
  poke := Dense.poke
  alloc := Dense.alloc

/-- The ten laws of the dense arena hold of the trie carrier. -/
instance instLawfulArenaDense {α : Type} : LawfulArena (Dense α) α where
  size_empty := rfl
  dense := fun s i => s.dense i
  alloc_fresh := fun _ _ => rfl
  size_alloc := fun _ _ => rfl
  peek_alloc_new := fun s v => Trie.get_set_same s.trie s.size v
  peek_alloc_old := fun s v i hi => Trie.get_set_other s.trie s.size v i (Nat.ne_of_lt hi)
  size_poke := fun s i v => by
    show (Dense.poke s i v).size = s.size
    unfold Dense.poke
    split
    · rfl
    · rfl
  peek_poke_same := fun s i v hi => by
    show (Dense.poke s i v).trie.get i = some v
    have bound : i < s.size := hi
    unfold Dense.poke
    rw [dif_pos bound]
    exact Trie.get_set_same s.trie i v
  peek_poke_other := fun s i j v hj => by
    show (Dense.poke s i v).trie.get j = s.trie.get j
    unfold Dense.poke
    split
    · exact Trie.get_set_other s.trie i v j hj
    · rfl
  poke_absent := fun s i v hi => by
    show Dense.poke s i v = s
    have outside : ¬ i < s.size := Nat.not_lt_of_ge hi
    unfold Dense.poke
    rw [dif_neg outside]

/-- A reader of `toList_refStepOf` at the trie carrier: the generic Ref step over the trie
projects to the reference's list step. No new proof: the connector is the class's. -/
theorem trie_ref_step_projects (cell : RefKey) (k : RefKernel) (s : Dense Val) :
    (refStepOfA cell k s).map (Prod.map id Arena.toList) = refStepOf cell k (Arena.toList s) :=
  toList_refStepOf cell k s

/-- The probe's lowering roots (probe C): a read, a write and an allocation over the carrier. -/
def peekAt (s : Dense Nat) (i : Nat) : Option Nat := Arena.peek s i
def pokeAt (s : Dense Nat) (i v : Nat) : Dense Nat := Arena.poke s i v
def allocAt (s : Dense Nat) (v : Nat) : Nat × Dense Nat := Arena.alloc s v

/-- Ten allocations, one replacement, every key read back. -/
def sample : List (Option Nat) :=
  let s := (List.range 10).foldl (fun s v => (allocAt s (v * v)).2) (Dense.empty : Dense Nat)
  let s := pokeAt s 7 700
  (List.range 12).map (peekAt s)

-- finite evaluation: ten allocated keys read back in order, the replaced key reads its new value,
-- and the two keys past the size read nothing
#guard sample == [some 0, some 1, some 4, some 9, some 16, some 25, some 36, some 700, some 64,
  some 81, none, none]

end LoweringCollation
