/-!
# Laws.Auto.ListSubset — the decided inclusion of `++`/`::`/`[]` trees

A list expression built from `++`, `::` and `[]` over atoms is reflected to a tree `Tree`: `nil`,
`app`, and `atom i`, the `i`th entry of an environment `ls : List (List α)` (a `::` head `h` is
the singleton atom `[h]`). `denote ls t` is the list the tree stands for. A hypothesis `L ⊆ M`
is a pair of trees. `check hyps a b` decides that every atom of `a` is reached from the atoms of
`b`: a hypothesis whose right side is reached adds its left side's atoms, as many rounds as there
are hypotheses. `subset_of_check` is the soundness theorem the tactic `sub_tac`
(`Laws/Auto/SubsetTac.lean`) applies; the kernel evaluates `check` on the reflected trees.

Placement: an instrument of the proof graph, with no semantic content of its own. It serves
every `MintedAt`, `KeyBounded` and `Minted` theorem of `Laws/Machine/Handles.lean` and of the
modules that instantiate it, which state their subset obligations through `sub_tac`.
-/

set_option autoImplicit false

namespace Effect4.Laws.ListSubset

/-- A list expression: `[]`, an atom (an index into the environment), or an append. -/
inductive Tree where
  | nil
  | atom (i : Nat)
  | app (l r : Tree)

/-- The atoms of a tree, left to right. -/
def Tree.atoms : Tree → List Nat
  | .nil => []
  | .atom i => [i]
  | .app l r => l.atoms ++ r.atoms

universe u
variable {α : Type u}

/-- The list a tree stands for, at an environment of atoms. -/
def denote (ls : List (List α)) : Tree → List α
  | .nil => []
  | .atom i => ls.getD i []
  | .app l r => denote ls l ++ denote ls r

/-- `i` occurs in `l`. -/
def has (i : Nat) : List Nat → Bool
  | [] => false
  | j :: js => (decide (i = j) || has i js)

theorem has_iff {i : Nat} : ∀ {l : List Nat}, has i l = true ↔ i ∈ l
  | [] => by simp only [has, Bool.false_eq_true, List.not_mem_nil]
  | j :: js => by
    simp only [has, Bool.or_eq_true, decide_eq_true_iff, List.mem_cons]
    exact or_congr Iff.rfl has_iff

/-- Every member of `xs` occurs in `ys`. -/
def allIn (xs ys : List Nat) : Bool := xs.all fun i => has i ys

theorem allIn_iff {xs ys : List Nat} : allIn xs ys = true ↔ ∀ i ∈ xs, i ∈ ys := by
  simp only [allIn, List.all_eq_true, has_iff]

/-- A hypothesis `L ⊆ M`, as its two trees. -/
abbrev Hyp := Tree × Tree

/-- One closure round: a hypothesis whose right side is reached adds its left side's atoms. -/
def step (hyps : List Hyp) (reach : List Nat) : List Nat :=
  hyps.foldl (fun acc p => if allIn p.2.atoms acc then acc ++ p.1.atoms else acc) reach

/-- `n` closure rounds. -/
def closure (hyps : List Hyp) : Nat → List Nat → List Nat
  | 0, reach => reach
  | n + 1, reach => closure hyps n (step hyps reach)

/-- Every atom of `a` is reached from the atoms of `b` through the hypotheses. -/
def check (hyps : List Hyp) (a b : Tree) : Bool :=
  allIn a.atoms (closure hyps hyps.length b.atoms)

/-! ### Soundness -/

/-- The atoms reached stand for sublists of `S`. -/
def Reach (ls : List (List α)) (S : List α) (reach : List Nat) : Prop :=
  ∀ i ∈ reach, ls.getD i [] ⊆ S

/-- Every hypothesis holds of its denotation. -/
def Sound (ls : List (List α)) (hyps : List Hyp) : Prop :=
  ∀ p ∈ hyps, denote ls p.1 ⊆ denote ls p.2

theorem sound_nil (ls : List (List α)) : Sound ls [] := by
  intro p hp
  cases hp

theorem sound_cons {ls : List (List α)} {l m : Tree} {hyps : List Hyp}
    (h : denote ls l ⊆ denote ls m) (hs : Sound ls hyps) : Sound ls ((l, m) :: hyps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact hs p hp

theorem denote_subset_of_atoms (ls : List (List α)) {S : List α} :
    ∀ t : Tree, (∀ i ∈ t.atoms, ls.getD i [] ⊆ S) → denote ls t ⊆ S
  | .nil, _ => List.nil_subset _
  | .atom i, h => h i (List.mem_singleton.mpr rfl)
  | .app l r, h =>
    List.append_subset.mpr
      ⟨denote_subset_of_atoms ls l fun i hi => h i (List.mem_append_left _ hi),
       denote_subset_of_atoms ls r fun i hi => h i (List.mem_append_right _ hi)⟩

theorem atom_subset_denote (ls : List (List α)) :
    ∀ (t : Tree) {i : Nat}, i ∈ t.atoms → ls.getD i [] ⊆ denote ls t
  | .nil, _, h => by cases h
  | .atom j, i, h => by
    obtain rfl : i = j := List.mem_singleton.mp h
    exact List.Subset.refl _
  | .app l r, i, h => by
    rcases List.mem_append.mp h with hl | hr
    · exact List.Subset.trans (atom_subset_denote ls l hl) (List.subset_append_left _ _)
    · exact List.Subset.trans (atom_subset_denote ls r hr) (List.subset_append_right _ _)

theorem reach_append {ls : List (List α)} {S : List α} {r₁ r₂ : List Nat}
    (h₁ : Reach ls S r₁) (h₂ : Reach ls S r₂) : Reach ls S (r₁ ++ r₂) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact h₁ i h
  · exact h₂ i h

theorem reach_atoms (ls : List (List α)) (t : Tree) : Reach ls (denote ls t) t.atoms :=
  fun _ hi => atom_subset_denote ls t hi

theorem reach_hyp {ls : List (List α)} {S : List α} {reach : List Nat} {p : Hyp}
    (hp : denote ls p.1 ⊆ denote ls p.2) (hr : Reach ls S reach) :
    Reach ls S (if allIn p.2.atoms reach then reach ++ p.1.atoms else reach) := by
  split
  · next hall =>
    refine reach_append hr fun i hi => ?_
    have hM : denote ls p.2 ⊆ S :=
      denote_subset_of_atoms ls p.2 fun j hj => hr j (allIn_iff.mp hall j hj)
    exact List.Subset.trans (atom_subset_denote ls p.1 hi) (List.Subset.trans hp hM)
  · exact hr

theorem reach_foldl {ls : List (List α)} {S : List α} :
    ∀ (hyps : List Hyp) {reach : List Nat}, Sound ls hyps → Reach ls S reach →
      Reach ls S (hyps.foldl (fun acc p => if allIn p.2.atoms acc then acc ++ p.1.atoms else acc) reach)
  | [], _, _, hr => hr
  | p :: ps, _, hs, hr =>
    reach_foldl ps (fun q hq => hs q (List.mem_cons.mpr (Or.inr hq)))
      (reach_hyp (hs p (List.mem_cons.mpr (Or.inl rfl))) hr)

theorem step_reach {ls : List (List α)} {S : List α} {hyps : List Hyp} {reach : List Nat}
    (hs : Sound ls hyps) (hr : Reach ls S reach) : Reach ls S (step hyps reach) :=
  reach_foldl hyps hs hr

theorem closure_reach {ls : List (List α)} {S : List α} {hyps : List Hyp} (hs : Sound ls hyps) :
    ∀ (n : Nat) {reach : List Nat}, Reach ls S reach → Reach ls S (closure hyps n reach)
  | 0, _, hr => hr
  | n + 1, _, hr => closure_reach hs n (step_reach hs hr)

/-- **Soundness.** A passed check is an inclusion of the denotations. -/
theorem subset_of_check (ls : List (List α)) (hyps : List Hyp) (a b : Tree)
    (hs : Sound ls hyps) (hc : check hyps a b = true) : denote ls a ⊆ denote ls b :=
  denote_subset_of_atoms ls a fun i hi =>
    closure_reach hs hyps.length (reach_atoms ls b) i (allIn_iff.mp hc i hi)

/-- Membership is the inclusion of the singleton. -/
theorem mem_of_singleton_subset {x : α} {l : List α} (h : [x] ⊆ l) : x ∈ l :=
  h (List.mem_singleton.mpr rfl)

/-- A membership hypothesis, as the inclusion of the singleton. -/
theorem singleton_subset_of_mem {x : α} {l : List α} (h : x ∈ l) : [x] ⊆ l := by
  intro y hy
  obtain rfl : y = x := List.mem_singleton.mp hy
  exact h

end Effect4.Laws.ListSubset
