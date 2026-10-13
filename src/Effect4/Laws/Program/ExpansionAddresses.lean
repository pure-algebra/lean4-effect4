import Effect4.Program.Typing.Source
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Typing.Table
import Effect4.Laws.Program.Typing.Annotate
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.ExpansionAddresses — the expansion keeps every address of the program

`Eff.expandRefs` (`Program/Refs.lean`) replaces each layer reference, a leaf, by the term at its
target, round after round. This module proves the address map of the expansion: the expansion's
addresses that are not strictly below a reference's site are the program's addresses, in their
order (`Eff.addresses_expandRefs`). So every address of the sketch as written is an address of
its expansion, and the copies at the sites hold the rest.

Proof graph, each fact a step of `Eff.addresses_expandRefs`:

* **One round at a node** (`Node.expandRound`): at a node that is no reference, the round is the
  same constructor over its children's rounds, so it commutes with `Node.child`
  (`Node.child_expandRound`). The case list is the generated `Node.child`'s.
* **Below a reference** (`Node.BelowRef`): a proper prefix of the address holds a reference. A
  reference is a leaf, so no address of a node is below one of its references
  (`Node.not_belowRef_of_mem`).
* **A round keeps the address list outside the copies** (`Node.addresses_expandRound_filter`):
  one step down the address list (`Node.addresses_eq_cons`) at a time, by recursion on the node.
* **The references of a round stand at or below the node's** (`Node.ref_expandRound`), so a
  filter that keeps no address below the program's references keeps none below a round's
  (`Node.belowRef_of_expandRound`), and every round keeps the filtered list
  (`Eff.addresses_rounds_filter`).
* **The sites are the references** (`belowSite_refSites_iff`): an address is strictly below a
  reference site exactly when it is below a reference. It reads a site through seat ADDRESS's
  `at_of_mem_refSites` (`Laws/Program/AddressMove.lean`) and `mem_refSites_of_at`
  (`Laws/Program/PathFold.lean`).

Placement (`AGENTS.md`, Trust):

- concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7): the expansion is a fold that
  is the identity at every constructor but a reference; requirement R14;
- question: the address map of the proposed claim `source-annotation-agrees`, whose pointer is
  `Sketch.sourceAnnotate_eq_sourceTable` (`Laws/Program/SourceTable.lean`), the consumer of
  `Eff.addresses_expandRefs`;
- reach: every operation alphabet and every program, its references well formed or not, at the
  bound of `Eff.expandRefs`;
- not established: which source address a copy's address comes from (a copy maps to no source
  address); the node at an address of the expansion beyond its existence; typing; a run;
- it unlocks the edit session's table at the source's addresses (R14, decisions row 373 (7)).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-! ## Two lists facts, with no classical step

The core lemmas `List.filter_eq_nil_iff` and `List.filter_eq_self` reach `Classical.choice`
(`#axiom_audit`, 2026-10-13), so the two facts below are proved by induction. -/

/-- A filter that refuses every element is empty. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem List.filter_eq_nil_of_all_false {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | y :: l, h => by
    rw [List.filter_cons, if_neg (by rw [h y List.mem_cons_self]; exact Bool.false_ne_true),
      List.filter_eq_nil_of_all_false fun x hx => h x (List.mem_cons_of_mem y hx)]

/-- A filter that keeps every element is the list. A step of `Eff.addresses_expandRefs`. The same
fact stands as `filter_all_true` in `Laws/Run/Journal.lean`; a common list bank should hold
one. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem List.filter_eq_self_of_all {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | y :: l, h => by
    rw [List.filter_cons, if_pos (h y List.mem_cons_self),
      List.filter_eq_self_of_all fun x hx => h x (List.mem_cons_of_mem y hx)]

/-! ## A proper prefix -/

/-- **A proper prefix has a nonempty rest.** A step of `Eff.addresses_expandRefs`. Its consumers
are the laws of `Node.BelowRef` below. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Path.properPrefix_eq_true_iff : ∀ (q a : List Nat),
    Path.properPrefix q a = true ↔ ∃ r, r ≠ [] ∧ a = q ++ r
  | [], [] => ⟨nofun, fun ⟨_, hr, h⟩ => (hr (List.append_eq_nil_iff.mp h.symm).2).elim⟩
  | [], b :: bs => ⟨fun _ => ⟨b :: bs, List.cons_ne_nil b bs, rfl⟩, fun _ => rfl⟩
  | j :: q, [] => ⟨nofun, fun ⟨r, _, h⟩ => (List.cons_ne_nil j (q ++ r) h.symm).elim⟩
  | j :: q, b :: bs => by
    simp only [Path.properPrefix, Bool.and_eq_true, decide_eq_true_eq, List.cons_append,
      List.cons.injEq, Path.properPrefix_eq_true_iff q bs]
    constructor
    · rintro ⟨rfl, r, hr, rfl⟩
      exact ⟨r, hr, rfl, rfl⟩
    · rintro ⟨r, hr, rfl, rfl⟩
      exact ⟨rfl, r, hr, rfl⟩

/-! ## One round of the expansion at a node -/

/-- **One round of the expansion at a node of any sort**: the round of its sort
(`Eff.expandRound` and its six siblings, `Program/Refs.lean`). -/
def Node.expandRound (orig : Node Op) : Node Op → Node Op
  | .eff e => .eff (Eff.expandRound orig e)
  | .stmts s => .stmts (Stmts.expandRound orig s)
  | .stmt s => .stmt (Stmt.expandRound orig s)
  | .action a => .action (ActionTerm.expandRound orig a)
  | .effs es => .effs (Effs.expandRound orig es)
  | .layer l => .layer (LayerTerm.expandRound orig l)
  | .layers ls => .layers (LayerTerms.expandRound orig ls)

/-- **The target of a node that is a layer reference**; `none` at every other node. -/
def Node.refTarget? : Node Op → Option (List Nat)
  | .layer (.ref t) => some t
  | _ => none

/-- A node whose target is answered is that reference. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.eq_of_refTarget? {n : Node Op} {t : List Nat} (h : n.refTarget? = some t) :
    n = .layer (.ref t) := by
  cases n
  case layer l =>
    cases l
    case ref t' =>
      cases h
      rfl
    all_goals cases h
  all_goals cases h

/-- A node with no target is no reference. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.ne_ref_of_refTarget? {n : Node Op} (h : n.refTarget? = none) (t : List Nat) :
    n ≠ .layer (.ref t) := by
  rintro rfl
  cases h

/-- A round of a node that is no reference is no reference: the round keeps the constructor. A
step of `Node.ref_expandRound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.refTarget?_expandRound (orig : Node Op) {n : Node Op} (h : n.refTarget? = none) :
    (Node.expandRound orig n).refTarget? = none := by
  cases n
  case layer l =>
    cases l
    case ref t => cases h
    all_goals rfl
  all_goals rfl

/-- **A round commutes with a child at a node that is no reference**: the round is the identity
fold there, so the child of the round is the round of the child. The case list is the generated
`Node.child`'s, at each index. A step of `Eff.addresses_expandRefs`. Its consumers are
`Node.addresses_expandRound_filter` and `Node.ref_expandRound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.child_expandRound (orig : Node Op) (n : Node Op) (i : Nat)
    (h : ∀ t, n ≠ .layer (.ref t)) :
    (Node.expandRound orig n).child i = (n.child i).map (Node.expandRound orig) := by
  cases n with
  | eff x => cases x <;> rcases i with _ | _ | _ | i <;> rfl
  | stmts x => cases x <;> rcases i with _ | _ | _ | i <;> rfl
  | stmt x => cases x <;> rcases i with _ | _ | _ | i <;> rfl
  | action x => cases x <;> rcases i with _ | _ | _ | i <;> rfl
  | effs x => cases x <;> rcases i with _ | _ | _ | i <;> rfl
  | layer x =>
    cases x
    case ref t => exact absurd rfl (h t)
    all_goals rcases i with _ | _ | _ | i <;> rfl
  | layers x => cases x <;> rcases i with _ | _ | _ | i <;> rfl

/-- A reference has no child. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.child_ref (t : List Nat) (i : Nat) :
    (Node.layer (.ref t) : Node Op).child i = none := by
  rcases i with _ | _ | _ | i <;> rfl

/-! ## Below a reference -/

/-- **An address strictly below a layer reference of a node**: a proper prefix of the address
holds a reference. -/
def Node.BelowRef (n : Node Op) (a : List Nat) : Prop :=
  ∃ q t, Path.properPrefix q a = true ∧ n.at_ q = some (.layer (.ref t))

/-- The root is below no reference. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.not_belowRef_nil (n : Node Op) : ¬ n.BelowRef [] := by
  rintro ⟨q, t, hq, -⟩
  obtain ⟨r, hr, h⟩ := (Path.properPrefix_eq_true_iff q []).mp hq
  exact hr (List.append_eq_nil_iff.mp h.symm).2

/-- Every address below the root of a reference is below the reference. A step of
`Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.belowRef_ref (t : List Nat) (i : Nat) (b : List Nat) :
    (Node.layer (.ref t) : Node Op).BelowRef (i :: b) :=
  ⟨[], t, rfl, rfl⟩

/-- **Below a reference, one step down**: at a node that is no reference, an address is below a
reference exactly when its rest is below one of the child's. A step of
`Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.belowRef_cons {n : Node Op} (hn : ∀ t, n ≠ .layer (.ref t)) (i : Nat)
    (b : List Nat) : n.BelowRef (i :: b) ↔ ∃ c, n.child i = some c ∧ c.BelowRef b := by
  constructor
  · rintro ⟨q, t, hq, hat⟩
    cases q with
    | nil => exact absurd (Option.some.inj hat) (hn t)
    | cons j q =>
      simp only [Path.properPrefix, Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨rfl, hq⟩ := hq
      simp only [Node.at_] at hat
      obtain ⟨c, hc, hat⟩ := Option.bind_eq_some_iff.mp hat
      exact ⟨c, hc, q, t, hq, hat⟩
  · rintro ⟨c, hc, q, t, hq, hat⟩
    refine ⟨i :: q, t, ?_, ?_⟩
    · simp only [Path.properPrefix, decide_true, Bool.true_and]
      exact hq
    · simp only [Node.at_, hc, Option.bind_some]
      exact hat

/-- **No address of a node is below one of its references**: a reference is a leaf. A step of
`Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.not_belowRef_of_mem (n : Node Op) {a : List Nat} (ha : a ∈ Node.addresses n) :
    ¬ n.BelowRef a := by
  rintro ⟨q, t, hq, hat⟩
  obtain ⟨r, hr, rfl⟩ := (Path.properPrefix_eq_true_iff q a).mp hq
  have hsome := (mem_addresses_iff n (q ++ r)).mp ha
  rw [Node.at_append, hat, Option.bind_some] at hsome
  obtain ⟨i, r', rfl⟩ := List.exists_cons_of_ne_nil hr
  simp only [Node.at_, Node.child_ref, Option.bind_none, Option.isSome_none,
    Bool.false_eq_true] at hsome

/-! ## A round at the address list -/

/-- An address of a child's list starts with the child's index. A step of
`Eff.addresses_expandRefs`; its other consumer is the table at the source's addresses
(`Sketch.sourceAnnotate_eq_sourceTable`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.mem_childAddresses {n : Node Op} {i : Nat} {x : List Nat}
    (hx : x ∈ n.childAddresses i) : ∃ b, x = i :: b := by
  unfold Node.childAddresses at hx
  split at hx
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨b, rfl⟩
  · cases hx

/-- **A round keeps the address list outside the copies**: a filter that keeps no address below
a reference of the node answers the same on the node and on its round. At a reference the round
puts a copy, whose addresses below the root the filter drops. Elsewhere the round commutes with
each child (`Node.child_expandRound`). A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.addresses_expandRound_filter (orig : Node Op) (n : Node Op)
    (keep : List Nat → Bool) (hkeep : ∀ a, keep a = true → ¬ n.BelowRef a) :
    (Node.addresses (Node.expandRound orig n)).filter keep = (Node.addresses n).filter keep := by
  cases hr : n.refTarget? with
  | some t =>
    obtain rfl := Node.eq_of_refTarget? hr
    rw [Node.addresses_eq_cons (Node.expandRound orig _), Node.addresses_eq_cons (.layer (.ref t))]
    have hdrop : ∀ i,
        ((Node.expandRound orig (.layer (.ref t))).childAddresses i).filter keep = [] := by
      intro i
      refine List.filter_eq_nil_of_all_false fun x hx => ?_
      obtain ⟨b, rfl⟩ := Node.mem_childAddresses hx
      cases hk : keep (i :: b) with
      | false => rfl
      | true => exact absurd (Node.belowRef_ref t i b) (hkeep _ hk)
    have hnone : ∀ i, (Node.layer (.ref t) : Node Op).childAddresses i = [] := by
      intro i
      simp only [Node.childAddresses, Node.child_ref]
    simp only [List.filter_cons, List.filter_append, hdrop, hnone, List.append_nil,
      List.filter_nil]
  | none =>
    have hn := Node.ne_ref_of_refTarget? hr
    rw [Node.addresses_eq_cons (Node.expandRound orig n), Node.addresses_eq_cons n]
    have hchild : ∀ i, ((Node.expandRound orig n).childAddresses i).filter keep =
        (n.childAddresses i).filter keep := by
      intro i
      unfold Node.childAddresses
      rw [Node.child_expandRound orig n i hn]
      cases hc : n.child i with
      | none => rfl
      | some c =>
        have := Node.sizeOf_child_lt n i c hc
        simp only [Option.map_some, List.filter_map]
        congr 1
        refine Node.addresses_expandRound_filter orig c (keep ∘ (i :: ·)) ?_
        intro a hk hb
        exact hkeep (i :: a) hk ((Node.belowRef_cons hn i a).mpr ⟨c, hc, hb⟩)
    simp only [List.filter_cons, List.filter_append, hchild]
termination_by sizeOf n

/-! ## The references of a round -/

/-- **A reference of a round stands at or below a reference of the node**: off the references,
the round keeps each constructor. A step of `Eff.addresses_expandRefs`. Its consumer is
`Node.belowRef_of_expandRound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.ref_expandRound (orig : Node Op) : ∀ (s : List Nat) (n : Node Op) (t : List Nat),
    (Node.expandRound orig n).at_ s = some (.layer (.ref t)) →
      ∃ s0 u t0, s = s0 ++ u ∧ n.at_ s0 = some (.layer (.ref t0))
  | [], n, t, h => by
    cases hr : n.refTarget? with
    | some t0 => exact ⟨[], [], t0, rfl, by rw [Node.eq_of_refTarget? hr]; rfl⟩
    | none =>
      have h1 := Node.refTarget?_expandRound orig hr
      simp only [Node.at_, Option.some.injEq] at h
      rw [h] at h1
      cases h1
  | i :: rest, n, t, h => by
    cases hr : n.refTarget? with
    | some t0 => exact ⟨[], i :: rest, t0, rfl, by rw [Node.eq_of_refTarget? hr]; rfl⟩
    | none =>
      have hn := Node.ne_ref_of_refTarget? hr
      simp only [Node.at_, Node.child_expandRound orig n i hn] at h
      cases hc : n.child i with
      | none =>
        rw [hc] at h
        cases h
      | some c =>
        rw [hc, Option.map_some, Option.bind_some] at h
        obtain ⟨s0, u, t0, rfl, hat⟩ := Node.ref_expandRound orig rest c t h
        refine ⟨i :: s0, u, t0, rfl, ?_⟩
        simp only [Node.at_, hc, Option.bind_some]
        exact hat

/-- **Below a reference of a round, below a reference of the node.** A step of
`Eff.addresses_expandRefs`. Its consumer is `Eff.addresses_rounds_filter`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.belowRef_of_expandRound (orig : Node Op) {n : Node Op} {a : List Nat}
    (h : (Node.expandRound orig n).BelowRef a) : n.BelowRef a := by
  obtain ⟨q, t, hq, hat⟩ := h
  obtain ⟨s0, u, t0, rfl, hat0⟩ := Node.ref_expandRound orig q n t hat
  obtain ⟨r, hr, rfl⟩ := (Path.properPrefix_eq_true_iff (s0 ++ u) a).mp hq
  refine ⟨s0, t0, (Path.properPrefix_eq_true_iff s0 _).mpr
    ⟨u ++ r, ?_, by rw [List.append_assoc]⟩, hat0⟩
  intro hnil
  exact hr (List.append_eq_nil_iff.mp hnil).2

/-- **The rounds keep the address list outside the copies**: each round against the same
original program, as `Eff.expandRefs` runs them. A step of `Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.addresses_rounds_filter (orig : Node Op) (keep : List Nat → Bool) :
    ∀ (xs : List Nat) (e : Eff Op), (∀ a, keep a = true → ¬ (Node.eff e).BelowRef a) →
      (Node.addresses (.eff (xs.foldl (fun acc _ => Eff.expandRound orig acc) e))).filter keep =
        (Node.addresses (.eff e)).filter keep
  | [], _, _ => rfl
  | _ :: xs, e, hkeep => by
    rw [List.foldl_cons, Eff.addresses_rounds_filter orig keep xs (Eff.expandRound orig e)
      (fun a hk hb => hkeep a hk (Node.belowRef_of_expandRound orig (n := .eff e) hb))]
    exact Node.addresses_expandRound_filter orig (.eff e) keep hkeep

/-! ## The reference sites -/

/-- **Below a site, below a reference**: an address is strictly below one of a program's
reference sites exactly when it is below one of its references. A step of
`Eff.addresses_expandRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem belowSite_refSites_iff (root : Eff Op) (a : List Nat) :
    Table.belowSite ((root.refSites []).map (·.1)) a = true ↔ (Node.eff root).BelowRef a := by
  unfold Table.belowSite
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, hp⟩
    obtain ⟨⟨s', t⟩, hmem, rfl⟩ := List.mem_map.mp hs
    exact ⟨s', t, hp, at_of_mem_refSites (x := (s', t)) hmem⟩
  · rintro ⟨q, t, hq, hat⟩
    exact ⟨q, List.mem_map.mpr ⟨(q, t), mem_refSites_of_at hat, rfl⟩, hq⟩

/-! ## The address map -/

/-- **The address map of the expansion**: the expansion's addresses that are not strictly below
a reference site of the program are the program's addresses, in their order. So every address of
the program is an address of its expansion, and the copies hold the rest. It holds at every
program, its references well formed or not. The rounds keep the filtered list
(`Eff.addresses_rounds_filter`), and the program's own addresses are below no reference
(`Node.not_belowRef_of_mem`). A step of `source-annotation-agrees`. Its consumer is
`Sketch.sourceAnnotate_eq_sourceTable` (`Laws/Program/SourceTable.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.addresses_expandRefs (root : Eff Op) :
    (Node.addresses (.eff root.expandRefs)).filter
        (fun a => !Table.belowSite ((root.refSites []).map (·.1)) a) =
      Node.addresses (.eff root) := by
  have hkeep : ∀ a, (!Table.belowSite ((root.refSites []).map (·.1)) a) = true →
      ¬ (Node.eff root).BelowRef a := by
    intro a hk hb
    rw [Bool.not_eq_true', ← Bool.not_eq_true, belowSite_refSites_iff] at hk
    exact hk hb
  unfold Eff.expandRefs
  rw [Eff.addresses_rounds_filter _ _ _ root hkeep]
  refine List.filter_eq_self_of_all fun a ha => ?_
  rw [Bool.not_eq_true', ← Bool.not_eq_true, belowSite_refSites_iff]
  exact Node.not_belowRef_of_mem _ ha

/-- **Every address of a program is an address of its expansion.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceTable_find`
(`Laws/Program/SourceTable.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.mem_addresses_expandRefs (root : Eff Op) {a : List Nat}
    (ha : a ∈ Node.addresses (.eff root)) : a ∈ Node.addresses (.eff root.expandRefs) := by
  rw [← Eff.addresses_expandRefs root] at ha
  exact (List.mem_filter.mp ha).1

end Effect4.Program
