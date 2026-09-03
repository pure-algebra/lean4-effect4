import Effect4.Target.TypeScript.StructureOrder

/-!
# Computed dominator facts for structured lexical scope

For reducible graphs whose declared sources and targets lie within the node
range, the pinned CHK computation supplies both premises of `DominatorFacts`.
The proof follows its actual DFS, RPO fold, intersection fuel, table updates
and finite iteration. It uses earlier-position ancestry rather than assuming
that the iteration has converged. All intermediate graph and table facts are
private; the public wrappers discharge the old conditional scoping premises.

The conclusion concerns the existing computed parent-chain predicate and
lexical break/continue binding. It does not assert graph-theoretic immediate
dominance, structured execution agreement, sufficient loop fuel, or interrupt
denotation. Those remain separate T4 obligations.
-/

set_option autoImplicit false

open TypeScript Effects Effect4.Target.EffectV4

namespace Effect4.Target.Structured
open TypeScript.Structure

private theorem findIdx_at_of_nodup : ∀ (xs : List Nat) (i : Nat) (hi : i < xs.length),
    xs.Nodup → xs.findIdx? (· = xs[i]) = some i := by
  intro xs
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
      intro i hi nodup
      obtain ⟨notMem, tailNodup⟩ := List.nodup_cons.mp nodup
      cases i with
      | zero => simp [List.findIdx?_cons]
      | succ i =>
          have tailBound : i < xs.length := by simpa using hi
          have headNe : x ≠ xs[i] := by
            intro same
            exact notMem (same ▸ List.getElem_mem tailBound)
          simpa [List.findIdx?_cons, headNe] using
            ih i tailBound tailNodup

private theorem index_rpo_at (g : Structure.Graph) (i : Nat) (hi : i < (Structure.rpo g).length) :
    Structure.index g (Structure.rpo g)[i] = i := by
  unfold Structure.index
  rw [findIdx_at_of_nodup _ i hi (rpo_nodup g)]

private theorem forward_target_later (g : Structure.Graph) (source target : Nat)
    (forward : Structure.isBackEdge g source target = false) :
    Structure.index g source < Structure.index g target := by
  simpa [Structure.isBackEdge] using forward

private theorem reachable_of_reducible {g : Structure.Graph} (reducible : Structure.reducible g = true)
    {node : Nat} (bound : node < g.size) : node ∈ Structure.rpo g := by
  have nodeChecks := List.all_eq_true.mp reducible node (List.mem_range.mpr bound)
  exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp nodeChecks).1

private theorem graphOf_sourceClosed (blocks : List (RawBlock String)) (entry : BlockId) :
    ∀ source target, target ∈ (Flow.graphOf blocks entry).succs source →
      source < (Flow.graphOf blocks entry).size := by
  intro source target member
  unfold Flow.graphOf at member ⊢
  dsimp only at member ⊢
  cases found : blocks[source]? with
  | none => rw [found] at member; simp at member
  | some block =>
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
      exact bound

private theorem emitWith_reducible {α : Type} (g : Structure.Graph) (shapes : Structuring.Shapes α)
    (body : Nat → (Nat → Option (List α)) → Option (List α)) {out : List α}
    (emitted : Structuring.emitWith g shapes body = some out) : Structure.reducible g = true := by
  cases h : Structure.reducible g with
  | false =>
      have never : Structuring.emitWith g shapes body = none := by
        unfold Structuring.emitWith
        rw [h]
        rfl
      rw [never] at emitted
      contradiction
  | true => rfl

private def TableBounded (n : Nat) (doms : List (Option Nat)) : Prop :=
  ∀ p, some p ∈ doms → p < n

private theorem intersect_bounded (n : Nat) (doms : List (Option Nat)) (bounded : TableBounded n doms) :
    ∀ fuel a b, a < n → b < n → idoms.intersect fuel doms a b < n := by
  intro fuel
  induction fuel with
  | zero => intro a b ha hb; exact ha
  | succ fuel ih =>
      intro a b ha hb
      rw [idoms.intersect]
      split
      · exact ha
      · split
        · split
          · next a' found => exact ih a' b (bounded a' (List.mem_of_getElem? found)) hb
          · exact ha
        · split
          · next b' found => exact ih a b' ha (bounded b' (List.mem_of_getElem? found))
          · exact ha

private theorem mem_set_subset {α : Type} (l : List α) (i : Nat) (a x : α)
    (member : x ∈ l.set i a) : x = a ∨ x ∈ l := by
  induction l generalizing i with
  | nil => simp at member
  | cons first rest ih =>
      cases i with
      | zero =>
          rcases List.mem_cons.mp member with same | tail
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem first tail)
      | succ i =>
          rcases List.mem_cons.mp member with same | tail
          · exact Or.inr (same ▸ List.mem_cons_self)
          · rcases ih i tail with same | old
            · exact Or.inl same
            · exact Or.inr (List.mem_cons_of_mem first old)

private theorem TableBounded.set {n : Nat} {doms : List (Option Nat)} (bounded : TableBounded n doms)
    (index parent : Nat) (bound : parent < n) : TableBounded n (doms.set index (some parent)) := by
  intro p member
  rcases mem_set_subset doms index (some parent) (some p) member with same | old
  · cases same
    exact bound
  · exact bounded p old

private theorem index_lt_of_mem (g : Graph) {node : Nat} (member : node ∈ rpo g) :
    index g node < (rpo g).length := by
  obtain ⟨i, hi, located⟩ := List.mem_iff_getElem.mp member
  rw [← located, index_rpo_at g i hi]
  exact hi

private def update (g : Graph) (doms : List (Option Nat)) (node : Nat) : List (Option Nat) :=
  let i := index g node
  if i = 0 then doms
  else
    let processed := (preds g node).filterMap fun p =>
      match doms[index g p]? with
      | some (some _) => some (index g p)
      | _ => if index g p = 0 then some 0 else none
    match processed with
    | [] => doms
    | first :: rest =>
        let newIdom := rest.foldl (fun acc p => idoms.intersect (rpo g).length doms acc p) first
        doms.set i (some newIdom)

private def step (g : Graph) (doms : List (Option Nat)) : List (Option Nat) :=
  (rpo g).foldl (update g) doms

private theorem update_preserves (g : Graph) (doms : List (Option Nat)) (node : Nat)
    (bounded : TableBounded (rpo g).length doms) :
    (update g doms node).length = doms.length ∧ TableBounded (rpo g).length (update g doms node) := by
  unfold update
  dsimp only
  split
  · exact ⟨rfl, bounded⟩
  · have processedBound : ∀ p, p ∈ ((preds g node).filterMap fun p =>
        match doms[index g p]? with
        | some (some _) => some (index g p)
        | _ => if index g p = 0 then some 0 else none) → p < (rpo g).length := by
      intro p member
      obtain ⟨predecessor, predMember, produced⟩ := List.mem_filterMap.mp member
      have predBound := index_lt_of_mem g (List.mem_filter.mp predMember).1
      split at produced
      · cases produced
        exact predBound
      · split at produced
        · cases produced
          omega
        · cases produced
    split
    · exact ⟨rfl, bounded⟩
    · next first rest found =>
        have firstBound : first < (rpo g).length := processedBound first (by rw [found]; simp)
        have restBound : ∀ p, p ∈ rest → p < (rpo g).length := by
          intro p member
          apply processedBound p
          rw [found]
          exact List.mem_cons_of_mem first member
        have foldedBound : rest.foldl
            (fun acc p => idoms.intersect (rpo g).length doms acc p) first < (rpo g).length := by
          apply List.foldlRecOn rest _ (motive := fun acc => acc < (rpo g).length) firstBound
          intro acc hAcc p member
          exact intersect_bounded (rpo g).length doms bounded _ acc p hAcc (restBound p member)
        exact ⟨List.length_set, bounded.set _ _ foldedBound⟩

private theorem step_preserves (g : Graph) (doms : List (Option Nat))
    (bounded : TableBounded (rpo g).length doms) :
    (step g doms).length = doms.length ∧ TableBounded (rpo g).length (step g doms) := by
  unfold step
  apply List.foldlRecOn (rpo g) (update g) (motive := fun next =>
    next.length = doms.length ∧ TableBounded (rpo g).length next) ⟨rfl, bounded⟩
  intro state prior node member
  have next := update_preserves g state node prior.2
  exact ⟨next.1.trans prior.1, next.2⟩

private theorem iterate_preserves (g : Graph) : ∀ fuel doms,
    TableBounded (rpo g).length doms →
    (idoms.iterate (step g) fuel doms).length = doms.length ∧
      TableBounded (rpo g).length (idoms.iterate (step g) fuel doms) := by
  intro fuel
  induction fuel with
  | zero => intro doms bounded; exact ⟨rfl, bounded⟩
  | succ fuel ih =>
      intro doms bounded
      rw [idoms.iterate]
      split
      · exact ⟨rfl, bounded⟩
      · have stepped := step_preserves g doms bounded
        have rest := ih (step g doms) stepped.2
        exact ⟨rest.1.trans stepped.1, rest.2⟩

private def initial (n : Nat) : List (Option Nat) :=
  (List.range n).map fun i => if i = 0 then some 0 else none

private theorem initial_length (n : Nat) : (initial n).length = n := by
  simp [initial]

private theorem initial_bounded (n : Nat) : TableBounded n (initial n) := by
  intro p member
  obtain ⟨i, member, produced⟩ := List.mem_map.mp member
  have bound := List.mem_range.mp member
  split at produced
  · next zero => cases produced; omega
  · cases produced

/- The local update/pass factors are definitionally the pinned algorithm. -/
private theorem idoms_exact (g : Graph) :
    idoms g = idoms.iterate (step g) ((rpo g).length + 1) (initial (rpo g).length) := by rfl

private theorem idoms_bounded (g : Graph) : TableBounded (rpo g).length (idoms g) := by
  rw [idoms_exact]
  exact (iterate_preserves g _ _ (initial_bounded _)).2

private theorem idom_position (g : Graph) {child parent : Nat}
    (up : idom g child = some parent) :
    ∃ parentIndex, (idoms g)[index g child]? = some (some parentIndex) ∧
      index g parent = parentIndex := by
  unfold idom at up
  split at up
  · cases up
  · split at up
    · next p found =>
        refine ⟨p, found, ?_⟩
        obtain ⟨bound, atParent⟩ := List.getElem?_eq_some_iff.mp up
        rw [← atParent]
        exact index_rpo_at g p bound
    · cases up

private theorem rpo_entry_first (g : Graph) : ∃ rest, rpo g = g.entry :: rest := by
  unfold rpo postorder
  rw [postorder.visit]
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  exact ⟨_, rfl⟩

private theorem rpo_length_pos (g : Graph) : 0 < (rpo g).length := by
  obtain ⟨rest, first⟩ := rpo_entry_first g
  rw [first]
  simp

private theorem index_entry_zero (g : Graph) : index g g.entry = 0 := by
  obtain ⟨rest, first⟩ := rpo_entry_first g
  unfold index
  rw [first, List.findIdx?_cons]
  simp

private theorem update_zero (g : Graph) (doms : List (Option Nat)) (node : Nat) :
    (update g doms node)[0]? = doms[0]? := by
  unfold update
  dsimp only
  split
  · rfl
  · next nonzero =>
      split
      · rfl
      · exact List.getElem?_set_ne nonzero

private theorem step_zero (g : Graph) (doms : List (Option Nat)) : (step g doms)[0]? = doms[0]? := by
  unfold step
  apply List.foldlRecOn (rpo g) (update g) (motive := fun next => next[0]? = doms[0]?) rfl
  intro state prior node member
  exact (update_zero g state node).trans prior

private structure VisitTree (g : Graph) (root : Nat) (before after : List Nat) : Prop where
  grows : before.Sublist after
  parents : ∀ target, target ∈ after → target ∈ before ∨ target = root ∨
    ∃ source, target ∈ g.succs source ∧ [target, source].Sublist after

private structure ForestTree (g : Graph) (root : Nat) (before after : List Nat) : Prop where
  grows : before.Sublist after
  parents : ∀ target, target ∈ after → target ∈ before ∨ target ∈ g.succs root ∨
    ∃ source, target ∈ g.succs source ∧ [target, source].Sublist after

private theorem visit_tree (g : Graph) : ∀ fuel seen order root,
    VisitTree g root order (postorder.visit g fuel seen order root).2 := by
  intro fuel
  induction fuel with
  | zero => intro seen order root; exact ⟨List.Sublist.refl _, fun _ h => Or.inl h⟩
  | succ fuel ih =>
      intro seen order root
      rw [postorder.visit]
      split
      · exact ⟨List.Sublist.refl _, fun _ h => Or.inl h⟩
      · have forest : ForestTree g root order ((g.succs root).foldl
            (fun (state : List Nat × List Nat) next =>
              postorder.visit g fuel state.1 state.2 next) (root :: seen, order)).2 := by
          apply List.foldlRecOn (g.succs root) _
            (motive := fun state : List Nat × List Nat => ForestTree g root order state.2)
            ⟨List.Sublist.refl _, fun _ h => Or.inl h⟩
          intro state prior next declared
          have one := ih state.1 state.2 next
          refine ⟨prior.grows.trans one.grows, ?_⟩
          intro target member
          rcases one.parents target member with old | atRoot | parent
          · rcases prior.parents target old with initial | atChild | parent
            · exact Or.inl initial
            · exact Or.inr (Or.inl atChild)
            · obtain ⟨source, edge, inside⟩ := parent
              exact Or.inr (Or.inr ⟨source, edge, inside.trans one.grows⟩)
          · exact Or.inr (Or.inl (atRoot ▸ declared))
          · exact Or.inr (Or.inr parent)
        dsimp only at forest ⊢
        generalize hfold : List.foldl
          (fun (state : List Nat × List Nat) next =>
            postorder.visit g fuel state.1 state.2 next)
          (root :: seen, order) (g.succs root) = after at forest ⊢
        obtain ⟨seenAfter, orderAfter⟩ := after
        dsimp only at forest ⊢
        refine ⟨forest.grows.trans (List.sublist_append_left _ _), ?_⟩
        intro target member
        rcases List.mem_append.mp member with prior | last
        · rcases forest.parents target prior with initial | child | parent
          · exact Or.inl initial
          · refine Or.inr (Or.inr ⟨root, child, ?_⟩)
            exact (List.singleton_sublist.mpr prior).append (List.Sublist.refl [root])
          · obtain ⟨source, edge, inside⟩ := parent
            exact Or.inr (Or.inr ⟨source, edge,
              inside.trans (List.sublist_append_left _ _)⟩)
        · exact Or.inr (Or.inl (by simpa using last))

private theorem rpo_forward_predecessor (g : Graph) {target : Nat}
    (member : target ∈ rpo g) (notEntry : target ≠ g.entry) :
    ∃ source, target ∈ g.succs source ∧ source ∈ rpo g ∧
      index g source < index g target := by
  have tree := visit_tree g (g.size + 1) [] [] g.entry
  have inPost : target ∈ postorder g := by simpa [rpo] using member
  rcases tree.parents target inPost with impossible | entry | parent
  · exact False.elim (List.not_mem_nil impossible)
  · exact False.elim (notEntry entry)
  · obtain ⟨source, edge, pair⟩ := parent
    have forwardPair : [source, target].Sublist (rpo g) := by
      simpa [rpo, postorder] using pair.reverse
    have indexed := List.pairwise_iff_forall_sublist.mp (rpo_index_order g) forwardPair
    refine ⟨source, edge, ?_, indexed⟩
    exact forwardPair.subset List.mem_cons_self

private def Descending (doms : List (Option Nat)) : Prop :=
  ∀ (slot parent : Nat), doms[slot]? = some (some parent) → parent ≤ slot

private theorem intersect_le_left (doms : List (Option Nat)) (descending : Descending doms) :
    ∀ fuel a b, idoms.intersect fuel doms a b ≤ a := by
  intro fuel
  induction fuel with
  | zero => intro a b; exact Nat.le_refl _
  | succ fuel ih =>
      intro a b
      rw [idoms.intersect]
      split
      · exact Nat.le_refl _
      · split
        · split
          · next a' found => exact Nat.le_trans (ih a' b) (descending a a' found)
          · exact Nat.le_refl _
        · split
          · next b' found => exact ih a b'
          · exact Nat.le_refl _

private def processedEntry (g : Graph) (doms : List (Option Nat)) (p : Nat) : Option Nat :=
  match doms[index g p]? with
  | some (some _) => some (index g p)
  | _ => if index g p = 0 then some 0 else none

private def processed (g : Graph) (doms : List (Option Nat)) (node : Nat) : List Nat :=
  (preds g node).filterMap (processedEntry g doms)

private theorem processedEntry_eq_index (g : Graph) (doms : List (Option Nat)) (node p : Nat)
    (produced : processedEntry g doms node = some p) : p = index g node := by
  unfold processedEntry at produced
  split at produced
  · cases produced; rfl
  · split at produced
    · next zero => cases produced; exact zero.symm
    · cases produced

private theorem processed_order (g : Graph) (doms : List (Option Nat)) (node : Nat) :
    (processed g doms node).Pairwise (· < ·) := by
  apply List.Pairwise.filterMap _ _ (List.Pairwise.filter _ (rpo_index_order g))
  intro a a' earlier b gotB b' gotB'
  rw [processedEntry_eq_index g doms a b gotB,
    processedEntry_eq_index g doms a' b' gotB']
  exact earlier

private theorem processed_mem_of_defined (g : Graph) (doms : List (Option Nat)) {node pred parent : Nat}
    (reachable : pred ∈ rpo g) (edge : node ∈ g.succs pred)
    (defined : doms[index g pred]? = some (some parent)) :
    index g pred ∈ processed g doms node := by
  apply List.mem_filterMap.mpr
  refine ⟨pred, List.mem_filter.mpr ⟨reachable, List.contains_iff_mem.mpr edge⟩, ?_⟩
  unfold processedEntry
  rw [defined]

private theorem Descending.set {doms : List (Option Nat)} (descending : Descending doms)
    (slot parent : Nat) (backward : parent ≤ slot) : Descending (doms.set slot (some parent)) := by
  intro i p found
  rw [List.getElem?_set] at found
  split at found
  · next same =>
      split at found
      · cases found
        exact same ▸ backward
      · cases found
  · exact descending i p found

private theorem fold_intersect_le_first (g : Graph) (doms : List (Option Nat))
    (descending : Descending doms) (first : Nat) (rest : List Nat) :
    rest.foldl (fun acc p => idoms.intersect (rpo g).length doms acc p) first ≤ first := by
  apply List.foldlRecOn rest _ (motive := fun acc => acc ≤ first) (Nat.le_refl _)
  intro acc prior p member
  exact Nat.le_trans (intersect_le_left doms descending _ acc p) prior

private def PrefixDefined (upto : Nat) (doms : List (Option Nat)) : Prop :=
  ∀ slot, slot < upto → ∃ parent, doms[slot]? = some (some parent)

private theorem update_form (g : Graph) (doms : List (Option Nat)) (node : Nat) :
    update g doms node =
      if index g node = 0 then doms
      else match processed g doms node with
        | [] => doms
        | first :: rest => doms.set (index g node)
            (some (rest.foldl (fun acc p => idoms.intersect (rpo g).length doms acc p) first)) := by rfl

private theorem update_length (g : Graph) (doms : List (Option Nat)) (node : Nat) :
    (update g doms node).length = doms.length := by
  rw [update_form]
  split
  · rfl
  · split
    · rfl
    · exact List.length_set

private theorem update_desc_prefix (g : Graph) (doms : List (Option Nat)) (node : Nat)
    (sized : doms.length = (rpo g).length)
    (root : doms[0]? = some (some 0)) (descending : Descending doms)
    (definedPrefix : PrefixDefined (index g node) doms) (member : node ∈ rpo g) :
    Descending (update g doms node) ∧ PrefixDefined (index g node + 1) (update g doms node) := by
  by_cases zero : index g node = 0
  · rw [update_form, if_pos zero]
    refine ⟨descending, ?_⟩
    intro slot bound
    have same : slot = 0 := by omega
    subst slot
    exact ⟨0, root⟩
  · have notEntry : node ≠ g.entry := by
      intro same
      subst node
      exact zero (index_entry_zero g)
    obtain ⟨pred, edge, reachable, earlier⟩ := rpo_forward_predecessor g member notEntry
    obtain ⟨parent, defined⟩ := definedPrefix (index g pred) earlier
    have selected := processed_mem_of_defined g doms reachable edge defined
    have ordered := processed_order g doms node
    cases found : processed g doms node with
    | nil => rw [found] at selected; exact False.elim (List.not_mem_nil selected)
    | cons first rest =>
        rw [found] at selected ordered
        have firstLe : first ≤ index g pred := by
          rcases List.mem_cons.mp selected with same | inRest
          · omega
          · exact Nat.le_of_lt ((List.pairwise_cons.mp ordered).1 _ inRest)
        have foldedLe := fold_intersect_le_first g doms descending first rest
        have parentLe : rest.foldl (fun acc p => idoms.intersect (rpo g).length doms acc p) first
            ≤ index g node := by omega
        rw [update_form, if_neg zero, found]
        refine ⟨descending.set _ _ parentLe, ?_⟩
        intro slot bound
        by_cases same : slot = index g node
        · subst slot
          refine ⟨_, List.getElem?_set_self ?_⟩
          rw [sized]
          exact index_lt_of_mem g member
        · have before : slot < index g node := by omega
          obtain ⟨p, old⟩ := definedPrefix slot before
          refine ⟨p, ?_⟩
          rw [List.getElem?_set_ne (Ne.symm same)]
          exact old

private theorem step_length (g : Graph) (doms : List (Option Nat)) :
    (step g doms).length = doms.length := by
  unfold step
  apply List.foldlRecOn (rpo g) (update g) (motive := fun next => next.length = doms.length) rfl
  intro state prior node member
  exact (update_length g state node).trans prior

private theorem initial_zero (n : Nat) (positive : 0 < n) : (initial n)[0]? = some (some 0) := by
  unfold initial
  rw [List.getElem?_map]
  simp [positive]

private def Strict (doms : List (Option Nat)) : Prop :=
  ∀ (slot parent : Nat), doms[slot]? = some (some parent) → slot = 0 ∨ parent < slot

private def ParentClosed (doms : List (Option Nat)) : Prop :=
  ∀ (slot parent : Nat), doms[slot]? = some (some parent) →
    ∃ grand, doms[parent]? = some (some grand)

private structure ForestTable (doms : List (Option Nat)) : Prop where
  root : doms[0]? = some (some 0)
  strict : Strict doms
  closed : ParentClosed doms

private theorem ForestTable.descending {doms : List (Option Nat)} (tree : ForestTable doms) :
    Descending doms := by
  intro slot parent found
  rcases tree.strict slot parent found with zero | before
  · subst slot
    rw [tree.root] at found
    cases found
    exact Nat.le_refl _
  · exact Nat.le_of_lt before

private theorem update_parent (g : Graph) (doms : List (Option Nat)) (node : Nat)
    (descending : Descending doms) (definedPrefix : PrefixDefined (index g node) doms)
    (member : node ∈ rpo g) (nonzero : index g node ≠ 0) :
    ∃ parent, parent < index g node ∧ update g doms node = doms.set (index g node) (some parent) := by
  have notEntry : node ≠ g.entry := by
    intro same
    subst node
    exact nonzero (index_entry_zero g)
  obtain ⟨pred, edge, reachable, earlier⟩ := rpo_forward_predecessor g member notEntry
  obtain ⟨parent, defined⟩ := definedPrefix (index g pred) earlier
  have selected := processed_mem_of_defined g doms reachable edge defined
  have ordered := processed_order g doms node
  cases found : processed g doms node with
  | nil => rw [found] at selected; exact False.elim (List.not_mem_nil selected)
  | cons first rest =>
      rw [found] at selected ordered
      have firstLe : first ≤ index g pred := by
        rcases List.mem_cons.mp selected with same | inRest
        · omega
        · exact Nat.le_of_lt ((List.pairwise_cons.mp ordered).1 _ inRest)
      have foldedLe := fold_intersect_le_first g doms descending first rest
      refine ⟨_, Nat.lt_of_le_of_lt (Nat.le_trans foldedLe firstLe) earlier, ?_⟩
      rw [update_form, if_neg nonzero, found]

private theorem Strict.set {doms : List (Option Nat)} (strict : Strict doms)
    (slot parent : Nat) (before : parent < slot) : Strict (doms.set slot (some parent)) := by
  intro i p found
  rw [List.getElem?_set] at found
  split at found
  · next same =>
      split at found
      · cases found
        exact Or.inr (same ▸ before)
      · cases found
  · exact strict i p found

private theorem ParentClosed.set {doms : List (Option Nat)} (closed : ParentClosed doms)
    (slot parent : Nat) (bound : slot < doms.length)
    (parentDefined : ∃ grand, doms[parent]? = some (some grand)) :
    ParentClosed (doms.set slot (some parent)) := by
  intro i p found
  by_cases updated : i = slot
  · subst i
    rw [List.getElem?_set_self bound] at found
    cases found
    by_cases self : parent = slot
    · subst parent
      exact ⟨slot, List.getElem?_set_self bound⟩
    · obtain ⟨grand, old⟩ := parentDefined
      exact ⟨grand, by rw [List.getElem?_set_ne (Ne.symm self)]; exact old⟩
  · rw [List.getElem?_set_ne (Ne.symm updated)] at found
    by_cases parentUpdated : p = slot
    · subst p
      exact ⟨parent, List.getElem?_set_self bound⟩
    · obtain ⟨grand, old⟩ := closed i p found
      exact ⟨grand, by rw [List.getElem?_set_ne (Ne.symm parentUpdated)]; exact old⟩

private theorem update_forest (g : Graph) (doms : List (Option Nat)) (node : Nat)
    (sized : doms.length = (rpo g).length) (tree : ForestTable doms)
    (definedPrefix : PrefixDefined (index g node) doms) (member : node ∈ rpo g) :
    ForestTable (update g doms node) := by
  by_cases zero : index g node = 0
  · rw [update_form, if_pos zero]
    exact tree
  · obtain ⟨parent, before, updated⟩ := update_parent g doms node tree.descending definedPrefix member zero
    refine ⟨(update_zero g doms node).trans tree.root, ?_, ?_⟩
    · rw [updated]
      exact tree.strict.set _ _ before
    · rw [updated]
      exact tree.closed.set _ _ (by rw [sized]; exact index_lt_of_mem g member) (definedPrefix parent before)

private theorem fold_forest_prefix (g : Graph) : ∀ (nodes : List Nat) (offset : Nat)
    (doms : List (Option Nat)),
    (∀ (i : Nat) (hi : i < nodes.length), index g nodes[i] = offset + i) →
    (∀ node, node ∈ nodes → node ∈ rpo g) →
    doms.length = (rpo g).length → ForestTable doms → PrefixDefined offset doms →
    ForestTable (nodes.foldl (update g) doms) ∧
      PrefixDefined (offset + nodes.length) (nodes.foldl (update g) doms) := by
  intro nodes
  induction nodes with
  | nil => intro offset doms positions members sized tree definedPrefix
           exact ⟨tree, definedPrefix⟩
  | cons node rest ih =>
      intro offset doms positions members sized tree definedPrefix
      have here : index g node = offset := by
        have first := positions 0 (by simp)
        change index g node = offset + 0 at first
        exact first.trans (Nat.add_zero offset)
      have definedAt : PrefixDefined (index g node) doms := by simpa [here] using definedPrefix
      have next := update_desc_prefix g doms node sized tree.root tree.descending
        definedAt (members node List.mem_cons_self)
      have after := ih (offset + 1) (update g doms node)
        (fun i hi => by
          have atNext := positions (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atNext)
        (fun next mem => members next (List.mem_cons_of_mem node mem))
        ((update_length g doms node).trans sized)
        (update_forest g doms node sized tree definedAt (members node List.mem_cons_self))
        (by simpa [here] using next.2)
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using after

private theorem step_forest (g : Graph) (doms : List (Option Nat))
    (sized : doms.length = (rpo g).length) (tree : ForestTable doms) :
    ForestTable (step g doms) := by
  have all := fold_forest_prefix g (rpo g) 0 doms
    (fun i hi => by simpa using index_rpo_at g i hi)
    (fun node mem => mem) sized tree
    (by intro slot before; exact False.elim (Nat.not_lt_zero slot before))
  exact all.1

private theorem iterate_forest (g : Graph) : ∀ fuel doms,
    doms.length = (rpo g).length → ForestTable doms →
    ForestTable (idoms.iterate (step g) fuel doms) := by
  intro fuel
  induction fuel with
  | zero => intro doms sized tree; exact tree
  | succ fuel ih =>
      intro doms sized tree
      rw [idoms.iterate]
      split
      · exact tree
      · exact ih (step g doms) ((step_length g doms).trans sized) (step_forest g doms sized tree)

private theorem initial_forest (n : Nat) (positive : 0 < n) : ForestTable (initial n) := by
  have root := initial_zero n positive
  refine ⟨root, ?_, ?_⟩
  · intro slot parent found
    have member := List.mem_of_getElem? found
    obtain ⟨i, member, produced⟩ := List.mem_map.mp member
    split at produced
    · cases produced
      by_cases zero : slot = 0
      · exact Or.inl zero
      · exact Or.inr (Nat.pos_of_ne_zero zero)
    · cases produced
  · intro slot parent found
    have member := List.mem_of_getElem? found
    obtain ⟨i, member, produced⟩ := List.mem_map.mp member
    split at produced
    · cases produced
      exact ⟨0, root⟩
    · cases produced

private theorem idoms_forest (g : Graph) : ForestTable (idoms g) := by
  rw [idoms_exact]
  exact iterate_forest g _ _ (initial_length _) (initial_forest _ (rpo_length_pos g))

/-- A computed parent never occurs later than its child in reverse postorder. -/
theorem idom_index_le (g : Graph) (parent child : Nat)
    (up : idom g child = some parent) : index g parent ≤ index g child := by
  obtain ⟨parentIndex, found, position⟩ := idom_position g up
  rw [position]
  exact (idoms_forest g).descending (index g child) parentIndex found

private inductive Ancestor (doms : List (Option Nat)) (parent : Nat) : Nat → Prop where
  | refl : Ancestor doms parent parent
  | step {node up : Nat} : doms[node]? = some (some up) →
      Ancestor doms parent up → Ancestor doms parent node

private theorem Ancestor.trans {doms : List (Option Nat)} {a b c : Nat}
    (ab : Ancestor doms a b) (bc : Ancestor doms b c) : Ancestor doms a c := by
  induction bc with
  | refl => exact ab
  | step found prior ih => exact .step found ih

private theorem Ancestor.le {doms : List (Option Nat)} {a b : Nat}
    (descending : Descending doms) (ancestry : Ancestor doms a b) : a ≤ b := by
  induction ancestry with
  | refl => exact Nat.le_refl _
  | @step node up found prior ih => exact Nat.le_trans ih (descending node up found)

private theorem Ancestor.defined {doms : List (Option Nat)} {a b : Nat}
    (tree : ForestTable doms) (ancestry : Ancestor doms a b)
    (defined : ∃ parent, doms[b]? = some (some parent)) :
    ∃ parent, doms[a]? = some (some parent) := by
  induction ancestry with
  | refl => exact defined
  | @step node up found prior ih => exact ih (tree.closed node up found)

private theorem defined_lt_length {doms : List (Option Nat)} {node : Nat}
    (defined : ∃ parent, doms[node]? = some (some parent)) : node < doms.length := by
  obtain ⟨parent, found⟩ := defined
  exact (List.getElem?_eq_some_iff.mp found).1

/- Each actual branch decreases the larger index, so table length fuel suffices. -/
private theorem intersect_ancestors (doms : List (Option Nat)) (tree : ForestTable doms) :
    ∀ fuel a b, max a b < fuel →
      (∃ parent, doms[a]? = some (some parent)) →
      (∃ parent, doms[b]? = some (some parent)) →
      Ancestor doms (idoms.intersect fuel doms a b) a ∧
      Ancestor doms (idoms.intersect fuel doms a b) b := by
  intro fuel
  induction fuel with
  | zero => intro a b bound definedA definedB; exact False.elim (Nat.not_lt_zero _ bound)
  | succ fuel ih =>
      intro a b bound definedA definedB
      by_cases same : a = b
      · rw [idoms.intersect, if_pos same]
        subst b
        exact ⟨.refl, .refl⟩
      · rw [idoms.intersect, if_neg same]
        by_cases after : a > b
        · rw [if_pos after]
          obtain ⟨up, found⟩ := definedA
          rw [found]
          have before : up < a := (tree.strict a up found).resolve_left (by omega)
          have smaller := ih up b (by omega) (tree.closed a up found) definedB
          exact ⟨.step found smaller.1, smaller.2⟩
        · rw [if_neg after]
          obtain ⟨up, found⟩ := definedB
          rw [found]
          have before : up < b := (tree.strict b up found).resolve_left (by omega)
          have smaller := ih a up (by omega) definedA (tree.closed b up found)
          exact ⟨smaller.1, .step found smaller.2⟩

private theorem fold_intersect_ancestors (doms : List (Option Nat)) (tree : ForestTable doms)
    (fuel : Nat) (enough : doms.length ≤ fuel) : ∀ (rest : List Nat) (first : Nat),
    (∃ parent, doms[first]? = some (some parent)) →
    (∀ node, node ∈ rest → ∃ parent, doms[node]? = some (some parent)) →
    Ancestor doms (rest.foldl (fun acc p => idoms.intersect fuel doms acc p) first) first ∧
      ∀ node, node ∈ rest →
      Ancestor doms (rest.foldl (fun acc p => idoms.intersect fuel doms acc p) first) node := by
  intro rest
  induction rest with
  | nil => intro first definedFirst definedRest; exact ⟨.refl, fun _ no => False.elim (List.not_mem_nil no)⟩
  | cons next rest ih =>
      intro first definedFirst definedRest
      have definedNext := definedRest next List.mem_cons_self
      have common := intersect_ancestors doms tree fuel first next
        (by have := defined_lt_length definedFirst; have := defined_lt_length definedNext; omega)
        definedFirst definedNext
      have deeper := ih (idoms.intersect fuel doms first next)
        (common.1.defined tree definedFirst)
        (fun node member => definedRest node (List.mem_cons_of_mem next member))
      refine ⟨deeper.1.trans common.1, ?_⟩
      intro node member
      rcases List.mem_cons.mp member with same | inRest
      · subst node
        exact deeper.1.trans common.2
      · exact deeper.2 node inRest

private theorem Ancestor.set_above {doms : List (Option Nat)} {a b slot parent : Nat}
    (descending : Descending doms) (ancestry : Ancestor doms a b)
    (above : b < slot) : Ancestor (doms.set slot (some parent)) a b := by
  induction ancestry with
  | refl => exact .refl
  | @step node up found prior ih =>
      have before := descending node up found
      have upBelow : up < slot := Nat.lt_of_le_of_lt before above
      apply Ancestor.step (up := up)
      · rw [List.getElem?_set_ne (by omega)]
        exact found
      · exact ih upBelow

private theorem processed_defined (g : Graph) (doms : List (Option Nat)) (node p : Nat)
    (root : doms[0]? = some (some 0)) (member : p ∈ processed g doms node) :
    ∃ parent, doms[p]? = some (some parent) := by
  obtain ⟨pred, predMember, produced⟩ := List.mem_filterMap.mp member
  unfold processedEntry at produced
  split at produced
  · next parent found => cases produced; exact ⟨parent, found⟩
  · split at produced
    · cases produced; exact ⟨0, root⟩
    · cases produced

private theorem rpo_get_index (g : Graph) {node : Nat} (member : node ∈ rpo g) :
    (rpo g)[index g node]? = some node := by
  obtain ⟨i, hi, located⟩ := List.mem_iff_getElem.mp member
  rw [← located, index_rpo_at g i hi]
  exact List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩

private theorem index_injective (g : Graph) {a b : Nat} (memberA : a ∈ rpo g)
    (memberB : b ∈ rpo g) (same : index g a = index g b) : a = b := by
  have getA := rpo_get_index g memberA
  have getB := rpo_get_index g memberB
  rw [same, getB] at getA
  exact Option.some.inj getA.symm

private theorem update_forward_ancestor (g : Graph) (doms : List (Option Nat)) (node source : Nat)
    (sized : doms.length = (rpo g).length) (tree : ForestTable doms)
    (definedPrefix : PrefixDefined (index g node) doms)
    (nodeMember : node ∈ rpo g) (sourceMember : source ∈ rpo g)
    (edge : node ∈ g.succs source) (forward : index g source < index g node) :
    ∃ parent, (update g doms node)[index g node]? = some (some parent) ∧
      Ancestor (update g doms node) parent (index g source) := by
  have nonzero : index g node ≠ 0 := by omega
  obtain ⟨sourceParent, definedSource⟩ := definedPrefix (index g source) forward
  have selected := processed_mem_of_defined g doms sourceMember edge definedSource
  cases found : processed g doms node with
  | nil => rw [found] at selected; exact False.elim (List.not_mem_nil selected)
  | cons first rest =>
      have allDefined : ∀ p, p ∈ first :: rest → ∃ parent, doms[p]? = some (some parent) := by
        intro p member
        exact processed_defined g doms node p tree.root (by rw [found]; exact member)
      have common := fold_intersect_ancestors doms tree (rpo g).length (Nat.le_of_eq sized)
        rest first (allDefined first List.mem_cons_self)
        (fun p member => allDefined p (List.mem_cons_of_mem first member))
      have ancestry : Ancestor doms
          (rest.foldl (fun acc p => idoms.intersect (rpo g).length doms acc p) first) (index g source) := by
        rw [found] at selected
        rcases List.mem_cons.mp selected with same | inRest
        · rw [same]; exact common.1
        · exact common.2 _ inRest
      rw [update_form, if_neg nonzero, found]
      refine ⟨_, ?_, ancestry.set_above tree.descending forward⟩
      apply List.getElem?_set_self
      rw [sized]
      exact index_lt_of_mem g nodeMember

private def ForwardParents (g : Graph) (upto : Nat) (doms : List (Option Nat)) : Prop :=
  ∀ source target, source ∈ rpo g → target ∈ rpo g → target ∈ g.succs source →
    index g source < index g target → index g target < upto →
    ∃ parent, doms[index g target]? = some (some parent) ∧ Ancestor doms parent (index g source)

private theorem update_forwardParents (g : Graph) (doms : List (Option Nat)) (node : Nat)
    (sized : doms.length = (rpo g).length) (tree : ForestTable doms)
    (definedPrefix : PrefixDefined (index g node) doms) (member : node ∈ rpo g)
    (prior : ForwardParents g (index g node) doms) :
    ForwardParents g (index g node + 1) (update g doms node) := by
  intro source target sourceMember targetMember edge forward bound
  by_cases current : index g target = index g node
  · have same := index_injective g targetMember member current
    subst target
    exact update_forward_ancestor g doms node source sized tree definedPrefix member sourceMember edge forward
  · have before : index g target < index g node := by omega
    obtain ⟨parent, found, ancestry⟩ := prior source target sourceMember targetMember edge forward before
    by_cases zero : index g node = 0
    · rw [update_form, if_pos zero]
      exact ⟨parent, found, ancestry⟩
    · obtain ⟨newParent, lower, updated⟩ := update_parent g doms node tree.descending definedPrefix member zero
      rw [updated]
      refine ⟨parent, ?_, ancestry.set_above tree.descending (Nat.lt_trans forward before)⟩
      rw [List.getElem?_set_ne (Ne.symm current)]
      exact found

private theorem fold_forwardParents (g : Graph) : ∀ (nodes : List Nat) (offset : Nat)
    (doms : List (Option Nat)),
    (∀ (i : Nat) (hi : i < nodes.length), index g nodes[i] = offset + i) →
    (∀ node, node ∈ nodes → node ∈ rpo g) →
    doms.length = (rpo g).length → ForestTable doms → PrefixDefined offset doms →
    ForwardParents g offset doms →
    ForwardParents g (offset + nodes.length) (nodes.foldl (update g) doms) := by
  intro nodes
  induction nodes with
  | nil => intro offset doms positions members sized tree definedPrefix prior
           exact prior
  | cons node rest ih =>
      intro offset doms positions members sized tree definedPrefix prior
      have here : index g node = offset := by
        have first := positions 0 (by simp)
        change index g node = offset + 0 at first
        exact first.trans (Nat.add_zero offset)
      have definedAt : PrefixDefined (index g node) doms := by simpa [here] using definedPrefix
      have next := update_desc_prefix g doms node sized tree.root tree.descending
        definedAt (members node List.mem_cons_self)
      have after := ih (offset + 1) (update g doms node)
        (fun i hi => by
          have atNext := positions (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atNext)
        (fun next mem => members next (List.mem_cons_of_mem node mem))
        ((update_length g doms node).trans sized)
        (update_forest g doms node sized tree definedAt (members node List.mem_cons_self))
        (by simpa [here] using next.2)
        (by simpa [here] using (update_forwardParents g doms node sized tree definedAt
          (members node List.mem_cons_self) (by simpa [here] using prior)))
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using after

private theorem step_forwardParents (g : Graph) (doms : List (Option Nat))
    (sized : doms.length = (rpo g).length) (tree : ForestTable doms) :
    ForwardParents g (rpo g).length (step g doms) := by
  have all := fold_forwardParents g (rpo g) 0 doms
    (fun i hi => by simpa using index_rpo_at g i hi)
    (fun node mem => mem) sized tree
    (by intro slot before; exact False.elim (Nat.not_lt_zero slot before))
    (by intro source target sm tm edge forward bound; exact False.elim (Nat.not_lt_zero _ bound))
  simpa only [step, Nat.zero_add] using all

private theorem iterate_forwardParents (g : Graph) : ∀ fuel doms,
    doms.length = (rpo g).length → ForestTable doms →
    ForwardParents g (rpo g).length doms →
    ForwardParents g (rpo g).length (idoms.iterate (step g) fuel doms) := by
  intro fuel
  induction fuel with
  | zero => intro doms sized tree forward; exact forward
  | succ fuel ih =>
      intro doms sized tree forward
      rw [idoms.iterate]
      split
      · exact forward
      · exact ih (step g doms) ((step_length g doms).trans sized)
          (step_forest g doms sized tree) (step_forwardParents g doms sized tree)

private theorem idoms_forwardParents (g : Graph) : ForwardParents g (rpo g).length (idoms g) := by
  rw [idoms_exact, idoms.iterate]
  have sized := initial_length (rpo g).length
  have tree := initial_forest (rpo g).length (rpo_length_pos g)
  have forward := step_forwardParents g _ sized tree
  split
  · next same =>
      have eq := beq_iff_eq.mp same
      rw [eq] at forward
      exact forward
  · exact iterate_forwardParents g _ _ ((step_length g _).trans sized)
      (step_forest g _ sized tree) forward

private def removeOne (removed : Nat) : List Nat → List Nat
  | [] => []
  | node :: rest => if node = removed then rest else node :: removeOne removed rest

private theorem mem_removeOne_of_ne (removed node : Nat) (different : node ≠ removed) :
    ∀ items, node ∈ items → node ∈ removeOne removed items := by
  intro items
  induction items with
  | nil => intro member; exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      intro member
      rw [removeOne]
      split
      · next same =>
          rcases List.mem_cons.mp member with atHead | inRest
          · exact False.elim (different (atHead.trans same))
          · exact inRest
      · rcases List.mem_cons.mp member with atHead | inRest
        · exact List.mem_cons.mpr (Or.inl atHead)
        · exact List.mem_cons_of_mem head (ih inRest)

private theorem removeOne_length (removed : Nat) : ∀ items,
    removed ∈ items → (removeOne removed items).length + 1 = items.length := by
  intro items
  induction items with
  | nil => intro member; exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      intro member
      rw [removeOne]
      split
      · rfl
      · next different =>
          have inRest : removed ∈ rest := by
            rcases List.mem_cons.mp member with atHead | inRest
            · exact False.elim (different atHead.symm)
            · exact inRest
          have shorter := ih inRest
          simpa only [List.length_cons] using congrArg (· + 1) shorter

/- Avoid the library subset/cardinality lemmas, which depend on Classical.choice. -/
private theorem nodup_length_le_subset : ∀ (items container : List Nat),
    items.Nodup → items ⊆ container → items.length ≤ container.length := by
  intro items
  induction items with
  | nil => intro container nodup subset; exact Nat.zero_le _
  | cons head rest ih =>
      intro container nodup subset
      have shape := List.nodup_cons.mp nodup
      have headMember := subset List.mem_cons_self
      have restSubset : rest ⊆ removeOne head container := by
        intro node member
        apply mem_removeOne_of_ne head node
        · intro same
          subst node
          exact shape.1 member
        · exact subset (List.mem_cons_of_mem head member)
      have smaller := ih (removeOne head container) shape.2 restSubset
      have length := removeOne_length head container headMember
      change rest.length + 1 ≤ container.length
      omega

private theorem rpo_length_le (g : Graph) (closed : GraphClosed g) : (rpo g).length ≤ g.size + 1 := by
  have subset : rpo g ⊆ g.entry :: List.range g.size := by
    intro node member
    by_cases entry : node = g.entry
    · subst node; exact List.mem_cons_self
    · obtain ⟨source, edge, sm, forward⟩ := rpo_forward_predecessor g member entry
      exact List.mem_cons_of_mem g.entry (List.mem_range.mpr (closed source node edge))
  have bound := nodup_length_le_subset (rpo g) (g.entry :: List.range g.size) (rpo_nodup g) subset
  simpa only [List.length_cons, List.length_range] using bound

private theorem index_of_rpo_get (g : Graph) {i node : Nat} (found : (rpo g)[i]? = some node) :
    index g node = i := by
  obtain ⟨bound, located⟩ := List.getElem?_eq_some_iff.mp found
  rw [← located]
  exact index_rpo_at g i bound

private theorem ancestor_walk (g : Graph) : ∀ (fuel a b parent node : Nat),
    (rpo g)[a]? = some parent → (rpo g)[b]? = some node →
    Ancestor (idoms g) a b → b < fuel → dominates.walk g parent fuel node = true := by
  intro fuel
  induction fuel with
  | zero => intro a b parent node pa nb ancestry bound; exact False.elim (Nat.not_lt_zero _ bound)
  | succ fuel ih =>
      intro a b parent node pa nb ancestry bound
      by_cases same : node = parent
      · rw [dominates.walk, if_pos same]
      · rw [dominates.walk, if_neg same]
        have different : a ≠ b := by
          intro equal
          rw [equal, nb] at pa
          exact same (Option.some.inj pa)
        have rootNonzero : b ≠ 0 := by
          have le := ancestry.le (idoms_forest g).descending
          omega
        have notEntry : node ≠ g.entry := by
          intro atEntry
          have position := index_of_rpo_get g nb
          rw [atEntry, index_entry_zero] at position
          exact rootNonzero position.symm
        cases ancestry with
        | refl => exact False.elim (different rfl)
        | @step current up found prior =>
            have earlier : up < b := ((idoms_forest g).strict b up found).resolve_left rootNonzero
            have currentBound := (List.getElem?_eq_some_iff.mp nb).1
            have upBound : up < (rpo g).length := Nat.lt_trans earlier currentBound
            let upNode := (rpo g)[up]
            have upGet : (rpo g)[up]? = some upNode := List.getElem?_eq_some_iff.mpr ⟨upBound, rfl⟩
            have parentStep : idom g node = some upNode := by
              unfold idom
              rw [if_neg notEntry, index_of_rpo_get g nb, found]
              exact upGet
            rw [parentStep]
            exact ih a up parent upNode pa upGet prior (by omega)

private theorem computed_forward_parent (g : Graph) (closed : GraphClosed g)
    (source target : Nat) (sourceMember : source ∈ rpo g) (targetMember : target ∈ rpo g)
    (edge : target ∈ g.succs source) (forward : index g source < index g target) :
    ∃ parent, idom g target = some parent ∧ dominates g parent source = true := by
  obtain ⟨parentIndex, found, ancestry⟩ := idoms_forwardParents g source target sourceMember targetMember
    edge forward (index_lt_of_mem g targetMember)
  have parentBound := idoms_bounded g parentIndex (List.mem_of_getElem? found)
  let parent := (rpo g)[parentIndex]
  have parentGet : (rpo g)[parentIndex]? = some parent := List.getElem?_eq_some_iff.mpr ⟨parentBound, rfl⟩
  refine ⟨parent, ?_, ?_⟩
  · have notEntry : target ≠ g.entry := by
      intro same
      rw [same, index_entry_zero] at forward
      exact Nat.not_lt_zero _ forward
    unfold idom
    rw [if_neg notEntry, found]
    exact parentGet
  · unfold dominates
    exact ancestor_walk g (g.size + 1) parentIndex (index g source) parent source parentGet
      (rpo_get_index g sourceMember) ancestry
      (Nat.lt_of_lt_of_le (index_lt_of_mem g sourceMember) (rpo_length_le g closed))

/-- The actual dominator computation supplies both lexical-placement facts. -/
theorem computed_dominatorFacts (g : Graph) (closed : GraphClosed g)
    (sourceBounded : ∀ source target, target ∈ g.succs source → source < g.size)
    (reducible : Structure.reducible g = true) : Effect4.Target.Structured.DominatorFacts g := by
  refine ⟨idom_index_le g, ?_⟩
  intro source target edge forward join
  exact computed_forward_parent g closed source target
    (reachable_of_reducible reducible (sourceBounded source target edge))
    (reachable_of_reducible reducible (closed source target edge)) edge
    (forward_target_later g source target forward)

/-- Successful emission scopes every transfer allowed by the declared-edge body contract. -/
theorem emitWith_wellScoped_computed {g : Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (closed : GraphClosed g)
    (sourceBounded : ∀ source target, target ∈ g.succs source → source < g.size)
    (scopedBody : BodyScopedOnEdges g body) {out : List Skeleton}
    (emitted : Structuring.emitWith g structuredShapes body = some out) :
    Skel.wellScopedList [] [] out = true := by
  exact Effect4.Target.Structured.emitWith_wellScoped_of_dominators closed sourceBounded
    (computed_dominatorFacts g closed sourceBounded (emitWith_reducible _ _ _ emitted))
    scopedBody emitted

/-- Every successfully lowered body has its breaks and continues inside their binders. -/
theorem skeletonBody_wellScoped_computed (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId) {out : List Skeleton}
    (emitted : Flow.skeletonBody table interrupts blocks entry = some out) :
    Skel.wellScopedList [] [] out = true := by
  have emitted' := emitted
  unfold Flow.skeletonBody at emitted'
  have reducible := emitWith_reducible _ _ _ emitted'
  exact Effect4.Target.Structured.skeletonBody_wellScoped_of_dominators table interrupts blocks entry
    (computed_dominatorFacts _ (graphOf_closed blocks entry) (graphOf_sourceClosed blocks entry)
      reducible) emitted

end Effect4.Target.Structured
