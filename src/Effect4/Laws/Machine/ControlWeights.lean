import Effect4.Laws.Machine.ControlSteps

/-!
# Weights when a command replaces one keyed record

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
Question: helper of the registration command custody clause of `Workers.Assertions.releases_step`.
Reach: one existing record, equal old/new keys, and distinct keys in the actual list.
The equality transports a natural-number projection through the machine's keyed update.
It establishes no invariant, source identity, progress or host behavior.
Unlock: active-code credits can move through actual machine updates without duplicating a fiber.
-/
set_option autoImplicit false
namespace Effect4.Machine.ControlWeights
universe u v

/-- The keyed replacement changes the weight of exactly the selected record.
Consumer: `ReleaseCustody.Control.update_credits` and source opportunity installation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem replace_sum {α : Type u} {K : Type v} [DecidableEq K]
    (key : α → K) (weight : α → Nat) (old next : α) (sameKey : key next = key old) :
    ∀ (rows : List α), (rows.map key).Nodup → old ∈ rows →
      ((rows.map fun g => if key g = key next then next else g).map weight).sum + weight old =
        (rows.map weight).sum + weight next
  | [], _, member => False.elim (List.not_mem_nil member)
  | head :: tail, unique, member => by
    have hu := List.nodup_cons.mp (show (key head :: tail.map key).Nodup from unique)
    rcases List.mem_cons.mp member with rfl | member
    · have unchanged : (tail.map fun g => if key g = key next then next else g) = tail := by
        calc
          _ = tail.map id := List.map_congr_left fun g hg => by
            have different : key g ≠ key next := by
              intro equal
              exact hu.1 (List.mem_map.mpr ⟨g, hg, equal.trans sameKey⟩)
            simp only [if_neg different, id_eq]
          _ = tail := List.map_id tail
      simp only [List.map_cons, if_pos sameKey.symm, unchanged, List.sum_cons]
      omega
    · have different : key head ≠ key next := by
        intro equal
        exact hu.1 (List.mem_map.mpr ⟨old, member, sameKey.symm.trans equal.symm⟩)
      have changed := replace_sum key weight old next sameKey tail hu.2 member
      simp only [List.map_cons, if_neg different, List.sum_cons]
      omega

/-- Removing one uniquely keyed weight partitions the original sum.
Consumer: ReleaseCustody.Control.outside_split and source opportunity accounting. -/
theorem omit_sum {α : Type u} {K : Type v} [DecidableEq K] (key : α → K) (weight : α → Nat)
    (old : α) : ∀ rows : List α, (rows.map key).Nodup → old ∈ rows →
    (rows.map (fun row => if key row = key old then 0 else weight row)).sum + weight old =
      (rows.map weight).sum
  | [], _, member => False.elim (List.not_mem_nil member)
  | head :: tail, unique, member => by
    have hu := List.nodup_cons.mp (show (key head :: tail.map key).Nodup from unique)
    rcases List.mem_cons.mp member with rfl | member
    · have unchanged : tail.map (fun row => if key row = key old then 0 else weight row) = tail.map weight := by
        apply List.map_congr_left
        intro row present
        have different : key row ≠ key old := by
          intro equal
          exact hu.1 (List.mem_map.mpr ⟨row,present,equal⟩)
        exact if_neg different
      simp only [List.map_cons, ite_true, List.sum_cons, Nat.zero_add, unchanged]
      omega
    · have different : key head ≠ key old := by
        intro equal
        exact hu.1 (List.mem_map.mpr ⟨old,member,equal.symm⟩)
      have inner := omit_sum key weight old tail hu.2 member
      simp only [List.map_cons, if_neg different, List.sum_cons]
      omega

/-- Exclude a selected key from a scalar projection over stored rows. -/
def omitted {α : Type u} {K : Type v} [DecidableEq K]
    (key : α → K) (weight : α → Nat) (owner : K) (row : α) : Nat :=
  if key row = owner then 0 else weight row

/-- Replacing the selected row leaves the omitted projection unchanged.
Consumer: ReleaseCustody.Control.outside_update and source opportunity installation. -/
theorem replace_omitted {α : Type u} {K : Type v} [DecidableEq K]
    (key : α → K) (weight : α → Nat) (owner : K) (next : α)
    (selected : key next = owner) (rows : List α) :
    ((rows.map fun row => if key row = key next then next else row).map (omitted key weight owner)).sum =
      (rows.map (omitted key weight owner)).sum := by
  have same : (rows.map fun row => if key row = key next then next else row).map (omitted key weight owner) =
      rows.map (omitted key weight owner) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro row _
    change omitted key weight owner (if key row = key next then next else row) = omitted key weight owner row
    by_cases equal : key row = key next
    · simp only [equal, if_true, omitted, selected]
    · simp only [equal, if_false]
  rw [same]

/-- A non-increasing replacement also decreases the omitted projection.
Consumer: ReleaseCustody.Control.outside_update_le and source opportunity interruption. -/
theorem replace_omitted_le {α : Type u} {K : Type v} [DecidableEq K]
    (key : α → K) (weight : α → Nat) (owner : K) (old next : α)
    (sameKey : key next = key old) (bounded : weight next ≤ weight old)
    (rows : List α) (unique : (rows.map key).Nodup) (member : old ∈ rows) :
    ((rows.map fun row => if key row = key next then next else row).map (omitted key weight owner)).sum ≤
      (rows.map (omitted key weight owner)).sum := by
  have bounded' : omitted key weight owner next ≤ omitted key weight owner old := by
    unfold omitted
    rw [sameKey]
    split
    · exact Nat.le_refl _
    · exact bounded
  have changed := replace_sum key (omitted key weight owner) old next sameKey rows unique member
  omega

/-- Installing a uniquely keyed owner spends at most its new weight.
Consumer: source opportunity settlement across every scheduler outcome. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem replace_sum_le_omitted {α : Type u} {K : Type v} [DecidableEq K]
    (key : α → K) (weight : α → Nat) (owner : K) (next : α)
    (selected : key next = owner) (rows : List α) (unique : (rows.map key).Nodup) :
    ((rows.map fun row => if key row = key next then next else row).map weight).sum ≤
      (rows.map (omitted key weight owner)).sum + weight next := by
  by_cases present : ∃ old ∈ rows, key old = owner
  · obtain ⟨old, member, same⟩ := present
    have installed := replace_sum key weight old next (selected.trans same.symm) rows unique member
    have partition := omit_sum key weight old rows unique member
    change (rows.map (omitted key weight (key old))).sum + weight old =
      (rows.map weight).sum at partition
    rw [same] at partition
    omega
  · have unchanged : (rows.map fun row => if key row = key next then next else row) = rows := by
      calc
        _ = rows.map id := List.map_congr_left fun row member => by
          have different : key row ≠ key next := by
            intro same
            exact present ⟨row, member, same.trans selected⟩
          simp only [if_neg different, id_eq]
        _ = rows := List.map_id rows
    have full : rows.map (omitted key weight owner) = rows.map weight := by
      apply List.map_congr_left
      intro row member
      have different : key row ≠ owner := by
        intro same
        exact present ⟨row, member, same⟩
      exact if_neg different
    rw [unchanged, full]
    exact Nat.le_add_right _ _


end Effect4.Machine.ControlWeights
