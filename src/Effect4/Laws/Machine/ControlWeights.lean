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
Consumer: `ReleaseCustody.Control.registration_loop_funded`. -/
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

end Effect4.Machine.ControlWeights
