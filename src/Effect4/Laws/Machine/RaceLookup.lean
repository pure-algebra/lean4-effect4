import Effect4.Machine.Fibers

/-!
Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Question: actual race updates retain the record selected by the existing lookup.
Consumers: observer place accounting and the existing origin-ledger proof.
These lookup facts establish no race admission, history invariant or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.RunMachine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-- The actual selected race carries the lookup key. -/
theorem id_of_race? {m : RunMachine ν σ β ε δ ι α χ St κ φ η}
    {key : Nat} {race : Race ν σ β ε δ ι α κ} (found : m.race? key = some race) :
    race.id = key :=
  of_decide_eq_true (List.find?_some (p := fun r : Race ν σ β ε δ ι α κ => decide (r.id = key)) found)

/-- Updating the selected race leaves its key selecting the actual replacement. -/
theorem race?_updateRace_same (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (race r : Race ν σ β ε δ ι α κ) (h : m.race? race.id = some race) (hid : r.id = race.id) :
    (m.updateRace r).race? race.id = some r := by
  unfold RunMachine.race? at h ⊢
  unfold RunMachine.updateRace
  rw [List.find?_map]
  have same : ((fun s : Race ν σ β ε δ ι α κ => decide (s.id = race.id)) ∘
      (fun s => if s.id = r.id then r else s)) = fun s => decide (s.id = race.id) := by
    funext s
    simp only [Function.comp]
    by_cases hs : s.id = r.id
    · simp only [hs, ↓reduceIte]
    · simp only [hs, ↓reduceIte]
  rw [same, h, Option.map_some, if_pos hid.symm]

/-- The selected-key form retains the observed id rather than choosing a new lookup. -/
theorem race?_updateRace_at (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (key : Nat) (race r : Race ν σ β ε δ ι α κ)
    (found : m.race? key = some race) (same : r.id = race.id) :
    (m.updateRace r).race? key = some r := by
  have keyed := id_of_race? found
  rw [← keyed] at found ⊢
  exact race?_updateRace_same m race r found same

/-- Replacing races changes no existing race key. -/
theorem race_ids_update (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (race : Race ν σ β ε δ ι α κ) :
    (m.updateRace race).races.map Race.id = m.races.map Race.id := by
  simp only [RunMachine.updateRace, List.map_map]
  congr 1
  funext old
  dsimp only [Function.comp_def]
  split
  · rename_i same
    exact same.symm
  · rfl

end Effect4.Machine.RunMachine
