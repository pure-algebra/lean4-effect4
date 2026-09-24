import Effect4.Machine.Fibers

/-!
# Laws.Machine.Keeps — what a primitive machine update leaves alone

The unary `Keeps` ladder of slice 5 (M4): `Keeps proj step` says `step` does not change the
projection `proj`. The machine's primitive updates are replacing one fiber (`update`) and
appending to the trace (`emit`); each keeps every other field of `RunMachine`, and a fiber
lookup at another id is unchanged by an update. Transition proofs (M6) compose these instead of
re-reading the whole record. A projection equation licenses reuse only for a predicate that
factors through that projection; coupled fields need their joint relation (monotonicity review,
2026-09-21).
-/

set_option autoImplicit false
namespace Effect4.Machine

universe u v w₁ w₂

/-- `step` leaves the projection `proj` as it was. -/
def Keeps {S : Sort w₁} {P : Sort w₂} (proj : S → P) (step : S → S) : Prop := ∀ s, proj (step s) = proj s

theorem Keeps.comp {S : Sort w₁} {P : Sort w₂} {proj : S → P} {s t : S → S}
    (hs : Keeps proj s) (ht : Keeps proj t) : Keeps proj (t ∘ s) :=
  fun x => (ht (s x)).trans (hs x)

theorem Keeps.id {S : Sort w₁} {P : Sort w₂} (proj : S → P) : Keeps proj (fun s => s) := fun _ => rfl

namespace RunMachine
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-! ## Replacing a fiber keeps every other field -/

section update
variable (f : RunFiber ν σ β ε δ ι α χ κ φ)

theorem update_keeps_races : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.races) (·.update f) :=
  fun _ => rfl
theorem update_keeps_nextId : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextId) (·.update f) :=
  fun _ => rfl
theorem update_keeps_nextToken :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextToken) (·.update f) := fun _ => rfl
theorem update_keeps_nextRace :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextRace) (·.update f) := fun _ => rfl
theorem update_keeps_middleware :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.middlewareInstalled) (·.update f) :=
  fun _ => rfl
theorem update_keeps_armed : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.armed) (·.update f) :=
  fun _ => rfl
theorem update_keeps_state : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.state) (·.update f) :=
  fun _ => rfl
theorem update_keeps_trace : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.trace) (·.update f) :=
  fun _ => rfl
theorem update_keeps_stuck : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.stuck) (·.update f) :=
  fun _ => rfl

/-- Replacing a fiber keeps the fiber ids, in order. -/
theorem update_keeps_ids :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.fibers.map (·.id)) (·.update f) := by
  intro m
  simp only [update, List.map_map]
  congr 1
  funext g
  simp only [Function.comp_apply]
  split
  · rename_i h
    exact h.symm
  · rfl

/-- A lookup at another id is untouched by replacing a fiber. -/
theorem fiber?_update_other (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (hne : id ≠ f.id) :
    (m.update f).fiber? id = m.fiber? id := by
  simp only [fiber?, update, List.find?_map]
  have hp : ((fun g : RunFiber ν σ β ε δ ι α χ κ φ => decide (g.id = id)) ∘
      (fun g => if g.id = f.id then f else g)) = fun g => decide (g.id = id) := by
    funext g
    simp only [Function.comp_apply]
    split
    · rename_i h
      rw [h]
    · rfl
  rw [hp]
  cases hfind : m.fibers.find? (fun g => decide (g.id = id)) with
  | none => rfl
  | some g =>
    have hg := List.find?_some hfind
    have hid : g.id = id := of_decide_eq_true hg
    simp only [Option.map_some]
    congr 1
    split
    · rename_i h
      exact absurd (hid.symm.trans h) hne
    · rfl

/-- A lookup at the replaced fiber's id finds the replacement, when some fiber had that id. -/
theorem fiber?_update_self (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (present : ∃ g ∈ m.fibers, g.id = f.id) : (m.update f).fiber? f.id = some f := by
  simp only [fiber?, update, List.find?_map]
  have hp : ((fun g : RunFiber ν σ β ε δ ι α χ κ φ => decide (g.id = f.id)) ∘
      (fun g => if g.id = f.id then f else g)) = fun g => decide (g.id = f.id) := by
    funext g
    simp only [Function.comp_apply]
    split
    · rename_i h
      simp only [h]
    · rfl
  rw [hp]
  obtain ⟨g, mem, hid⟩ := present
  cases hfind : m.fibers.find? (fun g => decide (g.id = f.id)) with
  | none =>
    have := List.find?_eq_none.mp hfind g mem
    simp only [hid, decide_true, not_true_eq_false] at this
  | some g' =>
    have hg' := List.find?_some hfind
    have hid' : g'.id = f.id := of_decide_eq_true hg'
    simp only [Option.map_some, hid', ↓reduceIte]

end update

/-! ## Appending to the trace keeps every other field -/

section emit
variable (events : List (RunEvent ν σ β ε δ ι α χ κ η))

theorem emit_keeps_fibers :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.fibers) (·.emit events) := fun _ => rfl
theorem emit_keeps_races : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.races) (·.emit events) :=
  fun _ => rfl
theorem emit_keeps_nextId : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextId) (·.emit events) :=
  fun _ => rfl
theorem emit_keeps_nextToken :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextToken) (·.emit events) := fun _ => rfl
theorem emit_keeps_nextRace :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextRace) (·.emit events) := fun _ => rfl
theorem emit_keeps_middleware :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.middlewareInstalled) (·.emit events) :=
  fun _ => rfl
theorem emit_keeps_armed : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.armed) (·.emit events) :=
  fun _ => rfl
theorem emit_keeps_state : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.state) (·.emit events) :=
  fun _ => rfl
theorem emit_keeps_stuck : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.stuck) (·.emit events) :=
  fun _ => rfl

-- A lookup through `emit` is `RunMachine.fiber?_emit` (`Laws/Machine/Clauses.lean`).

end emit

end RunMachine
end Effect4.Machine
