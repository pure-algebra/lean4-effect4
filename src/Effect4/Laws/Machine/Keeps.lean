import Effect4.Laws.Machine.Edit

/-!
# Laws.Machine.Keeps — what a primitive machine update leaves alone

The unary `Keeps` ladder of slice 5 (M4): `Keeps proj step` says `step` does not change the
projection `proj`. The primitive edits declare their written field in `Edit.writes`.
The update and emit field rows consume the single `Edit.frame` law.
A fiber lookup at another id is unchanged by an update. Transition proofs (M6) compose these
instead of re-reading the whole record. A projection equation licenses reuse only for a predicate that
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

/-- A left-to-right word keeps a projection when each step keeps it.
The machine edit word consumes this frame rule. -/
theorem Keeps.foldl {S : Type w₁} {P : Sort w₂} {A : Type u}
    (proj : S → P) (step : A → S → S) (word : List A)
    (kept : ∀ entry ∈ word, Keeps proj (step entry)) :
    Keeps proj (fun s => word.foldl (fun held entry => step entry held) s) := by
  intro s
  induction word generalizing s with
  | nil => rfl
  | cons entry rest ih =>
    exact (ih (fun next member => kept next (List.mem_cons_of_mem entry member)) _).trans
      (kept entry List.mem_cons_self s)

namespace RunMachine
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-! ## Replacing a fiber keeps every other field -/

section update
variable (f : RunFiber ν σ β ε δ ι α χ κ φ)

theorem update_keeps_races : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.races) (·.update f) :=
  fun m => Edit.frame (.update f) .races m (by intro impossible; cases impossible)
theorem update_keeps_nextId : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextId) (·.update f) :=
  fun m => Edit.frame (.update f) .nextId m (by intro impossible; cases impossible)
theorem update_keeps_nextToken :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextToken) (·.update f) :=
  fun m => Edit.frame (.update f) .nextToken m (by intro impossible; cases impossible)
theorem update_keeps_nextRace :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextRace) (·.update f) :=
  fun m => Edit.frame (.update f) .nextRace m (by intro impossible; cases impossible)
theorem update_keeps_middleware :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.middlewareInstalled) (·.update f) :=
  fun m => Edit.frame (.update f) .middlewareInstalled m (by intro impossible; cases impossible)
theorem update_keeps_armed : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.armed) (·.update f) :=
  fun m => Edit.frame (.update f) .armed m (by intro impossible; cases impossible)
theorem update_keeps_state : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.state) (·.update f) :=
  fun m => Edit.frame (.update f) .state m (by intro impossible; cases impossible)
theorem update_keeps_trace : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.trace) (·.update f) :=
  fun m => Edit.frame (.update f) .trace m (by intro impossible; cases impossible)
theorem update_keeps_stuck : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.stuck) (·.update f) :=
  fun m => Edit.frame (.update f) .stuck m (by intro impossible; cases impossible)

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
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.fibers) (·.emit events) :=
  fun m => Edit.frame (.emit events) .fibers m (by intro impossible; cases impossible)
theorem emit_keeps_races : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.races) (·.emit events) :=
  fun m => Edit.frame (.emit events) .races m (by intro impossible; cases impossible)
theorem emit_keeps_nextId : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextId) (·.emit events) :=
  fun m => Edit.frame (.emit events) .nextId m (by intro impossible; cases impossible)
theorem emit_keeps_nextToken :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextToken) (·.emit events) :=
  fun m => Edit.frame (.emit events) .nextToken m (by intro impossible; cases impossible)
theorem emit_keeps_nextRace :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.nextRace) (·.emit events) :=
  fun m => Edit.frame (.emit events) .nextRace m (by intro impossible; cases impossible)
theorem emit_keeps_middleware :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.middlewareInstalled) (·.emit events) :=
  fun m => Edit.frame (.emit events) .middlewareInstalled m (by intro impossible; cases impossible)
theorem emit_keeps_armed : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.armed) (·.emit events) :=
  fun m => Edit.frame (.emit events) .armed m (by intro impossible; cases impossible)
theorem emit_keeps_state : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.state) (·.emit events) :=
  fun m => Edit.frame (.emit events) .state m (by intro impossible; cases impossible)
theorem emit_keeps_stuck : Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.stuck) (·.emit events) :=
  fun m => Edit.frame (.emit events) .stuck m (by intro impossible; cases impossible)

-- A lookup through `emit` is `RunMachine.fiber?_emit` (`Laws/Machine/Clauses.lean`).

end emit

section fiberEdits
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [FiberCore ν β ε δ ι α κ φ]

/-- Message interpretation changes only the fiber table and requests only evaluation commands.
Concept: reactive-scheduling, R11, serving command-moves and source-location preservation.
Consumers: guard reservation and native source ownership after settlement.
This states no validity or cause provenance of the edited records. -/
theorem applyFiberEdit_shape (edit : FiberEdit ε δ ι α)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (applyFiberEdit edit m).1 = {m with fibers := (applyFiberEdit edit m).1.fibers} ∧
    ∀ command ∈ (applyFiberEdit edit m).2, ∃ target, command = Cmd.evaluate target := by
  cases edit with
  | observe target observer =>
    simp only [applyFiberEdit, modify]
    split
    all_goals exact ⟨rfl, by intro command member; cases member⟩
  | dropToken token => exact ⟨rfl, by intro command member; cases member⟩
  | interrupt target cause =>
    simp only [applyFiberEdit]
    split
    · exact ⟨rfl, by intro command member; cases member⟩
    · refine ⟨rfl, ?_⟩
      split
      · intro command member
        exact ⟨target, List.mem_singleton.mp member⟩
      · intro command member
        cases member

/-- The whole word has the same footprint, with command order retained by the actual fold. -/
theorem applyFiberEdits_shape (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (applyFiberEdits edits m).1 = {m with fibers := (applyFiberEdits edits m).1.fibers} ∧
    ∀ command ∈ (applyFiberEdits edits m).2, ∃ target, command = Cmd.evaluate target := by
  unfold applyFiberEdits
  suffices ∀ acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ),
      (∀ command ∈ acc.2, ∃ target, command = Cmd.evaluate target) →
      let next := edits.foldl (fun held edit =>
        let changed := applyFiberEdit edit held.1
        (changed.1, held.2 ++ changed.2)) acc
      next.1 = {acc.1 with fibers := next.1.fibers} ∧
        ∀ command ∈ next.2, ∃ target, command = Cmd.evaluate target from
    this (m, []) (by intro command member; cases member)
  intro acc commands
  induction edits generalizing acc with
  | nil => exact ⟨rfl, commands⟩
  | cons edit rest ih =>
    have shape := applyFiberEdit_shape edit acc.1
    have appended : ∀ command ∈ acc.2 ++ (applyFiberEdit edit acc.1).2,
        ∃ target, command = Cmd.evaluate target := by
      intro command member
      rcases List.mem_append.mp member with old | new
      · exact commands command old
      · exact shape.2 command new
    have next := ih ((applyFiberEdit edit acc.1).1,
      acc.2 ++ (applyFiberEdit edit acc.1).2) appended
    have replace (fibers : List (RunFiber ν σ β ε δ ι α χ κ φ)) :
        {(applyFiberEdit edit acc.1).1 with fibers} = {acc.1 with fibers} :=
      congrArg (fun held : RunMachine ν σ β ε δ ι α χ St κ φ η => {held with fibers}) shape.1
    exact ⟨next.1.trans (replace _), next.2⟩

theorem applyFiberEdit_state (edit : FiberEdit ε δ ι α)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : (applyFiberEdit edit m).1.state = m.state := by
  have same := congrArg (fun held : RunMachine ν σ β ε δ ι α χ St κ φ η => held.state)
    (applyFiberEdit_shape edit m).1
  exact same

theorem applyFiberEdits_state (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : (applyFiberEdits edits m).1.state = m.state := by
  have same := congrArg (fun held : RunMachine ν σ β ε δ ι α χ St κ φ η => held.state)
    (applyFiberEdits_shape edits m).1
  exact same

end fiberEdits

end RunMachine
end Effect4.Machine
