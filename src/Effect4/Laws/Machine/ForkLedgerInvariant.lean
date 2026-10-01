import Effect4.Laws.Machine.ForkLedger
import Effect4.Laws.Machine.Lift

/-! The allocation view needed by ledger lookup: distinct fiber and child IDs, both below
nextId, with each record child present. Parent, daemon and source-site correctness are separate. -/
set_option autoImplicit false

namespace Effect4.Machine.ForkLedger.Invariant

open Effect4 Effect4.Machine

universe u v

/-- Exactly the allocation observations needed by the four ledger lookup facts. -/
structure ViewOk (ids children : List FiberId) (next : Nat) : Prop where
  idsUnique : ids.Nodup
  childrenUnique : children.Nodup
  idsBelow : ∀ id ∈ ids, id.value < next
  childrenBelow : ∀ id ∈ children, id.value < next
  corresponds : children ⊆ ids

namespace ViewOk

theorem of_view {ids children ids' children' : List FiberId} {n n' : Nat}
    (h : ViewOk ids children n) (hi : ids' = ids) (hc : children' = children)
    (hn : n ≤ n') : ViewOk ids' children' n' := by
  subst ids'
  subst children'
  exact ⟨h.idsUnique, h.childrenUnique,
    fun id hm => Nat.lt_of_lt_of_le (h.idsBelow id hm) hn,
    fun id hm => Nat.lt_of_lt_of_le (h.childrenBelow id hm) hn, h.corresponds⟩

theorem fresh_ids {ids children : List FiberId} {n : Nat}
    (h : ViewOk ids children n) : (⟨n⟩ : FiberId) ∉ ids := by
  intro hm
  exact Nat.lt_irrefl n (h.idsBelow ⟨n⟩ hm)

theorem fresh_children {ids children : List FiberId} {n : Nat}
    (h : ViewOk ids children n) : (⟨n⟩ : FiberId) ∉ children := by
  intro hm
  exact Nat.lt_irrefl n (h.childrenBelow ⟨n⟩ hm)

private theorem nodup_snoc {α : Type u} {xs : List α} {x : α}
    (h : xs.Nodup) (fresh : x ∉ xs) : (xs ++ [x]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
  intro a ha b hb hab
  have hax : a = x := hab.trans (List.mem_singleton.mp hb)
  exact fresh (hax ▸ ha)

/-- A fork appends its new identity on both sides and advances the counter once. -/
theorem spawn {ids children : List FiberId} {n : Nat} (h : ViewOk ids children n) :
    ViewOk (ids ++ [⟨n⟩]) (children ++ [⟨n⟩]) (n + 1) := by
  refine ⟨nodup_snoc h.idsUnique h.fresh_ids,
    nodup_snoc h.childrenUnique h.fresh_children, ?_, ?_, ?_⟩
  · intro id hm
    rcases List.mem_append.mp hm with old | new
    · exact Nat.lt_succ_of_lt (h.idsBelow id old)
    · have hid : id = ⟨n⟩ := List.mem_singleton.mp new
      subst id
      exact Nat.lt_succ_self n
  · intro id hm
    rcases List.mem_append.mp hm with old | new
    · exact Nat.lt_succ_of_lt (h.childrenBelow id old)
    · have hid : id = ⟨n⟩ := List.mem_singleton.mp new
      subst id
      exact Nat.lt_succ_self n
  · intro id hm
    rcases List.mem_append.mp hm with old | new
    · exact List.mem_append_left _ (h.corresponds old)
    · exact List.mem_append_right _ new

/-- Root allocation appends only a fiber identity; roots have no ledger record. -/
theorem root {ids children : List FiberId} {n : Nat} (h : ViewOk ids children n) :
    ViewOk (ids ++ [⟨n⟩]) children (n + 1) := by
  refine ⟨nodup_snoc h.idsUnique h.fresh_ids, h.childrenUnique, ?_, ?_, ?_⟩
  · intro id hm
    rcases List.mem_append.mp hm with old | new
    · exact Nat.lt_succ_of_lt (h.idsBelow id old)
    · have hid : id = ⟨n⟩ := List.mem_singleton.mp new
      subst id
      exact Nat.lt_succ_self n
  · intro id hm
    exact Nat.lt_succ_of_lt (h.childrenBelow id hm)
  · intro id hm
    exact List.mem_append_left _ (h.corresponds hm)

end ViewOk

section Generic

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
variable {St κ φ η : Type (max u v)}

def Ok (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop :=
  ViewOk (m.fibers.map (·.id)) (m.forks.map (·.child)) m.nextId

theorem of_view {m m' : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (ids : m'.fibers.map (·.id) = m.fibers.map (·.id))
    (children : m'.forks.map (·.child) = m.forks.map (·.child))
    (bound : m.nextId ≤ m'.nextId) : Ok m' :=
  ViewOk.of_view h ids children bound

theorem fiber_ids_unique {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    (m.fibers.map (·.id)).Nodup := h.idsUnique

theorem record_children_unique {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    (m.forks.map (·.child)).Nodup := h.childrenUnique

theorem fiber_below {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (hf : f ∈ m.fibers) : f.id.value < m.nextId :=
  h.idsBelow f.id (List.mem_map.mpr ⟨f, hf, rfl⟩)

theorem record_below {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (record : ForkRecord) (hr : record ∈ m.forks) : record.child.value < m.nextId :=
  h.childrenBelow record.child (List.mem_map.mpr ⟨record, hr, rfl⟩)

theorem record_corresponds {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (record : ForkRecord) (hr : record ∈ m.forks) :
    ∃ f ∈ m.fibers, f.id = record.child :=
  List.mem_map.mp (h.corresponds (List.mem_map.mpr ⟨record, hr, rfl⟩))

theorem fresh {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    (⟨m.nextId⟩ : FiberId) ∉ m.fibers.map (·.id) ∧
      (⟨m.nextId⟩ : FiberId) ∉ m.forks.map (·.child) :=
  ⟨h.fresh_ids, h.fresh_children⟩

theorem fresh_fiber_lookup {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    m.fiber? ⟨m.nextId⟩ = none := by
  apply List.find?_eq_none.mpr
  intro f hf
  change ¬ decide (f.id = ⟨m.nextId⟩) = true
  intro he
  have hid := of_decide_eq_true he
  exact h.fresh_ids (List.mem_map.mpr ⟨f, hf, hid⟩)

theorem empty_ok (s : St) : Ok (RunMachine.empty s : RunMachine ν σ β ε δ ι α χ St κ φ η) :=
  ⟨List.nodup_nil, List.nodup_nil,
    (fun _ hm => nomatch hm), (fun _ hm => nomatch hm), (fun _ hm => nomatch hm)⟩

/-- Arbitrary update cannot create, remove or rename an identity: it replaces only matches. -/
theorem update_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : Ok (m.update f) :=
  of_view h (RunMachine.update_keeps_ids f m) rfl (Nat.le_refl _)

theorem emit_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (events : List (RunEvent ν σ β ε δ ι α χ κ η)) : Ok (m.emit events) := h

theorem updateRace_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (race : Race ν σ β ε δ ι α κ) : Ok (m.updateRace race) := h

theorem halt_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (why : Stuck) : Ok (m.halt why) := h

theorem arm_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) : Ok (m.arm id) := h

theorem disarm_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) : Ok (m.disarm id) := h

theorem state_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (s : St) : Ok { m with state := s } := h

theorem middleware_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    Ok { m with middlewareInstalled := true } := h

theorem modify_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact h
  · exact update_ok h _

theorem mapFibers_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ)
    (ids : ∀ f, (edit f).id = f.id) : Ok { m with fibers := m.fibers.map edit } := by
  apply of_view (m' := { m with fibers := m.fibers.map edit }) h ?_ rfl (Nat.le_refl _)
  simp only [List.map_map]
  congr 1
  funext f
  exact ids f

theorem postTask_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α κ) :
    Ok (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact halt_ok h _
  · exact emit_ok (arm_ok (update_ok h _) _) _

theorem start_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediate : Bool) :
    Ok (Effect4.Machine.start m parent child immediate).1 := by
  cases immediate
  · exact emit_ok (arm_ok h _) _
  · exact h

theorem drainOwed_ok (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (owed : List (Owed κ)) (h : Ok m) : Ok (drainOwed m owed).1 := by
  induction owed generalizing m with
  | nil => exact h
  | cons entry rest ih =>
    cases hm : entry.mode with
    | now => simpa only [drainOwed, hm] using ih m h
    | scheduled owner priority =>
      simpa only [drainOwed, hm] using
        ih (m.postTask owner priority (.resume entry.waiter entry.token entry.code))
          (postTask_ok h _ _ _)

section WithCore

variable [core : FiberCore ν β ε δ ι α κ φ]

/-- This is the only proof below that depends on the exact new spawn record construction. -/
theorem spawn_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    Ok (Effect4.Machine.spawn interp m parent program options site).1 := by
  -- Unfold only the allocation and projections. This works both beside the old origin
  -- field and after its deletion; the child's origin never enters the view.
  simpa only [Ok, Effect4.Machine.spawn, RunMachine.emit,
    List.map_append, List.map_cons, List.map_nil, RunFiber.make] using
    ViewOk.spawn h

theorem launchEntrant_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) (raceId : Nat)
    (host : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ) (site : List Nat) :
    Ok (launchEntrant interp raceId m host program site).1 :=
  spawn_ok interp h host program ⟨true, true, .interruptible⟩ site

theorem forkFinalizers_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (host : RunFiber ν σ β ε δ ι α χ κ φ) (programs : List κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (h : Ok m) :
    Ok (forkFinalizers interp m host programs).1 := by
  induction programs generalizing m with
  | nil => exact h
  | cons program rest ih =>
    exact ih (Effect4.Machine.spawn interp m host program ⟨true, true, .inherit⟩ []).1
      (spawn_ok interp h host program ⟨true, true, .inherit⟩ [])

theorem settle_ok (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η) (h : Ok it.machine) :
    Ok (settle id rest it).1 := by
  unfold settle
  split
  · exact update_ok h _
  · exact update_ok h _
  · split <;> exact update_ok h _
  · exact update_ok h _
  · exact update_ok h _
  · exact halt_ok (update_ok h _) _

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

theorem interruptEdit_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (who : Option FiberId) (extra : ReasonAnnotations α) (target : FiberId)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok (Lift.interruptEdit interp m who extra target fiber) := by
  unfold Lift.interruptEdit
  dsimp only
  split
  · exact update_ok (emit_ok (emit_ok h _) _) _
  · exact update_ok (emit_ok h _) _

variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

omit [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
/-- All outer decision edits preserve this invariant, independently of native store hooks. -/
theorem edits (interp : RunInterp ν σ β ε δ ι α χ St κ) :
    Lift.MachineEdits interp (Ok (ν := ν) (σ := σ) (β := β) (ε := ε)
      (δ := δ) (ι := ι) (α := α) (χ := χ) (St := St) (κ := κ) (φ := φ) (η := η)) :=
  { drain := fun _ owner _ h _ => disarm_ok (update_ok h _) owner
    ran := fun _ _ _ h => emit_ok h _
    yield := fun _ id _ h => modify_ok h id _
    interrupt := fun _ who extra target fiber h _ => interruptEdit_ok interp h who extra target fiber
    middleware := fun _ h => middleware_ok h
    clock := fun _ _ h _ => state_ok h _
    owed := fun m owed h => drainOwed_ok m [owed] h
    prepare := fun _ _ _ _ h => state_ok h _ }

/-- The remaining input is exposed here: command preservation has NOT been discharged. -/
theorem stepDecision_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (step : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) c rest,
      m.stuck = none → Ok m → Ok (driveStep interp m c rest).1)
    (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (decision : RunDecision ν σ β ε δ ι α) (h : Ok m) :
    Ok (stepDecisionState interp fuel m decision).1 :=
  Lift.machineFact_stepDecision interp Ok step (edits interp) fuel m decision h

end WithCore
end Generic
section Normalization

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
variable {St κ φ η : Type (max u v)}

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_update_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : Ok (m.update f) ↔ Ok m := by
  change ViewOk ((m.update f).fibers.map (·.id)) (m.forks.map (·.child)) m.nextId ↔ Ok m
  have ids : (m.update f).fibers.map (·.id) = m.fibers.map (·.id) :=
    RunMachine.update_keeps_ids f m
  rw [ids]
  rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_emit_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (events : List (RunEvent ν σ β ε δ ι α χ κ η)) : Ok (m.emit events) ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_modify_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok (m.modify id edit) ↔ Ok m := by
  unfold RunMachine.modify
  split
  · rfl
  · exact ok_update_iff _ _

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_updateRace_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (race : Race ν σ β ε δ ι α κ) : Ok (m.updateRace race) ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_arm_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) :
    Ok (m.arm id) ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_disarm_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) :
    Ok (m.disarm id) ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_halt_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (why : Stuck) :
    Ok (m.halt why) ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_state_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (state : St) :
    Ok { m with state } ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_token_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (token : Nat) :
    Ok { m with nextToken := token } ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_state_token_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (state : St) (token : Nat) : Ok { m with state, nextToken := token } ↔ Ok m := Iff.rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_middleware_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    Ok { m with middlewareInstalled := true } ↔ Ok m := Iff.rfl

theorem appendRoot_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (id : fiber.id = ⟨m.nextId⟩) :
    Ok { m with fibers := m.fibers ++ [fiber], nextId := m.nextId + 1 } := by
  change ViewOk ((m.fibers ++ [fiber]).map (·.id)) (m.forks.map (·.child)) (m.nextId + 1)
  simpa only [List.map_append, List.map_cons, List.map_nil, id] using ViewOk.root h

-- No of_view, generic transitivity, or reverse spawn rule enters this bank.
-- These simp equations have every right-hand variable on the left-hand side.

end Normalization

end Effect4.Machine.ForkLedger.Invariant
