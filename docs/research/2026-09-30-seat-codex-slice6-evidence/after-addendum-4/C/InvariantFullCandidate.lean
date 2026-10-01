import Effect4.Laws.Program.Guard.Core

/-!
UNCOMPILED DRAFT, 2026-09-30. Repository was not edited and no Lean process was run.

Assumed C representation (not defined again here):
* Effect4.Machine.ForkRecord is a closed record with child : FiberId,
  parent : FiberId, daemon : Bool, site : List Nat, in that order.
* RunMachine has forks : List ForkRecord; empty initializes it to [].
* spawn appends one record <nextId, parent.id, options.daemon, site> alongside
  its existing child-fiber append and nextId increment.
* update, emit, ordinary field updates, and root constructors retain forks.

The invariant deliberately constrains child identities, membership and allocation bounds.
It makes NO claim about the record's parent, daemon flag or source site's correctness.
Freshness is derived from bounds, rather than carried as another independently maintained fact.

The end-to-end native wrappers below take a per-command preservation premise. There is
no claim that this premise has been discharged: withFiber/evaluatePrim/native evaluator/
fireObserver/driveStep remain work for the caller. No sorry, axiom or placeholder theorem
is used to hide that boundary. Start by testing through spawn_ok, then the leaf plumbing.
-/

set_option autoImplicit false

namespace Draft.ForkLedger

open Effect4 Effect4.Machine Effect4.Program

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

section Native

open Effect4.Program.Guard

theorem load_ok (p : NativeEff) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) : Ok (Api.load p compileFuel answers) := by
  change ViewOk [Api.root] [] 1
  refine ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    List.nodup_nil, ?_, (fun _ hm => nomatch hm), (fun _ hm => nomatch hm)⟩
  intro id hm
  have hid : id = Api.root := List.mem_singleton.mp hm
  subst id
  exact Nat.zero_lt_succ 0

/-- Conditional native wrapper. The concrete command proof belongs in a later section. -/
theorem steppedBy_ok_of (p : NativeEff) (table : RowTable)
    (step : ∀ (m : NativeMachine) (c : Cmd EffName EffThunk Val Err Defect FiberId Ann)
      (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)),
      m.stuck = none → Ok m →
        letI := evaluatorFor p table
        Ok (driveStep (interpOf p table) m c rest).1)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision) (h : Ok m) :
    Ok (steppedBy p fuel table m decision) := by
  letI := evaluatorFor p table
  exact stepDecision_ok (interpOf p table) step fuel m decision h

theorem reachable_ok_of (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann))
    (step : ∀ (m : NativeMachine) (c : Cmd EffName EffThunk Val Err Defect FiberId Ann)
      (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)),
      m.stuck = none → Ok m →
        letI := evaluatorFor p table
        Ok (driveStep (interpOf p table) m c rest).1)
    (m : NativeMachine) (reachable : Reachable p table compileFuel answers m) : Ok m :=
  reachable_lift_pure p table compileFuel answers Ok (load_ok p compileFuel answers)
    (fun m fuel decision h => steppedBy_ok_of p table step fuel m decision h) m reachable

end Native
end Draft.ForkLedger

/-!
UNCOMPILED APPEND FRAGMENT, 2026-10-01.

Append after the root's corrected InvariantCandidate.lean, which defines
Draft.ForkLedger.Ok and its generic lemmas. No extra import is necessary.
This fragment supplies the concrete native command proof; no command-preservation
premise appears in the final steppedBy/reachable statements.

This is a proof draft, not checked evidence. No Lean/lake process was run by its author.
The RuleSets declaration below belongs in Laws/Auto/RuleSets.lean when integrated;
remove this local declaration if Effect4.StepInv already exists in the test environment.
-/

declare_aesop_rule_sets [Effect4.StepInv]

namespace Draft.ForkLedger

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

universe u v

section Normalization

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
variable {St κ φ η : Type (max u v)}

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_update_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : Ok (m.update f) ↔ Ok m := by
  change ViewOk ((m.update f).fibers.map (·.id)) (m.forks.map (·.child)) m.nextId ↔ Ok m
  rw [RunMachine.update_keeps_ids f m]
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

namespace Native

abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem countdown_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) (h : Ok m) :
    Ok (countdownPark interp m f targets resume failFast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact h
  · exact emit_ok (modify_ok h _ _) _

theorem countdown_result_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (after : NativeMachine) (next : NFiber) (parked : Bool) (h : Ok m)
    (step : countdownPark interp m f targets resume failFast = (after, next, parked)) :
    Ok after := by
  have kept := countdown_ok interp m f targets resume failFast h
  rw [step] at kept
  exact kept

theorem linkScope_ok (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (h : Ok m) : Ok (linkScope interp m mode scope target who extra).1 := by
  unfold linkScope
  repeat' split
  all_goals aesop (rule_sets := [Effect4.StepInv])

theorem interruptEach_ok (interp : NInterp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (targets : List FiberId) (acc : NativeMachine × List NCmd) (h : Ok acc.1) :
    Ok (interruptEach interp who extra targets acc).1 := by
  unfold interruptEach
  induction targets generalizing acc with
  | nil => exact h
  | cons target rest ih =>
    rw [List.foldl_cons]
    split
    · exact ih acc h
    · exact ih _ (emit_ok (update_ok h _) _)

theorem interruptEach_result_ok (interp : NInterp) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (acc : NativeMachine × List NCmd) (after : NativeMachine) (nested : List NCmd)
    (h : Ok acc.1) (step : interruptEach interp who extra targets acc = (after, nested)) :
    Ok after := by
  have kept := interruptEach_ok interp who extra targets acc h
  rw [step] at kept
  exact kept

theorem beginRace_ok (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (programs : List NCode) (site : Option (List Nat)) (h : Ok m) :
    Ok (beginRace interp m f yielding programs site).machine := h

theorem registerRace_ok (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (race : Nat) (h : Ok m) : Ok (registerRace m f yielding race).machine := by
  unfold registerRace
  split
  · exact h
  · exact updateRace_ok h _

theorem stepFrame_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (h : Ok m) : Ok (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact emit_ok h _

theorem finalizerOr_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (h : Ok m) :
    Ok (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact emit_ok h _
    · exact stepFrame_ok interp m f yielding h
  · exact stepFrame_ok interp m f yielding h

theorem withFiber_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : NAction) (h : Ok m) :
    Ok (evaluatePrim.withFiber interp m f yielding action).machine := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
  case dropObservers token =>
    exact mapFibers_ok h _ (fun _ => rfl)
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [spawn_ok, start_ok, countdown_ok, beginRace_ok,
        forkFinalizers_ok, linkScope_ok])
      (add safe forward [countdown_result_ok])

theorem evaluatePrim_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (h : Ok m) : Ok (Effect4.Machine.evaluatePrim interp m f yielding).machine := by
  unfold Effect4.Machine.evaluatePrim
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [withFiber_ok, registerRace_ok, countdown_ok, stepFrame_ok, finalizerOr_ok])
      (add safe forward [countdown_result_ok])

theorem enterScoped_ok (p : NativeEff) (point : Point) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    Ok (Effect4.Program.enterScoped p point m f yielding).machine := h

theorem exitScoped_ok (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (h : Ok m) :
    Ok (Effect4.Program.exitScoped p m f yielding exit).machine := by
  unfold Effect4.Program.exitScoped
  dsimp only
  split
  · split
    · exact emit_ok h _
    · rename_i after program _step
      cases program with
      | none => exact state_ok (emit_ok h _) after
      | some code => exact emit_ok (state_ok (emit_ok h _) after) _
  · exact evaluatePrim_ok _ m f yielding h

theorem evaluateNative_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    Ok (Effect4.Program.evaluateNative p m f yielding table).machine := by
  unfold Effect4.Program.evaluateNative
  split
  · split
    · exact enterScoped_ok p _ m f yielding h
    · exact evaluatePrim_ok _ m f yielding h
  · exact exitScoped_ok p m f yielding _ h
  · exact exitScoped_ok p m f yielding _ h
  · exact evaluatePrim_ok _ m f yielding h

theorem iteration_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (Effect4.Machine.iteration (interpOf p table) m f yielding).machine := by
  letI := evaluatorFor p table
  unfold Effect4.Machine.iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_ok p table m _ yielding h
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      exact evaluateNative_ok p table (m.emit _) _ _ (emit_ok h _)
    · cases hy

theorem exitFiber_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (exit : ExitV) (h : Ok m) : Ok (exitFiber interp m f exit).1 := by
  unfold exitFiber exitFiber.exitInterruptChildren exitFiber.exitStore
  repeat' split
  all_goals aesop (rule_sets := [Effect4.StepInv])

theorem fireObserver_ok (interp : NInterp) (fiber : FiberId) (exit : ExitV)
    (acc : NativeMachine × List NCmd) (observer : Observer) (h : Ok acc.1) :
    Ok (fireObserver interp fiber exit acc observer).1 := by
  cases observer <;> simp only [fireObserver]
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [interruptEach_ok])
      (add safe forward [interruptEach_result_ok])

/-- All 18 command constructors; no command is abstracted into an extra premise. -/
theorem driveStep_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (cmd : NCmd) (rest : List NCmd) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (Effect4.Machine.driveStep (interpOf p table) m cmd rest).1 := by
  letI := evaluatorFor p table
  cases cmd <;> simp only [Effect4.Machine.driveStep]
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [iteration_ok, evaluateNative_ok, fireObserver_ok,
        linkScope_ok, launchEntrant_ok, settle_ok, exitFiber_ok, drainOwed_ok])

theorem steppedBy_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (decision : NativeDecision) (h : Ok m) :
    Ok (steppedBy p fuel table m decision) := by
  letI := evaluatorFor p table
  exact Lift.machineFact_stepDecision (interpOf p table) Ok
    (fun m c rest _ hm => driveStep_ok p table m c rest hm)
    (Draft.ForkLedger.edits (interpOf p table)) fuel m decision h

theorem drive_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (cmds : List NCmd) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (drive (interpOf p table) fuel m cmds) := by
  letI := evaluatorFor p table
  exact Lift.driveState_lift_unit (interpOf p table) (fun m _ => Ok m)
    (fun m c rest _ hm => driveStep_ok p table m c rest hm) fuel m cmds h

/-- Root creation is a separate append; no fork record is fabricated for it. -/
theorem runFork_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (program : NCode) (context : Ctx) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (runFork (interpOf p table) fuel m program context).1 := by
  letI := evaluatorFor p table
  unfold runFork
  dsimp only
  exact drive_ok p table fuel _ _ (appendRoot_ok h _ rfl)

theorem runCallback_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (program : NCode) (context : Ctx) (key : Nat) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (runCallback (interpOf p table) fuel m program context key).1 := by
  letI := evaluatorFor p table
  unfold runCallback
  dsimp only
  exact drive_ok p table fuel _ _ (appendRoot_ok h _ rfl)

theorem reachable_ok (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine) (reachable : Reachable p table compileFuel answers m) : Ok m :=
  reachable_lift_pure p table compileFuel answers Ok (load_ok p compileFuel answers)
    (fun m fuel decision hm => steppedBy_ok p table fuel m decision hm) m reachable

/-- These four public consequences answer the four facts in the plan, on raw native prefixes. -/
theorem reachable_unique (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) : (m.forks.map (·.child)).Nodup :=
  (reachable_ok p table fuel answers m hr).childrenUnique

theorem reachable_bounded (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (∀ f ∈ m.fibers, f.id.value < m.nextId) ∧
    (∀ r ∈ m.forks, r.child.value < m.nextId) :=
  ⟨fiber_below (reachable_ok p table fuel answers m hr),
    record_below (reachable_ok p table fuel answers m hr)⟩

theorem reachable_corresponding (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (m.fibers.map (·.id)).Nodup ∧ (∀ r ∈ m.forks, ∃ f ∈ m.fibers, f.id = r.child) :=
  ⟨(reachable_ok p table fuel answers m hr).idsUnique,
    record_corresponds (reachable_ok p table fuel answers m hr)⟩

theorem reachable_fresh (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (⟨m.nextId⟩ : FiberId) ∉ m.fibers.map (·.id) ∧
    (⟨m.nextId⟩ : FiberId) ∉ m.forks.map (·.child) :=
  fresh (reachable_ok p table fuel answers m hr)

end Native
end Draft.ForkLedger
