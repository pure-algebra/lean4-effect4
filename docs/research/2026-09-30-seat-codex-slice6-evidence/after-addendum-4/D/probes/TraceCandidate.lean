import Slice6Probe.StepInvBank
import Effect4.Laws.Api.Supervision
import Effect4.Laws.Program.Guard.Core

/-!
UNCOMPILED C/D TRACE-AGREEMENT CANDIDATE, 2026-10-01.
No source mutations, Lean, lake, builds or generators were run by its author.

The observation is the ordered list of (parent, child, daemon) triples, using the
current Api.TraceFacts.Agrees and originForks. Source paths are not in RunEvent.forked,
so this theorem cannot establish source-site correctness. It does not establish that
a parent or daemon flag is semantically correct; it establishes agreement of the two
recordings. The allocation invariants and their runFork/runCallback facts are separate.

The candidate supplies native command preservation without a command premise, then
uses the existing Lift and Guard history lift. Primitive spawn also has a proposition
equality, but command-level forward preservation is not called Keeps.

Effect4.StepInv is a local draft bank; production placement belongs in the
named bank selected by the root. The diagnostic definitions and users move together
to Test only after their proofs pass. Update imports/names after that relocation.
-/

set_option autoImplicit false


namespace Draft.TraceAgreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Api.TraceFacts

universe u v

section Generic
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
variable {St κ φ η : Type (max u v)}

abbrev Ok (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop := Agrees m

/-- The no-fork condition is a named observation of the emitted event list. -/
def NoFork (events : List (RunEvent ν σ β ε δ ι α χ κ η)) : Prop :=
  forkedOf events = []

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem noFork_nil : NoFork ([] : List (RunEvent ν σ β ε δ ι α χ κ η)) := rfl

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem noFork_append (a b : List (RunEvent ν σ β ε δ ι α χ κ η))
    (ha : NoFork a) (hb : NoFork b) : NoFork (a ++ b) := by
  change forkedOf (a ++ b) = []
  rw [Api.forkedOf_append, ha, hb]
  rfl

/-- Frame events cannot be fork events, irrespective of frame contents. -/
@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem forkedOf_frame_map (id : FiberId) (events : List η) :
    forkedOf (events.map (RunEvent.frame (ν := ν) (σ := σ) (β := β) (ε := ε)
      (δ := δ) (ι := ι) (α := α) (χ := χ) (κ := κ) id)) = [] := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    simpa only [List.map_cons, forkedOf, List.filterMap_cons] using ih

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem noFork_frame_map (id : FiberId) (events : List η) :
    NoFork (events.map (RunEvent.frame (ν := ν) (σ := σ) (β := β) (ε := ε)
      (δ := δ) (ι := ι) (α := α) (χ := χ) (κ := κ) id)) :=
  forkedOf_frame_map id events

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_update_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : Ok (m.update f) ↔ Ok m := Iff.rfl

/-- There is deliberately no blanket emit rule: the no-fork premise is necessary. -/
@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_emit_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (events : List (RunEvent ν σ β ε δ ι α χ κ η)) (hf : NoFork events) :
    Ok (m.emit events) ↔ Ok m := by
  have trace : (m.emit events).trace = m.trace ++ events := by
    cases events with
    | nil => exact (List.append_nil _).symm
    | cons _ _ => rfl
  change forkedOf (m.emit events).trace = originForks m ↔ forkedOf m.trace = originForks m
  rw [trace, Api.forkedOf_append, hf, List.append_nil]

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

@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem ok_fibers_iff (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fibers : List (RunFiber ν σ β ε δ ι α χ κ φ)) :
    Ok { m with fibers } ↔ Ok m := Iff.rfl

/-- Unchanged observations, independent even of the machine's fiber IDs. -/
theorem update_keeps (fiber : RunFiber ν σ β ε δ ι α χ κ φ) :
    Keeps (Ok (St := St) (η := η)) (·.update fiber) := fun _ => rfl

theorem emit_keeps (events : List (RunEvent ν σ β ε δ ι α χ κ η)) (hf : NoFork events) :
    Keeps (Ok (St := St) (φ := φ)) (·.emit events) :=
  fun m => propext (ok_emit_iff m events hf)

theorem update_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : Ok (m.update f) := h

@[aesop safe apply (rule_sets := [Effect4.StepInv])]
theorem emit_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (events : List (RunEvent ν σ β ε δ ι α χ κ η)) (hf : NoFork events) : Ok (m.emit events) :=
  (ok_emit_iff m events hf).mpr h

theorem updateRace_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (race : Race ν σ β ε δ ι α κ) : Ok (m.updateRace race) := h

theorem halt_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (why : Stuck) : Ok (m.halt why) := h

theorem arm_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) : Ok (m.arm id) := h

theorem disarm_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) : Ok (m.disarm id) := h

theorem state_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (state : St) : Ok { m with state } := h

theorem middleware_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m) :
    Ok { m with middlewareInstalled := true } := h

theorem modify_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (id : FiberId) (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok (m.modify id edit) := (ok_modify_iff m id edit).mpr h

theorem mapFibers_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok { m with fibers := m.fibers.map edit } := h

theorem appendRoot_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) :
    Ok { m with fibers := m.fibers ++ [fiber], nextId := m.nextId + 1 } := h

theorem postTask_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α κ) :
    Ok (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact halt_ok h _
  · exact emit_ok (arm_ok (update_ok h _) _) _ rfl

theorem start_ok {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediate : Bool) :
    Ok (Effect4.Machine.start m parent child immediate).1 := by
  cases immediate
  · exact emit_ok (arm_ok h _) _ rfl
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

/-- Existing Api.spawn_forked only states the default site. Its trace is site-independent. -/
theorem spawn_forked_site (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    forkedOf (spawn interp m parent program options site).1.trace =
      forkedOf m.trace ++ [(parent.id, ⟨m.nextId⟩, options.daemon)] := by
  have same : (spawn interp m parent program options site).1.trace =
      (spawn interp m parent program options []).1.trace := rfl
  rw [same]
  exact Api.spawn_forked interp m parent program options

/-- Appending the same event and ledger triple preserves agreement in both directions. -/
@[aesop norm simp (rule_sets := [Effect4.StepInv])]
theorem spawn_iff (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    Ok (spawn interp m parent program options site).1 ↔ Ok m := by
  change forkedOf (spawn interp m parent program options site).1.trace =
    originForks (spawn interp m parent program options site).1 ↔ Ok m
  rw [spawn_forked_site]
  change forkedOf m.trace ++ [(parent.id, ⟨m.nextId⟩, options.daemon)] =
    (m.forks ++ [(⟨⟨m.nextId⟩, parent.id, options.daemon, site⟩ : ForkRecord)]).map
      (fun r => (r.parent, r.child, r.daemon)) ↔ Ok m
  rw [List.map_append]
  change forkedOf m.trace ++ [(parent.id, ⟨m.nextId⟩, options.daemon)] =
    originForks m ++ [(parent.id, ⟨m.nextId⟩, options.daemon)] ↔ Ok m
  constructor
  · intro h
    exact List.append_cancel_right h
  · intro h
    exact congrArg (fun xs => xs ++ [(parent.id, ⟨m.nextId⟩, options.daemon)]) h

theorem spawn_keeps (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    Keeps (Ok (η := η)) (fun m => (spawn interp m parent program options site).1) :=
  fun m => propext (spawn_iff interp m parent program options site)

theorem spawn_ok (interp : RunInterp ν σ β ε δ ι α χ St κ)
    {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Ok m)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    Ok (spawn interp m parent program options site).1 :=
  (spawn_iff interp m parent program options site).mpr h

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
    exact ih (spawn interp m host program ⟨true, true, .inherit⟩ []).1
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
  · exact update_ok (emit_ok (emit_ok h [RunEvent.interruptRecorded who target] rfl)
      [RunEvent.interruptDeferred target] rfl) _
  · exact update_ok (emit_ok h [RunEvent.interruptRecorded who target] rfl) _

/-- The four fields of the original lift note, restated exactly against the ledger. -/
structure AgreesUpdates (interp : RunInterp ν σ β ε δ ι α χ St κ) : Prop where
  drain : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, Agrees m →
    m.fiber? owner = some f →
      Agrees ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
  yield : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) id (v : Bool), Agrees m →
    Agrees (m.modify id fun f => { f with yieldOverride := some v })
  interrupt : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) who extra target t, Agrees m →
    m.fiber? target = some t → Agrees (Lift.interruptEdit interp m who extra target t)
  owed : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owed, Agrees m →
    Agrees (drainOwed m [owed]).1

/-- No reachability, unique-ID, valid-parent or freshness premise is needed by these edits. -/
theorem agrees_updates (interp : RunInterp ν σ β ε δ ι α χ St κ) :
    AgreesUpdates (φ := φ) (η := η) interp :=
  { drain := fun _ owner _ h _ => disarm_ok (update_ok h _) owner
    yield := fun _ id _ h => modify_ok h id _
    interrupt := fun _ who extra target fiber h _ => interruptEdit_ok interp h who extra target fiber
    owed := fun m owed h => drainOwed_ok m [owed] h }

/-- All eight outside-loop fields are filled; no store-hook premises remain. -/
theorem agrees_edits (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (u : AgreesUpdates (φ := φ) (η := η) interp) :
    Lift.MachineEdits interp (Ok (ν := ν) (σ := σ) (β := β) (ε := ε)
      (δ := δ) (ι := ι) (α := α) (χ := χ) (St := St) (κ := κ) (φ := φ) (η := η)) :=
  { drain := u.drain
    ran := fun _ _ _ h => emit_ok h _ rfl
    yield := u.yield
    interrupt := u.interrupt
    middleware := fun _ h => middleware_ok h
    clock := fun _ _ h _ => state_ok h _
    owed := u.owed
    prepare := fun _ _ _ _ h => state_ok h _ }

theorem edits (interp : RunInterp ν σ β ε δ ι α χ St κ) :
    Lift.MachineEdits interp (Ok (ν := ν) (σ := σ) (β := β) (ε := ε)
      (δ := δ) (ι := ι) (α := α) (χ := χ) (St := St) (κ := κ) (φ := φ) (η := η)) :=
  agrees_edits interp (agrees_updates interp)

end WithCore
end Generic

-- Closed constructor lists reduce this definition; mapped frame lists use the explicit law.
attribute [aesop norm simp (rule_sets := [Effect4.StepInv])] NoFork
attribute [aesop norm simp (rule_sets := [Effect4.StepInv])] Api.TraceFacts.forkedOf
attribute [aesop norm simp (rule_sets := [Effect4.StepInv])] List.filterMap_cons List.filterMap_nil

namespace Native
open Effect4.Program.Guard

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
  · have hm : Ok { m with nextToken := m.nextToken + 1 } := h
    apply emit_ok (modify_ok hm _ _)
    rfl

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
    · exact ih _ (emit_ok (update_ok h _) _ rfl)

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
    Ok (beginRace interp m f yielding programs site).machine := by
  unfold beginRace
  exact emit_ok h _ rfl

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
  split <;> exact emit_ok h _ (noFork_frame_map _ _)

theorem finalizerOr_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (h : Ok m) :
    Ok (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact emit_ok h _ (noFork_append _ _ (noFork_frame_map _ _) rfl)
    · exact stepFrame_ok interp m f yielding h
  · exact stepFrame_ok interp m f yielding h

theorem withFiber_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : NAction) (h : Ok m) :
    Ok (evaluatePrim.withFiber interp m f yielding action).machine := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
  case dropObservers token =>
    exact mapFibers_ok h _
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
    · exact emit_ok h _ (noFork_frame_map _ _)
    · rename_i after program _step
      cases program with
      | none => exact state_ok (emit_ok h _ (noFork_frame_map _ _)) after
      | some code => exact emit_ok (state_ok (emit_ok h _ (noFork_frame_map _ _)) after) _ rfl
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
      exact evaluateNative_ok p table (m.emit _) _ _ (emit_ok h _ rfl)
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
    (Draft.TraceAgreement.edits (interpOf p table)) fuel m decision h

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
  exact drive_ok p table fuel _ _ (appendRoot_ok h _)

theorem runCallback_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (program : NCode) (context : Ctx) (key : Nat) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (runCallback (interpOf p table) fuel m program context key).1 := by
  letI := evaluatorFor p table
  unfold runCallback
  dsimp only
  exact drive_ok p table fuel _ _ (appendRoot_ok h _)

/-- Initial load has neither fork records nor fork events. -/
theorem load_agrees (p : NativeEff) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    Agrees (Api.load p compileFuel answers) := rfl

/-- The lift note's exact history wrapper, now using the library's pure history lift. -/
theorem reachable_agrees_of (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann))
    (load : Agrees (Api.load program compileFuel answers))
    (step : ∀ m, Reachable program table compileFuel answers m → Agrees m →
      ∀ fuel decision, Agrees (steppedBy program fuel table m decision))
    (m : NativeMachine) (reachable : Reachable program table compileFuel answers m) :
    forkedOf m.trace = originForks m :=
  (reachable_lift_pure program table compileFuel answers
    (fun m => Reachable program table compileFuel answers m ∧ Agrees m)
    ⟨reachable_load program table compileFuel answers, load⟩
    (fun m fuel d h => ⟨reachable_step h.1 fuel d, step m h.1 h.2 fuel d⟩) m reachable).2

/-- Exact M1Trace.step_agrees proposition, with all native commands proved above. -/
theorem step_agrees (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (_reachable : Reachable program table compileFuel answers m)
    (agrees : Agrees m) (fuel : Nat) (decision : NativeDecision) :
    Agrees (steppedBy program fuel table m decision) :=
  steppedBy_ok program table fuel m decision agrees

/-- Exact M1Trace.reachable_agrees proposition; no command-preservation premise remains. -/
theorem reachable_agrees (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (reachable : Reachable program table compileFuel answers m) :
    forkedOf m.trace = originForks m :=
  reachable_agrees_of program table compileFuel answers (load_agrees program compileFuel answers)
    (fun m hr ha fuel decision =>
      step_agrees program table compileFuel answers m hr ha fuel decision) m reachable

end Native
end Draft.TraceAgreement

/- Append after the corresponding full candidate, in the SAME module.
This includes private theorems through their same-module source alias.
The expected ceiling is [propext, Quot.sound]; this file has NOT been run. -/

#print axioms Draft.TraceAgreement.noFork_nil
#print axioms Draft.TraceAgreement.noFork_append
#print axioms Draft.TraceAgreement.forkedOf_frame_map
#print axioms Draft.TraceAgreement.noFork_frame_map
#print axioms Draft.TraceAgreement.ok_update_iff
#print axioms Draft.TraceAgreement.ok_emit_iff
#print axioms Draft.TraceAgreement.ok_modify_iff
#print axioms Draft.TraceAgreement.ok_updateRace_iff
#print axioms Draft.TraceAgreement.ok_arm_iff
#print axioms Draft.TraceAgreement.ok_disarm_iff
#print axioms Draft.TraceAgreement.ok_halt_iff
#print axioms Draft.TraceAgreement.ok_state_iff
#print axioms Draft.TraceAgreement.ok_token_iff
#print axioms Draft.TraceAgreement.ok_state_token_iff
#print axioms Draft.TraceAgreement.ok_middleware_iff
#print axioms Draft.TraceAgreement.ok_fibers_iff
#print axioms Draft.TraceAgreement.update_keeps
#print axioms Draft.TraceAgreement.emit_keeps
#print axioms Draft.TraceAgreement.update_ok
#print axioms Draft.TraceAgreement.emit_ok
#print axioms Draft.TraceAgreement.updateRace_ok
#print axioms Draft.TraceAgreement.halt_ok
#print axioms Draft.TraceAgreement.arm_ok
#print axioms Draft.TraceAgreement.disarm_ok
#print axioms Draft.TraceAgreement.state_ok
#print axioms Draft.TraceAgreement.middleware_ok
#print axioms Draft.TraceAgreement.modify_ok
#print axioms Draft.TraceAgreement.mapFibers_ok
#print axioms Draft.TraceAgreement.appendRoot_ok
#print axioms Draft.TraceAgreement.postTask_ok
#print axioms Draft.TraceAgreement.start_ok
#print axioms Draft.TraceAgreement.drainOwed_ok
#print axioms Draft.TraceAgreement.spawn_forked_site
#print axioms Draft.TraceAgreement.spawn_iff
#print axioms Draft.TraceAgreement.spawn_keeps
#print axioms Draft.TraceAgreement.spawn_ok
#print axioms Draft.TraceAgreement.launchEntrant_ok
#print axioms Draft.TraceAgreement.forkFinalizers_ok
#print axioms Draft.TraceAgreement.settle_ok
#print axioms Draft.TraceAgreement.interruptEdit_ok
#print axioms Draft.TraceAgreement.agrees_updates
#print axioms Draft.TraceAgreement.agrees_edits
#print axioms Draft.TraceAgreement.edits
#print axioms Draft.TraceAgreement.Native.countdown_ok
#print axioms Draft.TraceAgreement.Native.countdown_result_ok
#print axioms Draft.TraceAgreement.Native.linkScope_ok
#print axioms Draft.TraceAgreement.Native.interruptEach_ok
#print axioms Draft.TraceAgreement.Native.interruptEach_result_ok
#print axioms Draft.TraceAgreement.Native.beginRace_ok
#print axioms Draft.TraceAgreement.Native.registerRace_ok
#print axioms Draft.TraceAgreement.Native.stepFrame_ok
#print axioms Draft.TraceAgreement.Native.finalizerOr_ok
#print axioms Draft.TraceAgreement.Native.withFiber_ok
#print axioms Draft.TraceAgreement.Native.evaluatePrim_ok
#print axioms Draft.TraceAgreement.Native.enterScoped_ok
#print axioms Draft.TraceAgreement.Native.exitScoped_ok
#print axioms Draft.TraceAgreement.Native.evaluateNative_ok
#print axioms Draft.TraceAgreement.Native.iteration_ok
#print axioms Draft.TraceAgreement.Native.exitFiber_ok
#print axioms Draft.TraceAgreement.Native.fireObserver_ok
#print axioms Draft.TraceAgreement.Native.driveStep_ok
#print axioms Draft.TraceAgreement.Native.steppedBy_ok
#print axioms Draft.TraceAgreement.Native.drive_ok
#print axioms Draft.TraceAgreement.Native.runFork_ok
#print axioms Draft.TraceAgreement.Native.runCallback_ok
#print axioms Draft.TraceAgreement.Native.load_agrees
#print axioms Draft.TraceAgreement.Native.reachable_agrees_of
#print axioms Draft.TraceAgreement.Native.step_agrees
#print axioms Draft.TraceAgreement.Native.reachable_agrees
