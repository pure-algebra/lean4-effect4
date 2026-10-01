import Effect4.Laws.Program.Guard.Single
import Effect4.Laws.Program.Guard.OuterDriver

/-!
Seat F probe (2026-10-01, landing item 3, M2): the repair for the six fold-level hand inductions of
`Guard/Single.lean` and `Guard/OuterDriver.lean`, proved off-tree so the coordinator can land it
with one decision.

`HeldInterruptRefuted.lean` proves `DecisionLift` cannot carry `Held`: its `interrupt` premise is
false there. But the fold lifts (`fireFold_lift`, `fireState_lift`, `flushAllState_lift`,
`advanceState_lift`, `Laws/Machine/Lift.lean`) read only eight of `DecisionLift`'s thirteen
premises. This probe states those eight as `FoldLift`, proves the four fold lifts from it (the
tree's proofs with `h : FoldLift`, named `fold_*` here to keep apart from the tree's), shows
`DecisionLift` projects to it (`ofDecisionLift`), and instantiates it for
`Held` (from the lemmas `Single.lean` already uses) and for `Preserved` (from the `DriverContract`
at fuel 1 and the lemmas `OuterDriver.lean` already uses). Each of the six statements is then
rederived and checked to be the tree's statement (`example : @x' = @x := rfl`, by proof
irrelevance once the types agree).

Red control: `HeldInterruptRefuted.interrupt_field_false` — the same `Held` instance cannot be a
`DecisionLift`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace SeatF.FoldLift

open Effect4 Effect4.Machine Effect4.Machine.Lift
open Effect4.Laws.Effects (WorldOrder)

section Generic

universe u v w

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w}

/-- The eight premises the fold lifts read: the command premise and the edits a `fire`, a
`flush` and an `advance` make outside the loop. -/
structure FoldLift (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop) :
    Prop where
  step : ∀ ts, StepKeeps o interp (Guarded J I O ts)
  nil : ∀ w m, O w m []
  drain : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, J w m →
    m.fiber? owner = some f →
    J w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      O w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
        (f.dispatcher.drain).1
  ran : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ), J w m →
    J w (m.emit [RunEvent.ranTask owner t])
  task : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ) ts, J w m → m.stuck = none →
    O w m (t :: ts) →
    I w (m.emit [RunEvent.ranTask owner t]) (taskCmds t) ∧
      O w (m.emit [RunEvent.ranTask owner t]) ts
  skip : ∀ w m (t : Machine.Task ν σ β ε δ ι α κ) ts, O w m (t :: ts) → O w m ts
  clockNone : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (none, st) →
    ∃ w', o.le w w' ∧ J w' { m with state := st }
  clockSome : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis owed st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (some owed, st) →
    ∃ w', o.le w w' ∧ J w' (drainOwed { m with state := st } [owed]).1 ∧
      ((drainOwed { m with state := st } [owed]).1.stuck = none →
        I w' (drainOwed { m with state := st } [owed]).1
          ((drainOwed { m with state := st } [owed]).2 ++ [Cmd.drainDue]))

variable {o : WorldOrder W} {interp : RunInterp ν σ β ε δ ι α χ St κ}
variable {J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
variable {O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}
variable {A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop}

/-- Every decision lift is a fold lift. -/
theorem ofDecisionLift (h : DecisionLift o interp J I O A) : FoldLift o interp J I O :=
  ⟨h.step, h.nil, h.drain, h.ran, h.task, h.skip, h.clockNone, h.clockSome⟩

theorem fold_loop (h : FoldLift o interp J I O) (ts : List (Machine.Task ν σ β ε δ ι α κ))
    (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m) (hi : m.stuck = none → I w m cmds ∧ O w m ts) :
    ∃ w', o.le w w' ∧ Guarded J I O ts w' (driveState interp fuel m cmds).1
      (driveState interp fuel m cmds).2 :=
  driveState_lift o interp (Guarded J I O ts) (h.step ts) fuel w m cmds ⟨hj, hi⟩

theorem fold_entry (h : FoldLift o interp J I O) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m)
    (hi : m.stuck = none → I w m cmds) :
    ∃ w', o.le w w' ∧ J w' (driveState interp fuel m cmds).1 := by
  obtain ⟨w', le, hj', _⟩ := fold_loop h [] fuel w m cmds hj (fun hs => ⟨hi hs, h.nil w m⟩)
  exact ⟨w', le, hj'⟩

theorem fold_fireFold (h : FoldLift o interp J I O) (fuel : Nat) (owner : FiberId) :
    ∀ (tasks : List (Machine.Task ν σ β ε δ ι α κ)) (w : W)
      (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × Bool),
      J w acc.1 → (acc.1.stuck = none → O w acc.1 tasks) →
      ∃ w', o.le w w' ∧ J w' (tasks.foldl (fireStep interp fuel owner) acc).1
  | [], w, _, hj, _ => ⟨w, o.refl w, hj⟩
  | t :: ts, w, acc, hj, ho => by
    rw [List.foldl_cons]
    by_cases hb : acc.2 = true
    · have hstep : fireStep interp fuel owner acc t =
          ((driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)).1,
            settled (driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t))) := by
        unfold fireStep
        rw [if_pos hb]
      rw [hstep]
      obtain ⟨w₁, le₁, hj₁, hi₁⟩ := fold_loop h ts fuel w (acc.1.emit [RunEvent.ranTask owner t])
        (taskCmds t) (h.ran w acc.1 owner t hj) (fun hs => h.task w acc.1 owner t ts hj hs (ho hs))
      obtain ⟨w₂, le₂, hj₂⟩ := fold_fireFold h fuel owner ts w₁
        ((driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)).1,
          settled (driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)))
        hj₁ (fun hs => (hi₁ hs).2)
      exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
    · have hstep : fireStep interp fuel owner acc t = acc := by
        unfold fireStep
        rw [if_neg hb]
      rw [hstep]
      exact fold_fireFold h fuel owner ts w acc hj (fun hs => h.skip w acc.1 t ts (ho hs))

theorem fold_fireState (h : FoldLift o interp J I O) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) (hj : J w m) :
    ∃ w', o.le w w' ∧ J w' (fireState interp fuel m owner).1 := by
  unfold fireState
  split
  · exact ⟨w, o.refl w, hj⟩
  · rename_i f hf
    obtain ⟨hj₀, ho₀⟩ := h.drain w m owner f hj hf
    exact fold_fireFold h fuel owner _ w _ hj₀ (fun _ => ho₀)

theorem fold_flushAllState (h : FoldLift o interp J I O) (fuel : Nat) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (flushAllState interp fuel rounds m).1
  | 0, w, _, hj => ⟨w, o.refl w, hj⟩
  | rounds + 1, w, m, hj => by
    simp only [flushAllState]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i owner _ _
      split
      · exact ⟨w, o.refl w, hj⟩
      · obtain ⟨w₁, le₁, hj₁⟩ := fold_fireState h fuel w m owner hj
        split
        · obtain ⟨w₂, le₂, hj₂⟩ := fold_flushAllState h fuel rounds w₁ _ hj₁
          exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
        · exact ⟨w₁, le₁, hj₁⟩

theorem fold_advanceState (h : FoldLift o interp J I O) (fuel : Nat) (millis : ClockMillis) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (advanceState interp fuel millis rounds m).1
  | 0, w, _, hj => ⟨w, o.refl w, hj⟩
  | rounds + 1, w, m, hj => by
    simp only [advanceState]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i hs
      split
      · rename_i st hc
        exact h.clockNone w m millis st hj (stuck_none_of_not hs) hc
      · rename_i owed st hc
        obtain ⟨w₁, le₁, hj₁, hi₁⟩ := h.clockSome w m millis owed st hj (stuck_none_of_not hs) hc
        obtain ⟨w₂, le₂, hj₂⟩ := fold_entry h fuel w₁ _ _ hj₁ hi₁
        split
        · obtain ⟨w₃, le₃, hj₃⟩ := fold_flushAllState h fuel fuel w₂ _ hj₂
          split
          · obtain ⟨w₄, le₄, hj₄⟩ := fold_advanceState h fuel millis rounds w₃ _ hj₃
            exact ⟨w₄, o.trans (o.trans (o.trans le₁ le₂) le₃) le₄, hj₄⟩
          · exact ⟨w₃, o.trans (o.trans le₁ le₂) le₃, hj₃⟩
        · exact ⟨w₂, o.trans le₁ le₂, hj₂⟩

/-- One command is the loop at fuel 1 on a running machine. -/
theorem driveState_one (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (c : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) (hs : m.stuck = none) :
    driveState interp 1 m (c :: rest) = driveStep interp m c rest := by
  rw [driveState_succ_cons, if_neg (not_isSome_of_none hs), driveState_zero]

end Generic

/-! ## `Held` as a fold lift -/

section HeldInstance

open Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.SingleGuard

/-- `Held` with a quiet queue and tasks that never name the guard key. -/
theorem held_foldLift (p : NativeEff) (table : RowTable) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) :
    letI := evaluatorFor p table
    FoldLift unitOrder (interpOf p table) (fun _ m => Held m fiber token request)
      (fun _ _ cmds => QuietQueue fiber token cmds)
      (fun _ _ ts => ∀ t ∈ ts, (fiber, token) ∉ taskKeys t) := by
  letI := evaluatorFor p table
  refine ⟨?step, ?nil, ?drain, ?ran, ?task, ?skip, ?clockNone, ?clockSome⟩
  case step =>
    intro ts _ m c rest _ hg
    obtain ⟨hj, hio⟩ := hg
    obtain ⟨quiet, tasks⟩ := hio (by assumption)
    have next := held_driveStep p table hj c rest (quiet c (List.mem_cons_self ..))
      (fun c' hc => quiet c' (List.mem_cons_of_mem _ hc))
    exact ⟨(), trivial, next.1, fun _ => ⟨next.2, tasks⟩⟩
  case nil => exact fun _ _ t ht => absurd ht (List.not_mem_nil)
  case drain =>
    intro _ m owner f h hf
    have memf := List.mem_of_find?_eq_some hf
    have self : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    have hp : Held (m.update { f with dispatcher := f.dispatcher.drain.2 }) fiber token request := by
      apply held_update_view h self { f with dispatcher := f.dispatcher.drain.2 } ⟨rfl, rfl, rfl⟩
      intro key hk
      have hobs : key ∈ f.observers.flatMap observerKeys := by
        simpa only [fiberKeys, bucketKeys, Dispatcher.drain, List.flatMap_nil, List.append_nil] using hk
      exact internalKeys_fiber memf (List.mem_append_left _ hobs)
    refine ⟨held_disarm hp owner, ?_⟩
    intro task ht hk
    apply h.key
    apply internalKeys_fiber memf
    apply List.mem_append_right
    obtain ⟨tasks, htasks, ht⟩ := List.mem_flatten.mp ht
    obtain ⟨bucket, hb, rfl⟩ := List.mem_map.mp htasks
    exact List.mem_flatMap.mpr ⟨bucket, hb, List.mem_flatMap.mpr ⟨task, ht, hk⟩⟩
  case ran => exact fun _ _ owner t h => held_emit h [RunEvent.ranTask owner t]
  case task =>
    intro _ _ _ t ts _ _ safe
    exact ⟨quiet_taskCmds t (safe t (List.mem_cons_self ..)),
      fun t' ht' => safe t' (List.mem_cons_of_mem _ ht')⟩
  case skip => exact fun _ _ _ _ safe t' ht' => safe t' (List.mem_cons_of_mem _ ht')
  case clockNone =>
    intro _ m millis st h _ hc
    refine ⟨(), trivial, held_withState h st ?_⟩
    have hk := clockStep_storeKeys p table m.state millis
    simpa only [hc] using hk
  case clockSome =>
    intro _ m millis owed st h _ hc
    have hs : Held { m with state := st } fiber token request := by
      apply held_withState h st
      have hk := clockStep_storeKeys p table m.state millis
      simpa only [hc] using hk
    have safe := clockStep_owed_safe p table h millis owed (by rw [hc])
    have drained := held_drainOwed hs [owed] (by
      intro d hd
      have he : d = owed := List.mem_singleton.mp hd
      exact he ▸ safe)
    refine ⟨(), trivial, drained.1, fun _ => ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact drained.2 c hc
    · have he : c = .drainDue := List.mem_singleton.mp hc
      exact he ▸ True.intro

/-- `held_fireFold`, through the fold lift. -/
theorem held_fireFold' (p : NativeEff) (table : RowTable) (fuel : Nat) (owner : FiberId)
    (tasks : List NTask) (acc : NativeMachine × Bool)
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held acc.1 fiber token request)
    (safe : ∀ task ∈ tasks, (fiber, token) ∉ taskKeys task) :
    letI := evaluatorFor p table
    Held (tasks.foldl (fireStep (interpOf p table) fuel owner) acc).1 fiber token request := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_fireFold (held_foldLift p table fiber token request) fuel owner
    tasks () acc h (fun _ => safe)
  exact held

example : @held_fireFold' = @held_fireFold := rfl

/-- `held_flushAllState`, through the fold lift. -/
theorem held_flushAllState' (p : NativeEff) (table : RowTable) (fuel rounds : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) :
    letI := evaluatorFor p table
    Held (flushAllState (interpOf p table) fuel rounds m).1 fiber token request := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_flushAllState (held_foldLift p table fiber token request) fuel
    rounds () m h
  exact held

example : @held_flushAllState' = @held_flushAllState := rfl

/-- `held_advanceState`, through the fold lift. -/
theorem held_advanceState' (p : NativeEff) (table : RowTable) (fuel : Nat) (millis : ClockMillis)
    (rounds : Nat) {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) :
    letI := evaluatorFor p table
    Held (advanceState (interpOf p table) fuel millis rounds m).1 fiber token request := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_advanceState (held_foldLift p table fiber token request) fuel
    millis rounds () m h
  exact held

example : @held_advanceState' = @held_advanceState := rfl

end HeldInstance

/-! ## `Preserved` as a fold lift -/

section PreservedInstance

open Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.OuterDriver
open Effect4.Program.Guard.RegistrationQueue

/-- `Preserved` from a start machine, with the driver's queue facts and reserved, race-free
snapshot tasks. -/
theorem preserved_foldLift (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (m₀ : NativeMachine) :
    letI := evaluatorFor p table
    FoldLift unitOrder (interpOf p table) (fun _ n => Preserved m₀ n)
      (fun _ n cmds => GuardQueue p table n cmds ∧ RegistrationQueue cmds)
      (fun _ n ts => ReservedKeys n (ts.flatMap taskKeys) ∧ ∀ t ∈ ts, taskRaceSites t = []) := by
  letI := evaluatorFor p table
  refine ⟨?step, ?nil, ?drain, ?ran, ?task, ?skip, ?clockNone, ?clockSome⟩
  case step =>
    intro ts _ m c rest hs hg
    obtain ⟨hj, hio⟩ := hg
    obtain ⟨⟨queue, registration⟩, ⟨keys, sites⟩⟩ := hio hs
    have inv := driver.invariant 1 m (c :: rest) hj.state queue registration
    have drive := Preserved.drive p table driver 1 m (c :: rest) hj.state queue registration
    have res := driver.reserved 1 m (c :: rest) _ hj.state queue registration keys
    rw [← driveState_one (interpOf p table) m c rest hs]
    exact ⟨(), trivial, hj.trans drive, fun _ => ⟨⟨inv.2.1, inv.2.2⟩, res, sites⟩⟩
  case nil =>
    exact fun _ _ => ⟨⟨fun _ hk => absurd hk List.not_mem_nil,
      fun _ _ _ _ hk => absurd hk List.not_mem_nil⟩, fun _ ht => absurd ht List.not_mem_nil⟩
  case drain =>
    intro _ m owner f hj hf
    have lookup' : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    have clear := clearDispatcher_preserved hj.state f lookup'
    have disarm := Preserved.disarm clear.state owner
    have before := clear.trans disarm
    have member := List.mem_of_find?_eq_some hf
    have keys := reservedKeys_subset (reservedKeys_fiber (f := f) hj.state member) (dispatcher_keys f)
    exact ⟨hj.trans before, before.reserved _ keys, dispatcher_sites hj.state f member⟩
  case ran => exact fun _ m owner t hj => hj.trans (Preserved.emit hj.state [RunEvent.ranTask owner t])
  case task =>
    intro _ m owner t ts hj _ hot
    have emitted := Preserved.emit hj.state [RunEvent.ranTask owner t]
    obtain ⟨keys, sites⟩ := hot
    have keysT : ReservedKeys m (taskKeys t) := reservedKeys_subset keys (List.subset_append_left ..)
    have keysTs : ReservedKeys m (ts.flatMap taskKeys) :=
      reservedKeys_subset keys (List.subset_append_right ..)
    exact ⟨⟨taskCmds_guardQueue p table _ t (emitted.reserved _ keysT) (sites t (List.mem_cons_self ..)),
        taskCmds_registration t⟩,
      emitted.reserved _ keysTs, fun t' ht' => sites t' (List.mem_cons_of_mem _ ht')⟩
  case skip =>
    intro _ _ t ts hot
    obtain ⟨keys, sites⟩ := hot
    exact ⟨reservedKeys_subset keys (List.subset_append_right ..),
      fun t' ht' => sites t' (List.mem_cons_of_mem _ ht')⟩
  case clockNone =>
    intro _ m millis st hj _ hc
    have h := clockStep_preserved p table m millis hj.state
    rw [hc] at h
    exact ⟨(), trivial, hj.trans h⟩
  case clockSome =>
    intro _ m millis owed st hj _ hc
    have facts := clockStep_owed_facts p table m millis owed (by rw [hc])
    have changed := clockStep_preserved p table m millis hj.state
    rw [hc] at changed
    have oldKeys : ReservedKeys m (taskKeys (.resume owed.waiter owed.token owed.code)) := by
      apply reservedKeys_subset (reservedKeys_internal m hj.state)
      intro key hk
      have eq := List.mem_singleton.mp hk
      exact eq ▸ facts.1
    have queue := taskCmds_guardQueue p table _ (.resume owed.waiter owed.token owed.code)
      (changed.reserved _ oldKeys) facts.2.1
    refine ⟨(), trivial, ?_, fun _ => ?_⟩
    · simpa only [drainOwed, facts.2.2] using hj.trans changed
    · simpa only [drainOwed, facts.2.2, List.append_nil, taskCmds, List.cons_append,
        List.nil_append] using
        (⟨queue, taskCmds_registration (.resume owed.waiter owed.token owed.code)⟩ :
          GuardQueue p table _ (taskCmds (.resume owed.waiter owed.token owed.code)) ∧
            RegistrationQueue (taskCmds (.resume owed.waiter owed.token owed.code)))

/-- `fireFold_preserved`, through the fold lift. -/
theorem fireFold_preserved' (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (owner : FiberId) (tasks : List NTask) (acc : NativeMachine × Bool)
    (state : GuardState acc.1) (keys : ReservedKeys acc.1 (tasks.flatMap taskKeys))
    (sites : ∀ task ∈ tasks, taskRaceSites task = []) :
    letI := evaluatorFor p table
    Preserved acc.1 (tasks.foldl (fireStep (interpOf p table) fuel owner) acc).1 := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_fireFold (preserved_foldLift p table driver acc.1) fuel owner tasks
    () acc (Preserved.refl state) (fun _ => ⟨keys, sites⟩)
  exact held

example : @fireFold_preserved' = @fireFold_preserved := rfl

/-- `flushAllState_preserved`, through the fold lift. -/
theorem flushAllState_preserved' (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    Preserved m (flushAllState (interpOf p table) fuel rounds m).1 := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_flushAllState (preserved_foldLift p table driver m) fuel rounds () m
    (Preserved.refl state)
  exact held

example : @flushAllState_preserved' = @flushAllState_preserved := rfl

/-- `advanceState_preserved`, through the fold lift. -/
theorem advanceState_preserved' (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    Preserved m (advanceState (interpOf p table) fuel millis rounds m).1 := by
  letI := evaluatorFor p table
  obtain ⟨_, _, held⟩ := fold_advanceState (preserved_foldLift p table driver m) fuel millis
    rounds () m (Preserved.refl state)
  exact held

example : @advanceState_preserved' = @advanceState_preserved := rfl

end PreservedInstance

end SeatF.FoldLift

#print axioms SeatF.FoldLift.ofDecisionLift
#print axioms SeatF.FoldLift.fold_advanceState
#print axioms SeatF.FoldLift.held_foldLift
#print axioms SeatF.FoldLift.preserved_foldLift
#print axioms SeatF.FoldLift.held_fireFold'
#print axioms SeatF.FoldLift.held_flushAllState'
#print axioms SeatF.FoldLift.held_advanceState'
#print axioms SeatF.FoldLift.fireFold_preserved'
#print axioms SeatF.FoldLift.flushAllState_preserved'
#print axioms SeatF.FoldLift.advanceState_preserved'
