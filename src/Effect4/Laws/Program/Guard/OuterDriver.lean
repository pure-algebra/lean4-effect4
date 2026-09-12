import Effect4.Laws.Program.Guard.Contract

/-! Outer scheduler induction. The command loop is supplied through the
frozen DriverContract. Dispatcher snapshots retain their removed keys as an
explicit reservation until all snapshot tasks have been considered. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard.OuterDriver
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue

structure Preserved (m n : NativeMachine) : Prop where
  state : GuardState n
  reserved : ∀ keys, ReservedKeys m keys → ReservedKeys n keys
  request : ∀ fiber token request, requestOf m fiber token = some request →
    requestOf n fiber token = some request ∨ InterruptedAt n fiber
  interrupted : ∀ fiber, InterruptedAt m fiber → InterruptedAt n fiber

theorem Preserved.refl {m : NativeMachine} (state : GuardState m) : Preserved m m :=
  ⟨state, fun _ h => h, fun _ _ _ h => Or.inl h, fun _ h => h⟩

theorem Preserved.trans {m n o : NativeMachine} (a : Preserved m n) (b : Preserved n o) :
    Preserved m o := by
  refine ⟨b.state, fun keys h => b.reserved keys (a.reserved keys h), ?_, ?_⟩
  · intro fiber token request h
    rcases a.request fiber token request h with h | h
    · exact b.request fiber token request h
    · exact Or.inr (b.interrupted fiber h)
  · exact fun fiber h => b.interrupted fiber (a.interrupted fiber h)

theorem Preserved.of_eq_requests {m n : NativeMachine} (state : GuardState n)
    (tokens : m.nextToken ≤ n.nextToken)
    (requests : ∀ fiber token, requestOf n fiber token = requestOf m fiber token)
    (interrupts : ∀ fiber, InterruptedAt m fiber → InterruptedAt n fiber) : Preserved m n :=
  ⟨state, fun _ h => reservedKeys_of_same_requests h tokens requests,
    fun fiber token _ h => Or.inl ((requests fiber token).trans h), interrupts⟩

theorem Preserved.emit {m : NativeMachine} (state : GuardState m) (events) :
    Preserved m (m.emit events) :=
  Preserved.of_eq_requests (guardState_emit state events) (Nat.le_refl _)
    (fun _ _ => rfl) (fun _ h => h)

theorem Preserved.disarm {m : NativeMachine} (state : GuardState m) (owner : FiberId) :
    Preserved m (m.disarm owner) := by
  have st : GuardState (m.disarm owner) := by
    rcases state
    constructor <;> assumption
  exact Preserved.of_eq_requests st (Nat.le_refl _) (fun _ _ => rfl) (fun _ h => h)

theorem Preserved.drive (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m commands)
    (registration : RegistrationQueue commands) :
    letI := evaluatorFor p table
    Preserved m (driveState (interpOf p table) fuel m commands).1 := by
  letI := evaluatorFor p table
  exact ⟨(driver.invariant fuel m commands state queue registration).1,
    fun keys h => driver.reserved fuel m commands keys state queue registration h,
    fun fiber token request h => driver.request fuel m commands fiber token request state queue registration h,
    fun fiber h => driver.interrupted fuel m commands fiber state queue registration h⟩

theorem taskCmds_guardQueue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (task : NTask) (reserved : ReservedKeys m (taskKeys task))
    (sites : taskRaceSites task = []) : GuardQueue p table m (taskCmds task) := by
  cases task <;> constructor
  all_goals first
    | exact fun command member => by
        simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial
    | exact List.nodup_nil
    | simpa only [taskCmds, List.flatMap_cons, List.flatMap_nil, commandKeys,
        List.nil_append, List.append_nil, taskKeys] using reserved
    | exact fun command member => by
        simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact sites
        · rfl

theorem taskCmds_registration (task : NTask) : RegistrationQueue (taskCmds task) := by
  cases task <;> exact ⟨True.intro, True.intro, True.intro⟩

theorem fireStep_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (owner : FiberId) (acc : NativeMachine × Bool) (task : NTask)
    (state : GuardState acc.1) (keys : ReservedKeys acc.1 (taskKeys task))
    (sites : taskRaceSites task = []) :
    letI := evaluatorFor p table
    Preserved acc.1 (fireStep (interpOf p table) fuel owner acc task).1 := by
  letI := evaluatorFor p table
  unfold fireStep
  split
  · have emitted := Preserved.emit state [RunEvent.ranTask owner task]
    exact emitted.trans (Preserved.drive p table driver fuel _ _ emitted.state
      (taskCmds_guardQueue p table _ task (emitted.reserved _ keys) sites)
      (taskCmds_registration task))
  · exact Preserved.refl state

theorem fireFold_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (owner : FiberId) (tasks : List NTask) (acc : NativeMachine × Bool)
    (state : GuardState acc.1) (keys : ReservedKeys acc.1 (tasks.flatMap taskKeys))
    (sites : ∀ task ∈ tasks, taskRaceSites task = []) :
    letI := evaluatorFor p table
    Preserved acc.1 (tasks.foldl (fireStep (interpOf p table) fuel owner) acc).1 := by
  letI := evaluatorFor p table
  induction tasks generalizing acc with
  | nil => exact Preserved.refl state
  | cons task tasks ih =>
    have head := fireStep_preserved p table driver fuel owner acc task state
      (reservedKeys_subset keys (List.subset_append_left ..)) (sites task (List.mem_cons_self ..))
    have tail := ih _ head.state
      (head.reserved _ (reservedKeys_subset keys (List.subset_append_right ..)))
      (fun t ht => sites t (List.mem_cons_of_mem _ ht))
    exact head.trans tail

theorem clearDispatcher_preserved {m : NativeMachine} (state : GuardState m) (f : NFiber)
    (lookup : m.fiber? f.id = some f) :
    Preserved m (m.update { f with dispatcher := f.dispatcher.drain.2 }) := by
  have member := List.mem_of_find?_eq_some lookup
  have old := guardState_fiber state member
  let g : NFiber := { f with dispatcher := f.dispatcher.drain.2 }
  have valid : FiberGuardState m g := by
    refine ⟨old.below, old.pending, old.idle, old.parkedBelow, old.exited,
      old.deferredCause, old.codes, ?_⟩
    intro bucket hb
    cases hb
  have keys : ReservedKeys m (fiberKeys g) := by
    apply reservedKeys_subset (reservedKeys_fiber (f := f) state member)
    simp only [g, fiberKeys, Dispatcher.drain, bucketKeys, List.flatMap_nil, List.append_nil]
    exact List.subset_append_left ..
  have nextState := guardState_update_preserved_request state lookup g valid ⟨rfl, rfl, rfl⟩ keys
  exact Preserved.of_eq_requests nextState (Nat.le_refl _)
    (requestOf_update_view lookup g ⟨rfl, rfl, rfl⟩)
    (fun _ h => Effect4.Program.Guard.Finish.interruptedAt_update lookup g rfl (fun h => h) h)

theorem dispatcher_keys (f : NFiber) :
    f.dispatcher.drain.1.flatMap taskKeys ⊆ fiberKeys f := by
  intro key hk
  simp only [Dispatcher.drain, List.mem_flatMap, List.mem_flatten, List.mem_map] at hk
  obtain ⟨task, ⟨tasks, ⟨bucket, hb, rfl⟩, ht⟩, hk⟩ := hk
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨bucket, hb, List.mem_flatMap.mpr ⟨task, ht, hk⟩⟩)

theorem dispatcher_sites {m : NativeMachine} (state : GuardState m) (f : NFiber)
    (member : f ∈ m.fibers) :
    ∀ task ∈ f.dispatcher.drain.1, taskRaceSites task = [] := by
  intro task ht
  simp only [Dispatcher.drain, List.mem_flatten, List.mem_map] at ht
  obtain ⟨tasks, ⟨bucket, hb, rfl⟩, ht⟩ := ht
  exact state.internalCodes.2.2.1 f member bucket hb task ht

theorem fireState_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (m : NativeMachine) (owner : FiberId) (state : GuardState m) :
    letI := evaluatorFor p table
    Preserved m (fireState (interpOf p table) fuel m owner).1 := by
  letI := evaluatorFor p table
  unfold fireState
  cases lookup : m.fiber? owner with
  | none => exact Preserved.refl state
  | some f =>
    have lookup' : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
    have clear := clearDispatcher_preserved state f lookup'
    have disarm := Preserved.disarm clear.state owner
    have before := clear.trans disarm
    have member := List.mem_of_find?_eq_some lookup
    have keys := reservedKeys_subset (reservedKeys_fiber (f := f) state member) (dispatcher_keys f)
    exact before.trans (fireFold_preserved p table driver fuel owner f.dispatcher.drain.1
      ((m.update { f with dispatcher := f.dispatcher.drain.2 }).disarm owner, true)
      before.state (before.reserved _ keys) (dispatcher_sites state f member))

theorem flushAllState_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    Preserved m (flushAllState (interpOf p table) fuel rounds m).1 := by
  letI := evaluatorFor p table
  induction rounds generalizing m with
  | zero => exact Preserved.refl state
  | succ rounds ih =>
    unfold flushAllState
    split
    · exact Preserved.refl state
    · rename_i owner rest armed
      split
      · exact Preserved.refl state
      · have fired := fireState_preserved p table driver fuel m owner state
        dsimp only
        split
        · exact fired.trans (ih _ fired.state)
        · exact fired

theorem timer_clockStep_keys {κ : Type} (timers : TimerStore) (millis : Nat) (answer : κ) :
    wakeKeys (timers.clockStep millis answer).2.wake ⊆ wakeKeys timers.wake := by
  unfold TimerStore.clockStep TimerStore.fireNext WakeList.wakeBy
  dsimp only
  cases hd : TimerStore.dueMin (timers.target.getD (timers.now + millis)) timers.wake.waiters with
  | none => exact List.Subset.refl _
  | some waiter =>
    intro key hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
      exact List.mem_append_left _ (List.mem_map.mpr ⟨w, List.mem_of_mem_erase hw, rfl⟩)
    · exact List.mem_append_right _ hk

theorem clockStep_preserved (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (millis : Nat) (state : GuardState m) :
    Preserved m { m with state := ((interpOf p table).clockStep millis m.state).2 } := by
  have keys : storeKeys ((interpOf p table).clockStep millis m.state).2 ⊆ storeKeys m.state :=
    storeKeys_mono (timer_clockStep_keys m.state.timers millis (Prim.success Val.unit))
      (List.Subset.refl _)
  have st := guardState_withState state _ keys ⟨state.internalCodes.1, state.internalCodes.2.1⟩
  exact Preserved.of_eq_requests st (Nat.le_refl _) (fun _ _ => rfl) (fun _ h => h)

theorem clockStep_owed_facts (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (millis : Nat) (owed : Owed NCode)
    (h : ((interpOf p table).clockStep millis m.state).1 = some owed) :
    (owed.waiter, owed.token) ∈ internalKeys m ∧ raceSites owed.code = [] ∧ owed.mode = .now := by
  change ((m.state.timers.clockStep millis (Prim.success Val.unit)).1.map
    (Owed.mapCode embed)) = some owed at h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  have facts := TimerStore.clockStep_owed m.state.timers millis (Prim.success Val.unit) o ho
  refine ⟨?_, ?_, facts.2⟩
  · have key := timer_clockStep_key m.state.timers millis (Prim.success Val.unit) o ho
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ key)))
  · change raceSites (embed o.code) = []
    rw [facts.1]
    rfl

theorem advanceTick_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel millis : Nat) (m : NativeMachine) (owed : Owed NCode) (state : GuardState m)
    (clock : ((interpOf p table).clockStep millis m.state).1 = some owed) :
    letI := evaluatorFor p table
    let mid : NativeMachine := { m with state := ((interpOf p table).clockStep millis m.state).2 }
    let drained := drainOwed mid [owed]
    Preserved m (driveState (interpOf p table) fuel drained.1 (drained.2 ++ [.drainDue])).1 := by
  letI := evaluatorFor p table
  have facts := clockStep_owed_facts p table m millis owed clock
  have changed := clockStep_preserved p table m millis state
  have oldKeys : ReservedKeys m (taskKeys (.resume owed.waiter owed.token owed.code)) := by
    apply reservedKeys_subset (reservedKeys_internal m state)
    intro key hk
    have eq := List.mem_singleton.mp hk
    exact eq ▸ facts.1
  have run := Preserved.drive p table driver fuel _ _ changed.state
    (taskCmds_guardQueue p table _ (.resume owed.waiter owed.token owed.code)
      (changed.reserved _ oldKeys) facts.2.1)
    (taskCmds_registration (.resume owed.waiter owed.token owed.code))
  simpa only [drainOwed, facts.2.2, List.append_nil, taskCmds,
    List.cons_append, List.nil_append] using changed.trans run

theorem advanceState_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel millis rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    Preserved m (advanceState (interpOf p table) fuel millis rounds m).1 := by
  letI := evaluatorFor p table
  induction rounds generalizing m with
  | zero => exact Preserved.refl state
  | succ rounds ih =>
    unfold advanceState
    split
    · exact Preserved.refl state
    · cases clock : (interpOf p table).clockStep millis m.state with
      | mk next stores =>
        cases next with
        | none =>
          have h := clockStep_preserved p table m millis state
          simpa only [clock] using h
        | some owed =>
          simp only
          have tick := advanceTick_preserved p table driver fuel millis m owed state
            (by rw [clock])
          simp only [clock] at tick
          split
          · have flushed := flushAllState_preserved p table driver fuel fuel _ tick.state
            split
            · exact (tick.trans flushed).trans (ih _ flushed.state)
            · exact tick.trans flushed
          · exact tick

theorem guardState_fireState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (m : NativeMachine) (owner : FiberId) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (fireState (interpOf p table) fuel m owner).1 :=
  (fireState_preserved p table driver fuel m owner state).state

theorem reservedKeys_fireState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (m : NativeMachine) (owner : FiberId) (state : GuardState m)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (fireState (interpOf p table) fuel m owner).1 keys :=
  (fireState_preserved p table driver fuel m owner state).reserved keys reserved

theorem requestOrInterrupted_fireState (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine) (owner : FiberId)
    (state : GuardState m) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (fireState (interpOf p table) fuel m owner).1 fiber token = some request ∨
      InterruptedAt (fireState (interpOf p table) fuel m owner).1 fiber :=
  (fireState_preserved p table driver fuel m owner state).request fiber token request before

theorem interruptedAt_fireState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (m : NativeMachine) (owner : FiberId) (state : GuardState m)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (fireState (interpOf p table) fuel m owner).1 fiber :=
  (fireState_preserved p table driver fuel m owner state).interrupted fiber before

theorem guardState_flushAllState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (flushAllState (interpOf p table) fuel rounds m).1 :=
  (flushAllState_preserved p table driver fuel rounds m state).state

theorem reservedKeys_flushAllState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel rounds : Nat) (m : NativeMachine) (state : GuardState m)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (flushAllState (interpOf p table) fuel rounds m).1 keys :=
  (flushAllState_preserved p table driver fuel rounds m state).reserved keys reserved

theorem requestOrInterrupted_flushAllState (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel rounds : Nat) (m : NativeMachine)
    (state : GuardState m) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (flushAllState (interpOf p table) fuel rounds m).1 fiber token = some request ∨
      InterruptedAt (flushAllState (interpOf p table) fuel rounds m).1 fiber :=
  (flushAllState_preserved p table driver fuel rounds m state).request fiber token request before

theorem interruptedAt_flushAllState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel rounds : Nat) (m : NativeMachine) (state : GuardState m)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (flushAllState (interpOf p table) fuel rounds m).1 fiber :=
  (flushAllState_preserved p table driver fuel rounds m state).interrupted fiber before

theorem guardState_advanceState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel millis rounds : Nat) (m : NativeMachine) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (advanceState (interpOf p table) fuel millis rounds m).1 :=
  (advanceState_preserved p table driver fuel millis rounds m state).state

theorem reservedKeys_advanceState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel millis rounds : Nat) (m : NativeMachine) (state : GuardState m)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (advanceState (interpOf p table) fuel millis rounds m).1 keys :=
  (advanceState_preserved p table driver fuel millis rounds m state).reserved keys reserved

theorem requestOrInterrupted_advanceState (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel millis rounds : Nat) (m : NativeMachine)
    (state : GuardState m) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (advanceState (interpOf p table) fuel millis rounds m).1 fiber token = some request ∨
      InterruptedAt (advanceState (interpOf p table) fuel millis rounds m).1 fiber :=
  (advanceState_preserved p table driver fuel millis rounds m state).request fiber token request before

theorem interruptedAt_advanceState (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel millis rounds : Nat) (m : NativeMachine) (state : GuardState m)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (advanceState (interpOf p table) fuel millis rounds m).1 fiber :=
  (advanceState_preserved p table driver fuel millis rounds m state).interrupted fiber before

end Effect4.Program.Guard.OuterDriver
