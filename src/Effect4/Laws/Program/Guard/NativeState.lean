import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.FrameOwned
import Effect4.Laws.Program.Guard.Messages

/-! Native evaluation preserves the stored machine invariant.
Returned-fiber installation is handled by Settle and NativeAssembly.
The executing fiber need only name an existing stored fiber: local iteration changes
its frame and counter before evaluation. Its existing code-safety premises belong
to the separately proved returned-frame component.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Effect4.Program.Guard.NativeState
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard

structure StateStep (before after : NativeMachine) : Prop where
  state : GuardState after
  tokens : before.nextToken ≤ after.nextToken
  requests : ∀ fiber token request, requestOf after fiber token = some request →
    requestOf before fiber token = some request
  races : RaceHostsPreserved before after

/-- The existing native-state census also records the emitted observer admission.
Raw withFiber calls retain their source-head premise; actual native evaluation discharges it. -/
structure NativeStep (before : NativeMachine)
    (next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (permit : Prop := True) : Prop where
  state : StateStep before next.machine
  messages : permit → Messages.MessageKeys before next

theorem NativeStep.empty {before : NativeMachine}
    {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores} {permit : Prop}
    (state : StateStep before next.machine) (edits : next.edits = []) :
    NativeStep before next permit := by
  refine ⟨state, ?_⟩
  intro _ target observer observed
  rw [edits] at observed
  exact False.elim (List.not_mem_nil observed)

theorem NativeStep.admit {before : NativeMachine}
    {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores} {permit : Prop}
    (step : NativeStep before next permit) (permission : permit) : NativeStep before next :=
  ⟨step.state, fun _ => step.messages permission⟩

theorem park_internal (p : NativeEff) (table : RowTable) (completed) (code : NCode)
    (kind : ParkKind) (park : (interpAt p completed table).parkOf code = some (.ok kind)) :
    externalRequest code = none := by
  cases code <;> aesop (add simp [externalRequest, interpAt, interpOf])

theorem NativeStep.keyless {before : NativeMachine}
    {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores} {permit : Prop}
    (state : StateStep before next.machine)
    (keys : ∀ target observer, FiberEdit.observe target observer ∈ next.edits → observerKeys observer = []) :
    NativeStep before next permit :=
  ⟨state, fun _ target observer observed => Or.inl (keys target observer observed)⟩

theorem NativeStep.raw {before after : NativeMachine} {f : NFiber}
    {yielding : Bool} {outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann}
    {nested : List NCmd} {permit : Prop} (state : StateStep before after) :
    NativeStep before ⟨after, f, yielding, outcome, nested, []⟩ permit :=
  NativeStep.empty state rfl

theorem races_same {m n : NativeMachine} (same : n.races = m.races) : RaceHostsPreserved m n :=
  fun _ race found => ⟨race, by simpa only [RunMachine.race?, same] using found, rfl⟩

theorem StateStep.refl {m : NativeMachine} (state : GuardState m) : StateStep m m :=
  ⟨state, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩

theorem StateStep.trans {m n o : NativeMachine} (a : StateStep m n) (b : StateStep n o) :
    StateStep m o :=
  ⟨b.state, Nat.le_trans a.tokens b.tokens,
    fun fiber token request h => a.requests fiber token request (b.requests fiber token request h),
    fun id race found => by
      obtain ⟨middle, seen, host⟩ := a.races id race found
      obtain ⟨last, final, same⟩ := b.races id middle seen
      exact ⟨last, final, same.trans host⟩⟩

theorem StateStep.reserved {m n : NativeMachine} (h : StateStep m n)
    {keys : List GuardKey} (keysBefore : ReservedKeys m keys) : ReservedKeys n keys :=
  reservedKeys_of_requests_subset keysBefore h.tokens h.requests

theorem StateStep.emit {m n : NativeMachine} (h : StateStep m n) (events) :
    StateStep m (n.emit events) := ⟨guardState_emit h.state events, h.tokens, h.requests, h.races⟩

theorem StateStep.arm {m n : NativeMachine} (h : StateStep m n) (owner : FiberId) :
    StateStep m (n.arm owner) := ⟨guardState_arm h.state owner, h.tokens, h.requests, h.races⟩

theorem StateStep.middleware {m : NativeMachine} (state : GuardState m) (flag : Bool) :
    StateStep m {m with middlewareInstalled := flag} := by
  refine ⟨?_, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩
  rcases state with ⟨a,b,c,d,e,f,g,h,i,j,k,l,n,o,q⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,n,o,q⟩

theorem StateStep.grow {m : NativeMachine} (state : GuardState m) :
    StateStep m {m with nextToken := m.nextToken + 1} :=
  ⟨guardState_increaseTokens state _ (Nat.le_succ _), Nat.le_succ _, fun _ _ _ h => h, races_same rfl⟩

theorem StateStep.store {m : NativeMachine} (state : GuardState m) (stores : Stores)
    (keys : storeKeys stores ⊆ storeKeys m.state) :
    StateStep m {m with state := stores} :=
  ⟨guardState_withState state stores keys, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩

theorem StateStep.storeFresh {m : NativeMachine} (state : GuardState m)
    (stores : Stores) (fiber : FiberId)
    (keys : storeKeys stores ⊆ storeKeys m.state ++ [(fiber, m.nextToken)]) :
    StateStep m {m with state := stores, nextToken := m.nextToken + 1} :=
  ⟨guardState_storeFresh state stores fiber keys, Nat.le_succ _, fun _ _ _ h => h, races_same rfl⟩

theorem StateStep.observer {m : NativeMachine} (state : GuardState m)
    (target : FiberId) (observer : Observer) (keys : ReservedKeys m (observerKeys observer)) :
    StateStep m (m.modify target fun f => {f with observers := f.observers ++ [observer]}) := by
  refine ⟨guardState_addObserver state target observer keys, ?_, ?_,
    races_same (Effect4.Program.Guard.FrameOwned.modify_races m target _)⟩
  · unfold RunMachine.modify
    split <;> exact Nat.le_refl _
  · intro fiber token request h
    rwa [requestOf_addObserver] at h

theorem StateStep.registerRace {m : NativeMachine} (state : GuardState m)
    (f : NFiber) (yielding : Bool) (id : Nat) :
    StateStep m (registerRace m f yielding id).machine := by
  unfold Effect4.Machine.registerRace
  split
  · exact .refl state
  · rename_i race hr
    refine ⟨guardState_updateRace (race := race) state ?_ {race with registering := true}
      rfl rfl rfl (state.internalCodes.2 race (List.mem_of_find?_eq_some hr)),
      Nat.le_refl _, fun _ _ _ h => h,
      raceHostsPreserved_updateRace (race := race)
        (by simpa only [race_id_of_lookup hr] using hr) _ rfl rfl⟩
    simpa only [race_id_of_lookup hr] using hr

theorem guardState_appendRace {m : NativeMachine} (state : GuardState m)
    (race : NRace) (id : race.id = m.nextRace) (token : race.token = m.nextToken)
    (host : ∃ saved, m.fiber? race.host = some saved)
    (programs : ∀ code ∈ race.programs, raceSites code = []) :
    GuardState {m with races := m.races ++ [race], nextRace := m.nextRace + 1, nextToken := m.nextToken + 1} := by
  have hall (P : NRace → Prop) (old : ∀ r ∈ m.races, P r) (new : P race) :
      ∀ r ∈ m.races ++ [race], P r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact old r hr
    · exact (List.mem_singleton.mp hr) ▸ new
  have keys : internalKeys {m with races := m.races ++ [race], nextRace := m.nextRace + 1, nextToken := m.nextToken + 1} ⊆
      internalKeys m ++ [(race.host, race.token)] := by
    intro key hk
    simp only [internalKeys, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    rcases hk with (((ha | hb) | hc) | (hd | he)) | hf
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ha))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hb))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
    · exact Or.inl (Or.inl (Or.inr hd))
    · exact Or.inr he
    · exact Or.inl (Or.inr hf)
  constructor
  · exact state.fiberIds
  · exact state.fibersBelow
  · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨state.raceIds, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro value hv other ho he
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hv
    have bound := state.racesBelow r hr
    have : r.id = m.nextRace := heq.trans (he.trans (List.mem_singleton.mp ho)) |>.trans id
    omega
  · exact hall _ (fun r hr => Nat.lt_trans (state.racesBelow r hr) (Nat.lt_succ_self _))
      (by simp only [id]; exact Nat.lt_succ_self _)
  · exact hall _ state.raceHosts host
  · intro key hk
    rcases List.mem_append.mp (keys hk) with hk | hk
    · exact Nat.lt_trans (state.keysBelow key hk) (Nat.lt_succ_self _)
    · rw [List.mem_singleton.mp hk, token]; exact Nat.lt_succ_self _
  · exact fun f t r h => Nat.lt_trans (state.requestsBelow f t r h) (Nat.lt_succ_self _)
  · intro f t r h hk
    rcases List.mem_append.mp (keys hk) with hk | hk
    · exact state.requestsOwned f t r h hk
    · have ht := congrArg Prod.snd (List.mem_singleton.mp hk)
      have bound := state.requestsBelow f t r h
      simp only [token] at ht
      omega
  · exact state.pendingShape
  · exact state.parkedIdle
  · exact fun f hf t hp => Nat.lt_trans (state.parkedBelow f hf t hp) (Nat.lt_succ_self _)
  · exact state.exited
  · exact state.deferredCause
  · exact fun f hf => frameCodeOwned_transport (raceHostsPreserved_append m [race])
      (state.frameCodes f hf)
  · exact ⟨state.internalCodes.1, hall _ state.internalCodes.2 programs⟩

theorem StateStep.beginRace (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (entrants : List NCode) (host : ∃ saved, m.fiber? f.id = some saved)
    (programs : ∀ code ∈ entrants, raceSites code = []) (site : Option (List Nat) := none)
    (mode : Supervision.RaceMode := .firstSuccess) :
    StateStep m (beginRace (interpAt p completed table) m f yielding entrants site mode).machine := by
  apply StateStep.emit
  exact ⟨guardState_appendRace state _ rfl rfl host programs, Nat.le_succ _, fun _ _ _ h => h,
    raceHostsPreserved_append m [_]⟩

theorem StateStep.countdownEdits (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resumeWith : Resume EffName) (failFast : Bool) :
    StateStep m (countdownParkEdits (interpAt p completed table) m f targets resumeWith failFast).1 := by
  rw [Edits.countdown_word]
  unfold Edits.countdownWord
  cases found : countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
  | mk exits target =>
    cases target with
    | none => exact .grow state
    | some pair => exact (StateStep.grow state).emit _

theorem StateStep.countdown (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resumeWith : Resume EffName) (failFast : Bool) :
    StateStep m (countdownPark (interpAt p completed table) m f targets resumeWith failFast).1 := by
  unfold countdownPark countdownParkEdits
  dsimp only
  split
  · exact .grow state
  · dsimp only [applyFiberEdits, List.foldl, applyFiberEdit]
    rw [RunMachine.modify_emit]
    exact ((StateStep.grow state).trans
      (.observer (guardState_increaseTokens state _ (Nat.le_succ _)) _ (.countdown f.id m.nextToken)
        (reservedKeys_fresh state f.id))).emit _

theorem storeKeys_registerDeferred (stores : Stores) (cell : DeferredKey)
    (fiber : FiberId) (token : Nat) :
    storeKeys {stores with deferreds := (stores.deferreds.register cell fiber token).1} ⊆
      storeKeys stores ++ [(fiber, token)] := by
  intro key hk
  rcases List.mem_append.mp hk with hk | hk
  · exact List.mem_append_left _ (List.mem_append_left _ hk)
  · rcases List.mem_append.mp
      (deferredKeys_register_subset stores.deferreds cell fiber token hk) with hk | hk
    · exact List.mem_append_left _ (List.mem_append_right _ hk)
    · exact List.mem_append_right _ hk

theorem storeKeys_sleep (stores : Stores) (fiber : FiberId) (token : Nat)
    (millis : ClockMillis) :
    storeKeys {stores with timers := stores.timers.sleep fiber token millis} ⊆
      storeKeys stores ++ [(fiber, token)] := by
  intro key hk
  change key ∈ wakeKeys (stores.timers.sleep fiber token millis).wake ++
    deferredKeys stores.deferreds at hk
  rcases List.mem_append.mp hk with hk | hk
  · rcases (wakeKeys_register_mem _ _ _ _ _).mp hk with hk | hk
    · exact List.mem_append_left _ (List.mem_append_left _ hk)
    · exact List.mem_append_right _ (List.mem_singleton.mpr hk)
  · exact List.mem_append_left _ (List.mem_append_right _ hk)

theorem registerExternal_storeKeys (p : NativeEff) (table : RowTable)
    (op : NativeOp) (request : Val) (origin : List Nat) (fiber : FiberId) (token : Nat)
    (stores : Stores) :
    storeKeys ((interpOf p table).registerAsync (.external op request origin) fiber token stores).1 =
      storeKeys stores := by
  have h := registerExternal_internal_state p table op request origin fiber token stores
  simp only [storeKeys, h.1, h.2]

attribute [aesop norm -1 apply (rule_sets := [Effect4.Stores])]
  storeKeys_registerDeferred storeKeys_sleep
attribute [aesop norm simp (rule_sets := [Effect4.Stores])] registerExternal_storeKeys

theorem registerAsync_state (p : NativeEff) (table : RowTable) (completed)
    (stores : Stores) (name : EffName)
    (fiber : FiberId) (token : Nat) :
    storeKeys ((interpAt p completed table).registerAsync name fiber token stores).1 ⊆
      storeKeys stores ++ [(fiber, token)] := by
  have base : storeKeys stores ⊆ storeKeys stores ++ [(fiber, token)] :=
    fun _ h => List.mem_append_left _ h
  cases name with
  | registerAwait cell =>
    simpa only [interpAt, interpOf] using storeKeys_registerDeferred stores cell fiber token
  | store name =>
    cases name with
    | registerAwait cell =>
      simpa only [interpAt, interpOf] using storeKeys_registerDeferred stores cell fiber token
    | registerSleep millis =>
      simpa only [interpAt, interpOf] using storeKeys_sleep stores fiber token millis
    | _ => exact base
  | external op request origin =>
    change storeKeys ((interpOf p table).registerAsync (.external op request origin) fiber token
      stores).1 ⊆ _
    rw [registerExternal_storeKeys]
    exact base
  | _ => exact base

attribute [aesop norm -1 apply (rule_sets := [Effect4.Stores])] registerAsync_state

theorem syncState_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (thunk : EffThunk) (stores : Stores) (value : Val)
    (h : (interpAt p completed table).syncState thunk m.state = some (stores, value)) :
    StateStep m {m with state := stores} := by
  apply StateStep.store state stores
  cases thunk with
  | op operation => exact syncOpStep_storeKeys h
  | store thunk =>
    cases thunk with
    | op operation => exact syncOpStep_storeKeys h
    | _ => cases h
  | _ => cases h

theorem closeScopeUnsafe_state (scope : Nat) (exit : ExitV) (mask : Bool)
    {stores after : Stores} {code : Option Effect4.Machine.Program}
    (h : storesCloseScopeUnsafe scope exit mask stores = some (after, code)) :
    storeKeys after = storeKeys stores ∧ after.deferreds = stores.deferreds := by
  unfold storesCloseScopeUnsafe scopeCloseSnapshot at h
  cases he : stores.scopes.entryAt scope <;> simp only [he, bind, Option.bind, pure, Pure.pure] at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

theorem closeScope_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (scope : Nat) (exit : ExitV)
    (mask : Bool) (fiber : FiberId) (stores : Stores) (code : NCode)
    (h : (interpAt p completed table).closeScope scope exit mask fiber m.state = some (stores, code)) :
    StateStep m {m with state := stores} := by
  change Option.map _ (storesCloseScope scope exit mask m.state) = _ at h
  -- `Scope.close` writes the unsafe close's state (`storesCloseScope_unsafe`)
  obtain ⟨⟨after, prog⟩, hr, hrp⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hrp
  obtain ⟨rfl, _⟩ := hrp
  obtain ⟨program, hu⟩ := storesCloseScope_unsafe hr
  obtain ⟨keys, codes⟩ := closeScopeUnsafe_state scope exit mask hu
  apply StateStep.store state after
  · rw [keys]; exact fun _ h => h

theorem StateStep.spawn (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (code : NCode)
    (sites : raceSites code = []) (options : Supervision.ForkOptions) (site : List Nat := []) :
    StateStep m (spawn (interpAt p completed table) m f code options site).1 := by
  change StateStep m (Effect4.Machine.spawn (interpOf p table) m f code options site).1
  refine ⟨guardState_spawn p table state f code sites options site, Nat.le_refl _, ?_, races_same rfl⟩
  intro fiber token request hr
  rwa [requestOf_spawn (site := site)] at hr

theorem StateStep.start {m : NativeMachine} (state : GuardState m)
    (f : NFiber) (child : FiberId) (immediate : Bool) :
    StateStep m (start m f child immediate).1 := by
  unfold Effect4.Machine.start
  split
  · exact .refl state
  · exact ((StateStep.refl state).arm f.id).emit _

theorem StateStep.forkFinalizers (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (codes : List NCode)
    (sites : ∀ code ∈ codes, raceSites code = []) :
    StateStep m (forkFinalizers (interpAt p completed table) m f codes).1 := by
  induction codes generalizing m with
  | nil => exact .refl state
  | cons code codes ih =>
    simp only [Effect4.Machine.forkFinalizers]
    have step := StateStep.spawn p table completed state f code
      (sites code (List.mem_cons_self ..)) ⟨true, true, .inherit⟩
    exact step.trans (ih step.state (fun c hc => sites c (List.mem_cons_of_mem _ hc)))

theorem StateStep.interruptRecord (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StateStep m (m.update (interruptRecord (interpAt p completed table) who extra f).1) := by
  change StateStep m (m.update (Effect4.Machine.interruptRecord (interpOf p table) who extra f).1)
  exact ⟨guardState_interruptRecord p table state hf who extra, Nat.le_refl _,
    requestOf_interruptRecord_subset p table hf who extra, races_same rfl⟩

theorem StateStep.linkScopeEdits (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StateStep m (linkScopeEdits (interpAt p completed table) m mode scope target who extra).1 := by
  rw [Edits.link_plan_word]
  change StateStep m (Edits.run (Edits.linkWord (interpOf p table) m mode scope target who) m)
  unfold Edits.linkWord
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => dsimp only; exact ⟨guardState_halt state _, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩
  | some status =>
    cases status with
    | some exit =>
      cases hf : m.fiber? target with
      | none => dsimp only; exact ⟨guardState_halt state _, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩
      | some f => dsimp only; exact (StateStep.refl state).emit _
    | none =>
      cases hf : m.fiber? target with
      | none => dsimp only; exact ⟨guardState_halt state _, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩
      | some f =>
        dsimp only
        split
        · exact .refl state
        · cases linked : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => dsimp only; exact ⟨guardState_halt state _, Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩
          | some pair =>
            obtain ⟨stores, key⟩ := pair
            dsimp only
            exact (StateStep.emit (⟨guardState_scopeLinkFiber p table state mode scope target linked,
              Nat.le_refl _, fun _ _ _ h => h, races_same rfl⟩ : StateStep m {m with state := stores}) _)

theorem StateStep.linkScope (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StateStep m (linkScope (interpAt p completed table) m mode scope target who extra).1 := by
  have step := StateStep.linkScopeEdits p table completed state mode scope target who extra
  refine ⟨guardState_linkScope p table state mode scope target who extra, ?_, ?_, ?_⟩
  · unfold Effect4.Machine.linkScope
    rw [(RunMachine.applyFiberEdits_shape _ _).1]
    exact step.tokens
  · exact fun fiber token request h => step.requests fiber token request
      (Messages.requestOf_fiberEdits_subset _ _ fiber token request h)
  · intro id race found
    obtain ⟨next, seen, same⟩ := step.races id race found
    refine ⟨next, ?_, same⟩
    unfold Effect4.Machine.linkScope
    rw [(RunMachine.applyFiberEdits_shape _ _).1]
    exact seen

theorem StateStep.filterObservers {m : NativeMachine} (state : GuardState m) (keep : Observer → Bool) :
    StateStep m (filteredMachine keep m) :=
  ⟨guardState_filterObservers_at state keep, Nat.le_refl _,
    fun _ _ _ hr => (filtered_request keep m _ _).symm ▸ hr, races_same rfl⟩

theorem StateStep.startAfter {m n : NativeMachine} (h : StateStep m n)
    (f : NFiber) (child : FiberId) (immediate : Bool) :
    StateStep m (Effect4.Machine.start n f child immediate).1 := h.trans (.start h.state f child immediate)

theorem stepFrame_step (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    NativeStep m (evaluatePrim.stepFrame (interpAt p completed table) m f yielding) := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact NativeStep.empty ((StateStep.refl state).emit _) rfl

theorem stepFrame_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    StateStep m (evaluatePrim.stepFrame (interpAt p completed table) m f yielding).machine :=
  (stepFrame_step p table completed state f yielding).state

theorem finalizerOr_step (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV) :
    NativeStep m (evaluatePrim.finalizerOr (interpAt p completed table) m f yielding exit) := by
  unfold evaluatePrim.finalizerOr
  repeat' split
  all_goals
    aesop (add safe 90 apply [stepFrame_step])
      (add safe 50 apply [NativeStep.raw, StateStep.emit, StateStep.refl])

theorem finalizerOr_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV) :
    StateStep m (evaluatePrim.finalizerOr (interpAt p completed table) m f yielding exit).machine :=
  (finalizerOr_step p table completed state f yielding exit).state

theorem interruptAs_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (target who : FiberId) :
    StateStep m (evaluatePrim.interruptAs (interpAt p completed table) m f yielding target who).machine := by
  unfold evaluatePrim.interruptAs
  cases hf : m.fiber? target with
  | none => exact .refl state
  | some targetFiber => exact (StateStep.refl state).emit _

theorem NativeStep.countdown (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) (yielding : Bool) (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann) :
    let next := countdownParkEdits (interpAt p completed table) m f targets resume failFast
    NativeStep m ⟨next.1, next.2.1, yielding, outcome, [], next.2.2.2⟩
      (externalRequest f.frame.current = none) := by
  refine ⟨StateStep.countdownEdits p table completed state f targets resume failFast, ?_⟩
  intro current
  unfold Messages.MessageKeys countdownParkEdits
  cases walk : countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
  | mk exits target =>
    cases target with
    | none =>
      simp only [walk]
      intro target observer observed
      exact False.elim (List.not_mem_nil observed)
    | some pair =>
      obtain ⟨target, remaining⟩ := pair
      simp only [walk]
      intro seen observer observed
      have selected := List.mem_singleton.mp observed
      cases selected
      exact Or.inr ⟨rfl, Nat.lt_succ_self _, current⟩

theorem NativeStep.linkScope (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann) (permit : Prop) :
    let next := linkScopeEdits (interpAt p completed table) m mode scope target who extra
    NativeStep m ⟨next.1, f, yielding, outcome, [], next.2⟩ permit := by
  refine ⟨StateStep.linkScopeEdits p table completed state mode scope target who extra, ?_⟩
  intro _ seen observer observed
  unfold linkScopeEdits at observed
  repeat' split at observed
  all_goals aesop (add simp [Messages.MessageKeys, observerKeys])

theorem withFiber_step (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (action : NAction) (sites : actionRaceSites action = [])
    (host : ∃ saved, m.fiber? f.id = some saved) :
    NativeStep m (evaluatePrim.withFiber (interpAt p completed table) m f yielding action)
      (externalRequest f.frame.current = none) := by
  cases action <;> simp only [actionRaceSites] at sites <;>
    unfold evaluatePrim.withFiber <;> dsimp only
  case fork code options site =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split
    · exact (StateStep.spawn p table completed state f code sites options site).startAfter _ _ _
    · exact (StateStep.middleware state true).trans
        ((StateStep.spawn p table completed (StateStep.middleware state true).state f code sites options site).startAfter _ _ _)
  case forkIn code options scope site =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact (StateStep.spawn p table completed state f code sites _ site).startAfter _ _ _
  case forkScoped code options site =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split
    · exact (StateStep.spawn p table completed state f code sites _ site).startAfter _ _ _
    · exact .refl state
  case ambientScope =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split <;> exact .refl state
  case runIn target scope =>
    exact NativeStep.linkScope p table completed state _ _ _ _ _ _ _ _ _
  case interruptAs target who =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact interruptAs_state p table completed state f yielding target who
  case interruptScoped target =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split <;> exact .refl state
  case awaitAll targets => exact NativeStep.countdown p table completed state f targets _ _ _ _
  case awaitAllFailFast targets => exact NativeStep.countdown p table completed state f targets _ _ _ _
  case awaitNewChildren snapshot => exact NativeStep.countdown p table completed state f _ _ _ _ _
  case raceAll entrants site =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact StateStep.beginRace p table completed state f yielding entrants host
      (List.flatMap_eq_nil_iff.mp sites) site
  case raceAllFirst entrants site =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact StateStep.beginRace p table completed state f yielding entrants host
      (List.flatMap_eq_nil_iff.mp sites) site .firstExit
  case setInterruptible code mask =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    cases mask <;> exact .refl state
  case closeScope scope exit =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split
    · exact .refl state
    · rename_i stores code hs
      exact closeScope_state p table completed state scope exit _ _ stores code hs
  case closePar finalizers =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact StateStep.forkFinalizers p table completed state f finalizers
      (List.flatMap_eq_nil_iff.mp sites)
  case dropObservers token =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    exact .refl state
  case cancelRace id =>
    apply NativeStep.keyless ?_ (by
      intro target observer observed
      repeat' split at observed
      all_goals aesop (add simp [observerKeys]))
    split <;> exact .refl state
  all_goals apply NativeStep.keyless ?_ (by
    intro target observer observed
    dsimp only [spawn, start, beginRace, evaluatePrim.interruptAs] at observed
    repeat' split at observed
    all_goals aesop (add simp [observerKeys]))
  all_goals aesop (rule_sets := [Effect4.Stores]) (add safe apply [StateStep.refl, StateStep.emit])

theorem withFiber_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (action : NAction) (sites : actionRaceSites action = [])
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine :=
  (withFiber_step p table completed state f yielding action sites host).state

theorem StateStep.joinPark {m : NativeMachine} (state : GuardState m)
    (f : NFiber) (target : FiberId) (other : NFiber)
    (hf : m.fiber? target = some other) (mode : Supervision.ObserverMode) :
    StateStep m (({m with nextToken := m.nextToken + 1} : NativeMachine).update
      {other with observers := other.observers ++ [.resumeAwait f.id m.nextToken mode]}) := by
  have step := (StateStep.grow state).trans
    (StateStep.observer (StateStep.grow state).state target
      (.resumeAwait f.id m.nextToken mode) (reservedKeys_fresh state f.id))
  simpa only [RunMachine.modify, show ({m with nextToken := m.nextToken + 1} : NativeMachine).fiber? target = some other from hf] using step

theorem StateStep.registerAsync (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (name : EffName) (fiber : FiberId) :
    StateStep m {m with
      state := ((interpAt p completed table).registerAsync name fiber m.nextToken m.state).1,
      nextToken := m.nextToken + 1} := by
  exact StateStep.storeFresh state _ fiber
    (registerAsync_state p table completed m.state name fiber m.nextToken)

theorem StateStep.countdown_result (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resumeWith : Resume EffName) (failFast : Bool) (after : NativeMachine) (next : NFiber)
    (parked : Bool)
    (h : countdownPark (interpAt p completed table) m f targets resumeWith failFast =
      (after, next, parked)) : StateStep m after := by
  simpa only [h] using StateStep.countdown p table completed state f targets resumeWith failFast

theorem StateStep.countdownEdits_result (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resumeWith : Resume EffName) (failFast : Bool) (after : NativeMachine) (next : NFiber)
    (parked : Bool) (edits : List (FiberEdit Err Defect FiberId Ann))
    (h : countdownParkEdits (interpAt p completed table) m f targets resumeWith failFast =
      (after, next, parked, edits)) : StateStep m after := by
  simpa only [h] using StateStep.countdownEdits p table completed state f targets resumeWith failFast

theorem NativeStep.countdown_result (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) (after : NativeMachine) (next : NFiber)
    (parked : Bool) (edits : List (FiberEdit Err Defect FiberId Ann))
    (yielding : Bool) (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (h : countdownParkEdits (interpAt p completed table) m f targets resume failFast =
      (after, next, parked, edits)) :
    NativeStep m ⟨after, next, yielding, outcome, [], edits⟩ (externalRequest f.frame.current = none) := by
  simpa only [h] using NativeStep.countdown p table completed state f targets resume failFast yielding outcome

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] StateStep.registerAsync
attribute [aesop safe forward (rule_sets := [Effect4.Stores])] StateStep.countdownEdits_result

theorem withFiber_actual (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (action : NAction) (sites : actionRaceSites action = [])
    (host : ∃ saved, m.fiber? f.id = some saved) (thunk : EffThunk)
    (current : f.frame.current = .withFiber thunk) :
    NativeStep m (evaluatePrim.withFiber (interpAt p completed table) m f yielding action) := by
  apply NativeStep.admit (withFiber_step p table completed state f yielding action sites host)
  rw [current]
  rfl

theorem countdown_actual (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (after : NativeMachine) (next : NFiber) (parked : Bool)
    (edits : List (FiberEdit Err Defect FiberId Ann)) (yielding : Bool)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (kind : ParkKind) (park : (interpAt p completed table).parkOf f.frame.current = some (.ok kind))
    (h : countdownParkEdits (interpAt p completed table) m f targets .exitsValue false =
      (after, next, parked, edits)) :
    NativeStep m ⟨after, next, yielding, outcome, [], edits⟩ :=
  NativeStep.admit (NativeStep.countdown_result p table completed state f targets _ _
    after next parked edits yielding _ h) (park_internal p table completed f.frame.current kind park)

theorem join_actual (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (target : FiberId) (mode : Supervision.ObserverMode)
    (park : (interpAt p completed table).parkOf f.frame.current = some (.ok (.join target mode))) :
    let token := m.nextToken
    let grown : NativeMachine := {m with nextToken := token + 1}
    let name := (interpAt p completed table).cancelName (interpAt p completed table).parkCancelName f.id token
    let next := ({f with frame := {f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack}} : NFiber).park
      ⟨token, some target, [], [], .void, false⟩
    NativeStep m ⟨grown.emit [RunEvent.parkedOn next.id token], next, yielding, .parked, [],
      [.observe target (.resumeAwait f.id token mode)]⟩ := by
  refine ⟨(StateStep.grow state).emit _, ?_⟩
  intro _ seen observer observed
  cases List.mem_singleton.mp observed
  exact Or.inr ⟨rfl, Nat.lt_succ_self _, park_internal p table completed f.frame.current _ park⟩

theorem NativeStep.registerRace {m : NativeMachine} (state : GuardState m)
    (f : NFiber) (yielding : Bool) (id : Nat) :
    NativeStep m (registerRace m f yielding id) := by
  apply NativeStep.empty (StateStep.registerRace state f yielding id)
  unfold Effect4.Machine.registerRace
  split <;> rfl

theorem evaluatePrim_step (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    NativeStep m (evaluatePrim (interpAt p completed table) m f yielding) := by
  have ha (thunk : EffThunk) (action : NAction)
      (h : (interpAt p completed table).withFiberOf thunk = some action) :
      actionRaceSites action = [] := by
    have sites := raceSites_withFiberOf p table thunk
    change (interpOf p table).withFiberOf thunk = some action at h
    rw [h] at sites
    exact sites
  have parked (targets : List FiberId) (after : NativeMachine) (next : NFiber)
      (edits : List (FiberEdit Err Defect FiberId Ann))
      (park : (interpAt p completed table).parkOf f.frame.current = some (.ok (.awaitAll targets)))
      (h : countdownParkEdits (interpAt p completed table) m f targets .exitsValue false =
        (after, next, true, edits)) : NativeStep m ⟨after, next, yielding, .parked, [], edits⟩ :=
    countdown_actual p table completed state f targets after next true edits yielding .parked _ park h
  have continued (targets : List FiberId) (after : NativeMachine) (next : NFiber)
      (edits : List (FiberEdit Err Defect FiberId Ann))
      (park : (interpAt p completed table).parkOf f.frame.current = some (.ok (.awaitAll targets)))
      (h : countdownParkEdits (interpAt p completed table) m f targets .exitsValue false =
        (after, next, false, edits)) : NativeStep m ⟨after, next, yielding, .continue_, [], edits⟩ :=
    countdown_actual p table completed state f targets after next false edits yielding .continue_ _ park h
  have joining := join_actual p table completed state f yielding
  unfold evaluatePrim
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe apply [StateStep.refl, StateStep.emit, StateStep.arm, StateStep.grow,
        StateStep.registerRace])
      (add safe 90 apply [NativeStep.raw, withFiber_actual, stepFrame_step, finalizerOr_step, NativeStep.registerRace])
      (add unsafe 90% apply [parked, continued])
      (add safe apply [joining])
      (add safe forward [syncState_state, ha])

theorem evaluatePrim_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluatePrim (interpAt p completed table) m f yielding).machine :=
  (evaluatePrim_step p table completed state f yielding host).state

theorem StateStep.closeUnsafe {m n : NativeMachine} (step : StateStep m n)
    (scope : Nat) (exit : ExitV) (mask : Bool) (stores : Stores) (code : Option Effect4.Machine.Program)
    (h : storesCloseScopeUnsafe scope exit mask n.state = some (stores, code)) :
    StateStep m {n with state := stores} := by
  obtain ⟨keys, codes⟩ := closeScopeUnsafe_state scope exit mask h
  apply step.trans (.store step.state stores ?_)
  · rw [keys]; exact fun _ h => h

theorem NativeStep.before {m n : NativeMachine}
    {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores}
    (before : StateStep m n) (tokens : n.nextToken = m.nextToken)
    (step : NativeStep n next) : NativeStep m next := by
  refine ⟨before.trans step.state, ?_⟩
  simpa only [Messages.MessageKeys, tokens] using step.messages

theorem enterScoped_step (p : NativeEff) (point : Point)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    NativeStep m (enterScoped p point m f yielding) :=
  NativeStep.empty (.store state _ (fun _ h => h)) rfl

theorem enterScoped_state (p : NativeEff) (point : Point)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    StateStep m (enterScoped p point m f yielding).machine :=
  (enterScoped_step p point state f yielding).state

theorem exitScoped_step (p : NativeEff) {m : NativeMachine}
    (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    NativeStep m (exitScoped p m f yielding exit) := by
  unfold exitScoped
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe apply [evaluatePrim_step, NativeStep.raw, StateStep.refl, StateStep.emit, StateStep.closeUnsafe])

theorem exitScoped_state (p : NativeEff) {m : NativeMachine}
    (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (exitScoped p m f yielding exit).machine :=
  (exitScoped_step p state f yielding exit host).state

theorem evaluateNative_step (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    NativeStep m (evaluateNative p m f yielding table) := by
  unfold evaluateNative
  repeat' split
  all_goals aesop (add safe apply [evaluatePrim_step, enterScoped_step, exitScoped_step])

theorem evaluateNative_state (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluateNative p m f yielding table).machine :=
  (evaluateNative_step p table state f yielding host).state

theorem iteration_step (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    letI := evaluatorFor p table
    NativeStep m (iteration (interpOf p table) m f yielding) := by
  letI := evaluatorFor p table
  have hid : (countOp (runloopTop f)).id = f.id := by
    unfold runloopTop
    split <;> rfl
  have host' : ∃ saved, m.fiber? (countOp (runloopTop f)).id = some saved := by
    rw [hid]; exact host
  unfold iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_step p table state _ _ host'
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      apply NativeStep.before ((StateStep.refl state).emit _) rfl
      apply evaluateNative_step p table (guardState_emit state _)
      exact host'
    · cases hy

theorem iteration_state (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    letI := evaluatorFor p table
    StateStep m (iteration (interpOf p table) m f yielding).machine :=
  (iteration_step p table state f yielding host).state

end Effect4.Program.Guard.NativeState
