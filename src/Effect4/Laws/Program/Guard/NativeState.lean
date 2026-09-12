import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.FrameOwned

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

theorem StateStep.refl {m : NativeMachine} (state : GuardState m) : StateStep m m :=
  ⟨state, Nat.le_refl _, fun _ _ _ h => h⟩

theorem StateStep.trans {m n o : NativeMachine} (a : StateStep m n) (b : StateStep n o) :
    StateStep m o :=
  ⟨b.state, Nat.le_trans a.tokens b.tokens,
    fun fiber token request h => a.requests fiber token request (b.requests fiber token request h)⟩

theorem StateStep.reserved {m n : NativeMachine} (h : StateStep m n)
    {keys : List GuardKey} (keysBefore : ReservedKeys m keys) : ReservedKeys n keys :=
  reservedKeys_of_requests_subset keysBefore h.tokens h.requests

theorem StateStep.emit {m n : NativeMachine} (h : StateStep m n) (events) :
    StateStep m (n.emit events) := ⟨guardState_emit h.state events, h.tokens, h.requests⟩

theorem StateStep.arm {m n : NativeMachine} (h : StateStep m n) (owner : FiberId) :
    StateStep m (n.arm owner) := ⟨guardState_arm h.state owner, h.tokens, h.requests⟩

theorem StateStep.middleware {m : NativeMachine} (state : GuardState m) (flag : Bool) :
    StateStep m {m with middlewareInstalled := flag} := by
  refine ⟨?_, Nat.le_refl _, fun _ _ _ h => h⟩
  rcases state with ⟨a,b,c,d,e,f,g,h,i,j,k,l,n,o,q⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,n,o,q⟩

theorem StateStep.grow {m : NativeMachine} (state : GuardState m) :
    StateStep m {m with nextToken := m.nextToken + 1} :=
  ⟨guardState_increaseTokens state _ (Nat.le_succ _), Nat.le_succ _, fun _ _ _ h => h⟩

theorem StateStep.store {m : NativeMachine} (state : GuardState m) (stores : Stores)
    (keys : storeKeys stores ⊆ storeKeys m.state) (codes : DeferredCodes stores.deferreds) :
    StateStep m {m with state := stores} :=
  ⟨guardState_withState state stores keys codes, Nat.le_refl _, fun _ _ _ h => h⟩

theorem StateStep.storeFresh {m : NativeMachine} (state : GuardState m)
    (stores : Stores) (fiber : FiberId)
    (keys : storeKeys stores ⊆ storeKeys m.state ++ [(fiber, m.nextToken)])
    (codes : DeferredCodes stores.deferreds) :
    StateStep m {m with state := stores, nextToken := m.nextToken + 1} :=
  ⟨guardState_storeFresh state stores fiber keys codes, Nat.le_succ _, fun _ _ _ h => h⟩

theorem StateStep.observer {m : NativeMachine} (state : GuardState m)
    (target : FiberId) (observer : Observer) (keys : ReservedKeys m (observerKeys observer)) :
    StateStep m (m.modify target fun f => {f with observers := f.observers ++ [observer]}) := by
  refine ⟨guardState_addObserver state target observer keys, ?_, ?_⟩
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
      rfl rfl rfl (state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr)),
      Nat.le_refl _, fun _ _ _ h => h⟩
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
    refine ⟨state.raceIds, by simp, ?_⟩
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
  · exact ⟨state.internalCodes.1, state.internalCodes.2.1,
      state.internalCodes.2.2.1, hall _ state.internalCodes.2.2.2 programs⟩

theorem StateStep.beginRace (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (entrants : List NCode) (host : ∃ saved, m.fiber? f.id = some saved)
    (programs : ∀ code ∈ entrants, raceSites code = []) :
    StateStep m (beginRace (interpAt p completed table) m f yielding entrants).machine := by
  apply StateStep.emit
  exact ⟨guardState_appendRace state _ rfl rfl host programs, Nat.le_succ _, fun _ _ _ h => h⟩

theorem StateStep.countdown (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (targets : List FiberId)
    (resumeWith : Resume EffName) (failFast : Bool) :
    StateStep m (countdownPark (interpAt p completed table) m f targets resumeWith failFast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact .grow state
  · exact ((StateStep.grow state).trans
      (.observer (guardState_increaseTokens state _ (Nat.le_succ _)) _ (.countdown f.id m.nextToken)
        (reservedKeys_fresh state f.id))).emit _

theorem registerAsync_state (p : NativeEff) (table : RowTable) (completed)
    (stores : Stores) (hd : DeferredCodes stores.deferreds) (name : EffName)
    (fiber : FiberId) (token : Nat) :
    storeKeys ((interpAt p completed table).registerAsync name fiber token stores).1 ⊆
      storeKeys stores ++ [(fiber, token)] ∧
    DeferredCodes ((interpAt p completed table).registerAsync name fiber token stores).1.deferreds := by
  have base : storeKeys stores ⊆ storeKeys stores ++ [(fiber, token)] :=
    fun _ h => List.mem_append_left _ h
  have deferred (cell : DeferredKey) :
      storeKeys {stores with deferreds := (stores.deferreds.register cell fiber token).1} ⊆
          storeKeys stores ++ [(fiber, token)] ∧
        DeferredCodes (stores.deferreds.register cell fiber token).1 := by
    refine ⟨?_, (deferredCodes_register hd cell fiber token).1⟩
    intro key hk
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (List.mem_append_left _ hk)
    · rcases List.mem_append.mp (deferredKeys_register_subset stores.deferreds cell fiber token hk) with hk | hk
      · exact List.mem_append_left _ (List.mem_append_right _ hk)
      · exact List.mem_append_right _ hk
  cases name <;> try exact ⟨base, hd⟩
  case registerAwait cell => exact deferred cell
  case store name =>
    cases name <;> try exact ⟨base, hd⟩
    case registerAwait cell => exact deferred cell
    case registerSleep millis =>
      refine ⟨?_, hd⟩
      intro key hk
      change key ∈ wakeKeys (stores.timers.sleep fiber token millis).wake ++ deferredKeys stores.deferreds at hk
      rcases List.mem_append.mp hk with hk | hk
      · rcases (wakeKeys_register_mem _ _ _ _ _).mp hk with hk | hk
        · exact List.mem_append_left _ (List.mem_append_left _ hk)
        · exact List.mem_append_right _ (List.mem_singleton.mpr hk)
      · exact List.mem_append_left _ (List.mem_append_right _ hk)
  case external op request =>
    have h := registerExternal_internal_state p table op request fiber token stores
    change storeKeys ((interpOf p table).registerAsync (.external op request) fiber token stores).1 ⊆ _ ∧
      DeferredCodes ((interpOf p table).registerAsync (.external op request) fiber token stores).1.deferreds
    unfold storeKeys
    rw [h.1, h.2]
    exact ⟨base, hd⟩

theorem syncState_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (thunk : EffThunk) (stores : Stores) (value : Val)
    (h : (interpAt p completed table).syncState thunk m.state = some (stores, value)) :
    StateStep m {m with state := stores} := by
  have hd : DeferredCodes m.state.deferreds := ⟨state.internalCodes.1, state.internalCodes.2.1⟩
  cases thunk <;> simp only [interpAt, interpOf] at h
  all_goals try contradiction
  case op op => exact .store state stores (syncOpStep_storeKeys h) (syncOpStep_deferredCodes hd h)
  case store thunk =>
    cases thunk <;> simp only at h
    all_goals try contradiction
    exact .store state stores (syncOpStep_storeKeys h) (syncOpStep_deferredCodes hd h)

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
  unfold storesCloseScope at h
  cases hu : storesCloseScopeUnsafe scope exit mask m.state with
  | none => simp only [hu, Option.map_none] at h; cases h
  | some result =>
    rcases result with ⟨after, prog⟩
    simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    obtain ⟨keys, codes⟩ := closeScopeUnsafe_state scope exit mask hu
    apply StateStep.store state after
    · rw [keys]; exact fun _ h => h
    · rw [codes]; exact ⟨state.internalCodes.1, state.internalCodes.2.1⟩

theorem StateStep.spawn (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (code : NCode)
    (sites : raceSites code = []) (options : Supervision.ForkOptions) :
    StateStep m (spawn (interpAt p completed table) m f code options).1 := by
  change StateStep m (Effect4.Machine.spawn (interpOf p table) m f code options).1
  refine ⟨guardState_spawn p table state f code sites options, Nat.le_refl _, ?_⟩
  intro fiber token request hr
  rwa [requestOf_spawn] at hr

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
    requestOf_interruptRecord_subset p table hf who extra⟩

theorem StateStep.linkScope (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StateStep m (linkScope (interpAt p completed table) m mode scope target who extra).1 := by
  change StateStep m (Effect4.Machine.linkScope (interpOf p table) m mode scope target who extra).1
  refine ⟨guardState_linkScope p table state mode scope target who extra, ?_, ?_⟩
  · unfold Effect4.Machine.linkScope
    repeat' first | exact Nat.le_refl _ | dsimp only | split | unfold RunMachine.modify
  · intro fiber token request hr
    unfold Effect4.Machine.linkScope at hr
    cases hs : (interpOf p table).scopeStatus scope m.state with
    | none => simp only [hs] at hr; exact hr
    | some status =>
      cases status with
      | some exit =>
        simp only [hs] at hr
        cases hf : m.fiber? target with
        | none => simp only [hf] at hr; exact hr
        | some f =>
          simp only [hf] at hr
          exact requestOf_interruptRecord_subset p table
            (by simpa only [fiber_id_of_lookup hf] using hf) who extra fiber token request hr
      | none =>
        simp only [hs] at hr
        cases hf : m.fiber? target with
        | none => simp only [hf] at hr; exact hr
        | some f =>
          simp only [hf] at hr
          split at hr
          · exact hr
          · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
            | none => simp only [hl] at hr; exact hr
            | some result =>
              rcases result with ⟨after, key⟩
              simp only [hl] at hr
              change requestOf (({m with state := after} : NativeMachine).modify target
                (fun g => {g with observers := g.observers ++ [.dropScopeFinalizer scope key]}))
                  fiber token = some request at hr
              rwa [requestOf_addObserver] at hr

abbrev filteredFiber (keep : Observer → Bool) (f : NFiber) : NFiber :=
  {f with observers := f.observers.filter keep}

abbrev filteredMachine (keep : Observer → Bool) (m : NativeMachine) : NativeMachine :=
  {m with fibers := m.fibers.map (filteredFiber keep)}

theorem filtered_lookup (keep : Observer → Bool) (m : NativeMachine) (fiber : FiberId) :
    (filteredMachine keep m).fiber? fiber = (m.fiber? fiber).map (filteredFiber keep) := by
  simp only [RunMachine.fiber?, List.find?_map, Function.comp_def]

theorem filtered_request (keep : Observer → Bool) (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    requestOf (filteredMachine keep m) fiber token = requestOf m fiber token := by
  unfold requestOf
  rw [filtered_lookup]
  cases hf : m.fiber? fiber <;> rfl

theorem filtered_fiberKeys (keep : Observer → Bool) (f : NFiber) :
    fiberKeys (filteredFiber keep f) ⊆ fiberKeys f := by
  intro key hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨obs, ho, hk⟩ := List.mem_flatMap.mp hk
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨obs, (List.mem_filter.mp ho).1, hk⟩)
  · exact List.mem_append_right _ hk

theorem filtered_internalKeys (keep : Observer → Bool) (m : NativeMachine) :
    internalKeys (filteredMachine keep m) ⊆ internalKeys m := by
  intro key hk
  rw [internalKeys_store_decomposition] at hk ⊢
  rcases List.mem_append.mp hk with hk | hk
  · exact List.mem_append_left _ hk
  · obtain ⟨f, hf, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp hf
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨old, hm, filtered_fiberKeys keep old hk⟩)

theorem StateStep.filterObservers {m : NativeMachine} (state : GuardState m) (keep : Observer → Bool) :
    StateStep m (filteredMachine keep m) := by
  have hall (P : NFiber → Prop) (old : ∀ f ∈ m.fibers, P (filteredFiber keep f)) :
      ∀ f ∈ (filteredMachine keep m).fibers, P f := by
    intro f hf
    obtain ⟨oldf, hm, rfl⟩ := List.mem_map.mp hf
    exact old oldf hm
  refine ⟨?_, Nat.le_refl _, ?_⟩
  · constructor
    · simpa only [List.map_map, Function.comp_def] using state.fiberIds
    · exact hall _ state.fibersBelow
    · exact state.raceIds
    · exact state.racesBelow
    · intro race hr
      obtain ⟨f, hf⟩ := state.raceHosts race hr
      exact ⟨filteredFiber keep f, by rw [filtered_lookup, hf]; rfl⟩
    · exact fun key hk => state.keysBelow key (filtered_internalKeys keep m hk)
    · intro fiber token request hr
      rw [filtered_request] at hr
      exact state.requestsBelow fiber token request hr
    · intro fiber token request hr hk
      rw [filtered_request] at hr
      exact state.requestsOwned fiber token request hr (filtered_internalKeys keep m hk)
    · exact hall _ state.pendingShape
    · exact hall _ state.parkedIdle
    · exact hall _ state.parkedBelow
    · exact hall _ state.exited
    · exact hall _ state.deferredCause
    · exact hall _ state.frameCodes
    · exact ⟨state.internalCodes.1, state.internalCodes.2.1,
        hall _ state.internalCodes.2.2.1, state.internalCodes.2.2.2⟩
  · intro fiber token request hr
    rwa [filtered_request] at hr

theorem StateStep.startAfter {m n : NativeMachine} (h : StateStep m n)
    (f : NFiber) (child : FiberId) (immediate : Bool) :
    StateStep m (Effect4.Machine.start n f child immediate).1 := h.trans (.start h.state f child immediate)

theorem stepFrame_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    StateStep m (evaluatePrim.stepFrame (interpAt p completed table) m f yielding).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact (StateStep.refl state).emit _

theorem finalizerOr_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV) :
    StateStep m (evaluatePrim.finalizerOr (interpAt p completed table) m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  repeat' first
    | exact (StateStep.refl state).emit _
    | exact stepFrame_state p table completed state f yielding
    | dsimp only
    | split

theorem interruptAs_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (target who : FiberId) :
    StateStep m (evaluatePrim.interruptAs (interpAt p completed table) m f yielding target who).machine := by
  unfold evaluatePrim.interruptAs
  cases hf : m.fiber? target with
  | none => exact .refl state
  | some targetFiber =>
    exact (StateStep.interruptRecord p table completed state
      (by simpa only [fiber_id_of_lookup hf] using hf) (some who) _).emit _

theorem withFiber_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (action : NAction) (sites : actionRaceSites action = [])
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine := by
  cases action <;> simp only [actionRaceSites] at sites <;>
    unfold evaluatePrim.withFiber <;> dsimp only
  all_goals try exact .refl state
  all_goals try exact (StateStep.refl state).emit _
  case fork code options =>
    split
    · exact (StateStep.spawn p table completed state f code sites options).startAfter _ _ _
    · exact (StateStep.middleware state true).trans
        ((StateStep.spawn p table completed (StateStep.middleware state true).state f code sites options).startAfter _ _ _)
  case forkIn code options scope =>
    exact (StateStep.spawn p table completed state f code sites _).startAfter _ _ _
  case forkScoped code options =>
    split
    · exact (StateStep.spawn p table completed state f code sites _).startAfter _ _ _
    · exact .refl state
  case ambientScope => split <;> exact .refl state
  case runIn target scope => exact StateStep.linkScope p table completed state _ _ _ _ _
  case interruptAs target who => exact interruptAs_state p table completed state f yielding target who
  case interruptScoped target => split <;> exact .refl state
  case awaitAll targets => exact StateStep.countdown p table completed state f targets _ _
  case awaitAllFailFast targets => exact StateStep.countdown p table completed state f targets _ _
  case awaitNewChildren snapshot => exact StateStep.countdown p table completed state f _ _ _
  case raceAll entrants =>
    exact StateStep.beginRace p table completed state f yielding entrants host
      (List.flatMap_eq_nil_iff.mp sites)
  case setInterruptible code mask => cases mask <;> exact .refl state
  case closeScope scope exit =>
    split
    · exact .refl state
    · rename_i stores code hs
      exact closeScope_state p table completed state scope exit _ _ stores code hs
  case closePar finalizers =>
    exact StateStep.forkFinalizers p table completed state f finalizers
      (List.flatMap_eq_nil_iff.mp sites)
  case dropObservers token => exact StateStep.filterObservers state _
  case cancelRace id => split <;> exact .refl state

theorem StateStep.joinPark {m : NativeMachine} (state : GuardState m)
    (f : NFiber) (target : FiberId) (other : NFiber)
    (hf : m.fiber? target = some other) (mode : Supervision.ObserverMode) :
    StateStep m (({m with nextToken := m.nextToken + 1} : NativeMachine).update
      {other with observers := other.observers ++ [.resumeAwait f.id m.nextToken mode]}) := by
  have step := (StateStep.grow state).trans
    (StateStep.observer (StateStep.grow state).state target
      (.resumeAwait f.id m.nextToken mode) (reservedKeys_fresh state f.id))
  simpa only [RunMachine.modify, show ({m with nextToken := m.nextToken + 1} : NativeMachine).fiber? target = some other from hf] using step

theorem evaluatePrim_state (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluatePrim (interpAt p completed table) m f yielding).machine := by
  have ha (thunk : EffThunk) (action : NAction)
      (h : (interpAt p completed table).withFiberOf thunk = some action) :
      actionRaceSites action = [] := by
    have sites := raceSites_withFiberOf p table thunk
    change (interpOf p table).withFiberOf thunk = some action at h
    rw [h] at sites
    exact sites
  unfold evaluatePrim
  repeat' first
    | exact .refl state
    | exact ((StateStep.grow state).arm f.id).emit _
    | exact StateStep.registerRace state f yielding _
    | exact StateStep.countdown p table completed state f _ _ _
    | exact (StateStep.joinPark state f _ _ (by assumption) _).emit _
    | exact withFiber_state p table completed state f yielding _ (ha _ _ (by assumption)) host
    | exact stepFrame_state p table completed state f yielding
    | exact finalizerOr_state p table completed state f yielding _
    | exact syncState_state p table completed state _ _ _ (by assumption)
    | dsimp only
    | split
  all_goals
    have hd : DeferredCodes m.state.deferreds := ⟨state.internalCodes.1, state.internalCodes.2.1⟩
    first
    | exact .storeFresh state _ f.id (registerAsync_state p table completed m.state hd _ f.id m.nextToken).1
        (registerAsync_state p table completed m.state hd _ f.id m.nextToken).2
    | exact (StateStep.storeFresh state _ f.id (registerAsync_state p table completed m.state hd _ f.id m.nextToken).1
        (registerAsync_state p table completed m.state hd _ f.id m.nextToken).2).emit _

theorem StateStep.closeUnsafe {m n : NativeMachine} (step : StateStep m n)
    (scope : Nat) (exit : ExitV) (mask : Bool) (stores : Stores) (code : Option Effect4.Machine.Program)
    (h : storesCloseScopeUnsafe scope exit mask n.state = some (stores, code)) :
    StateStep m {n with state := stores} := by
  obtain ⟨keys, codes⟩ := closeScopeUnsafe_state scope exit mask h
  apply step.trans (.store step.state stores ?_ ?_)
  · rw [keys]; exact fun _ h => h
  · rw [codes]; exact ⟨step.state.internalCodes.1, step.state.internalCodes.2.1⟩

theorem enterScoped_state (p : NativeEff) (point : Point)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool) :
    StateStep m (enterScoped p point m f yielding).machine :=
  .store state _ (fun _ h => h) ⟨state.internalCodes.1, state.internalCodes.2.1⟩

theorem exitScoped_state (p : NativeEff) {m : NativeMachine}
    (state : GuardState m) (f : NFiber) (yielding : Bool) (exit : ExitV)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (exitScoped p m f yielding exit).machine := by
  unfold exitScoped
  repeat' first
    | exact evaluatePrim_state p [] m.completedExits state f yielding host
    | exact (StateStep.refl state).emit _
    | exact StateStep.closeUnsafe ((StateStep.refl state).emit _) _ _ _ _ _ (by assumption)
    | exact (StateStep.closeUnsafe ((StateStep.refl state).emit _) _ _ _ _ _ (by assumption)).emit _
    | dsimp only
    | split

theorem evaluateNative_state (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    StateStep m (evaluateNative p m f yielding table).machine := by
  unfold evaluateNative
  repeat' first
    | exact evaluatePrim_state p table m.completedExits state f yielding host
    | exact enterScoped_state p _ state f yielding
    | exact exitScoped_state p state f yielding _ host
    | dsimp only
    | split

theorem iteration_state (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m) (f : NFiber) (yielding : Bool)
    (host : ∃ saved, m.fiber? f.id = some saved) :
    letI := evaluatorFor p table
    StateStep m (iteration (interpOf p table) m f yielding).machine := by
  letI := evaluatorFor p table
  have hid : (countOp (runloopTop f)).id = f.id := by
    unfold runloopTop
    split <;> rfl
  have host' : ∃ saved, m.fiber? (countOp (runloopTop f)).id = some saved := by
    rw [hid]; exact host
  unfold iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_state p table state _ _ host'
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      apply ((StateStep.refl state).emit _).trans
      apply evaluateNative_state p table (guardState_emit state _)
      exact host'
    · cases hy


end Effect4.Program.Guard.NativeState
