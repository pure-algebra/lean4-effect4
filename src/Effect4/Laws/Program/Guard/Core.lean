import Effect4.Api

/-!
DI-68 guard ownership for the owner-approved reachable-machine scope. A prefix is raw
decision data with an explicit command budget for each step. The program, table,
compile budget, initial choices and initial oracle answers stay fixed. No decision
admission or sufficiency assumption is built into reachability.

Existing invariants reviewed: Machine.Book.MachineOk/PendingOk, the concrete
Simulation.Hooks.StoresOk, Stores.WF, and the handle-minting predicates. Their
statements do not assert guard-token ownership. The predicates below track that
ownership explicitly, with initial-state and individual command lemmas.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Effect4.Program.Guard

open Effect4 Effect4.Machine Effect4.Program

abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev Prefix := List (Nat × NativeDecision)

def executePrefix (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (history : Prefix) : NativeMachine :=
  history.foldl (fun m s => steppedBy p s.1 table m s.2) m

def Reachable (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (choices : List Bool) (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine) : Prop :=
  ∃ history : Prefix, m = executePrefix p table (Api.load p compileFuel choices answers) history

theorem reachable_load (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (choices : List Bool) (answers : List (Completion Val Err Defect FiberId Ann)) :
    Reachable p table compileFuel choices answers (Api.load p compileFuel choices answers) :=
  ⟨[], rfl⟩

theorem reachable_step {p : NativeEff} {table : RowTable} {compileFuel : Nat}
    {choices : List Bool} {answers : List (Completion Val Err Defect FiberId Ann)}
    {m : NativeMachine} (h : Reachable p table compileFuel choices answers m)
    (fuel : Nat) (d : NativeDecision) :
    Reachable p table compileFuel choices answers (steppedBy p fuel table m d) := by
  obtain ⟨history, rfl⟩ := h
  refine ⟨history ++ [(fuel, d)], ?_⟩
  simp only [executePrefix, List.foldl_append, List.foldl_cons, List.foldl_nil]

def Interrupted (f : NFiber) : Prop :=
  f.interruptPending = true ∨ f.exit.isSome = true

def InterruptedAt (m : NativeMachine) (fiber : FiberId) : Prop :=
  ∃ f, m.fiber? fiber = some f ∧ Interrupted f

/-- The exact one-step conclusion, with interruption read after the step. -/
def GuardPersistsAt (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (fuel : Nat) (d : NativeDecision) : Prop :=
  requestOf (steppedBy p fuel table m d) fiber token = some request ∨
    InterruptedAt (steppedBy p fuel table m d) fiber

/-- Both guard laws exclude exactly the answer addressed to this key. -/
def NotKeyAnswer (fiber : FiberId) (token : Nat) (d : NativeDecision) : Prop :=
  ∀ answer, d ≠ .answerAsync fiber token answer

theorem notKeyAnswer_answer_iff (fiber target : FiberId) (token offered : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    NotKeyAnswer fiber token (.answerAsync target offered answer) ↔
      target ≠ fiber ∨ offered ≠ token := by
  constructor
  · intro h
    by_cases hf : target = fiber
    · right
      intro ht
      exact h answer (by rw [hf, ht])
    · exact Or.inl hf
  · rintro (hf | ht) other he
    · exact hf (RunDecision.answerAsync.inj he).1
    · exact ht (RunDecision.answerAsync.inj he).2.1

def externalRequest : NCode → Option (NativeOp × Val)
  | .async (.external op request) _ _ => some (op, request)
  | _ => none

theorem requestOf_shape {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : requestOf m fiber token = some request) :
    ∃ f, m.fiber? fiber = some f ∧ f.parked = .withGuard token ∧
      externalRequest f.frame.current = some request := by
  unfold requestOf at h
  cases hf : m.fiber? fiber with
  | none => simp [hf] at h
  | some f =>
    refine ⟨f, rfl, ?_⟩
    by_cases hp : f.parked = .withGuard token
    · refine ⟨hp, ?_⟩
      simp only [hf, guard] at h
      cases hc : f.frame.current <;> simp_all [externalRequest]
      rename_i register signal cancel
      cases register <;> simp_all
    · simp [hf, hp, guard] at h
      cases h

theorem requestOf_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) (fiber : FiberId) (token : Nat) :
    requestOf (Api.load p compileFuel choices answers) fiber token = none := by
  unfold requestOf
  simp only [Api.load, RunMachine.fiber?, List.find?_cons, RunFiber.make, List.find?_nil]
  split <;> simp [guard]

/-- Equality of these three fields is precisely what `requestOf` observes. -/
def RequestView (f g : NFiber) : Prop :=
  f.id = g.id ∧ f.parked = g.parked ∧ f.frame.current = g.frame.current

abbrev GuardKey := FiberId × Nat

def wakeKeys {α : Type} (w : WakeList α) : List GuardKey :=
  w.waiters.map (fun a => (a.fiber, a.token)) ++
    w.batch.toList.flatMap (fun b => b.map fun a => (a.fiber, a.token))

def taskKeys : Task EffName EffThunk Val Err Defect FiberId Ann → List GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | _ => []

def observerKeys : Observer → List GuardKey
  | .resumeAwait fiber token _ => [(fiber, token)]
  | .countdown fiber token => [(fiber, token)]
  | _ => []

/-- Internal sources of resumes; the race callbacks are covered by their race's key. -/
def internalKeys (m : NativeMachine) : List GuardKey :=
  wakeKeys m.state.timers.wake ++
    m.state.deferreds.cells.flatMap (fun c => wakeKeys c.wake) ++
    m.state.deferreds.due.map (fun d => (d.waiter, d.token)) ++
    m.races.map (fun r => (r.host, r.token)) ++
    m.fibers.flatMap (fun f =>
      f.observers.flatMap observerKeys ++
      f.dispatcher.buckets.flatMap fun b => b.tasks.flatMap taskKeys)

def RequestsOwned (m : NativeMachine) : Prop :=
  ∀ fiber token request, requestOf m fiber token = some request →
    (fiber, token) ∉ internalKeys m

def InternalKeysBelow (m : NativeMachine) : Prop :=
  ∀ k ∈ internalKeys m, k.2 < m.nextToken

theorem internalKeys_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    internalKeys (Api.load p compileFuel choices answers) = [] := rfl

theorem requestsOwned_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    RequestsOwned (Api.load p compileFuel choices answers) := by
  intro fiber token request h
  rw [requestOf_load] at h
  cases h

theorem internalKeysBelow_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    InternalKeysBelow (Api.load p compileFuel choices answers) := by
  intro k hk
  rw [internalKeys_load] at hk
  cases hk

theorem fresh_key_not_internal {m : NativeMachine} (h : InternalKeysBelow m) (fiber : FiberId) :
    (fiber, m.nextToken) ∉ internalKeys m := by
  intro hk
  exact Nat.lt_irrefl _ (h _ hk)

theorem requestOf_eq_of_fiber_eq {m m' : NativeMachine} (fiber : FiberId) (token : Nat)
    (h : m.fiber? fiber = m'.fiber? fiber) : requestOf m fiber token = requestOf m' fiber token := by
  simp only [requestOf, h]

theorem fiber_id_of_lookup {m : NativeMachine} {fiber : FiberId} {f : NFiber}
    (h : m.fiber? fiber = some f) : f.id = fiber := by
  exact of_decide_eq_true (List.find?_some (p := fun g : NFiber => decide (g.id = fiber)) h)

theorem fiber_lookup_update (m : NativeMachine) (f : NFiber) (fiber : FiberId) :
    (m.update f).fiber? fiber =
      (m.fiber? fiber).map (fun g => if g.id = f.id then f else g) := by
  unfold RunMachine.update RunMachine.fiber?
  rw [List.find?_map]
  have hp : (fun g : NFiber => decide ((if g.id = f.id then f else g).id = fiber)) =
      (fun g : NFiber => decide (g.id = fiber)) := by
    funext g
    split <;> simp_all
  rw [show ((fun g : NFiber => decide (g.id = fiber)) ∘
      (fun g => if g.id = f.id then f else g)) = _ from hp]

theorem requestOf_update_other (m : NativeMachine) (f : NFiber) (fiber : FiberId) (token : Nat)
    (hne : f.id ≠ fiber) : requestOf (m.update f) fiber token = requestOf m fiber token := by
  apply requestOf_eq_of_fiber_eq
  rw [fiber_lookup_update]
  cases hf : m.fiber? fiber with
  | none => rfl
  | some g =>
    have hid := fiber_id_of_lookup hf
    simp only [Option.map_some, hid, Ne.symm hne, ↓reduceIte]

theorem requestOf_modify_view (m : NativeMachine) (target fiber : FiberId) (token : Nat)
    (k : NFiber → NFiber) (hk : ∀ f, RequestView f (k f)) :
    requestOf (m.modify target k) fiber token = requestOf m fiber token := by
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => rfl
  | some f =>
    have hid := fiber_id_of_lookup hf
    have hv := hk f
    by_cases he : target = fiber
    · subst fiber
      simp only [requestOf, fiber_lookup_update, hf, Option.map_some, ← hv.1, ↓reduceIte]
      dsimp only [bind, Option.bind]
      rw [← hv.2.1, ← hv.2.2]
    · exact requestOf_update_other m (k f) fiber token (by rw [← hv.1, hid]; exact he)

theorem requestOf_yieldVerdict (p : NativeEff) (fuel : Nat) (table : RowTable)
    (m : NativeMachine) (fiber target : FiberId) (token : Nat) (verdict : Bool) :
    requestOf (steppedBy p fuel table m (.yieldVerdict target verdict)) fiber token =
      requestOf m fiber token :=
  requestOf_modify_view m target fiber token _ (fun _ => ⟨rfl, rfl, rfl⟩)

theorem requestOf_installMiddleware (p : NativeEff) (fuel : Nat) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    requestOf (steppedBy p fuel table m .installMiddleware) fiber token = requestOf m fiber token := rfl

theorem requestOf_answer_zero (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber target : FiberId) (token offered : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    requestOf (steppedBy p 0 table m (.answerAsync target offered answer)) fiber token =
      requestOf m fiber token := rfl

theorem requestOf_evaluate_zero (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber target : FiberId) (token : Nat) :
    requestOf (steppedBy p 0 table m (.evaluate target)) fiber token = requestOf m fiber token := rfl

theorem requestOf_advance_zero (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token millis : Nat) :
    requestOf (steppedBy p 0 table m (.advance millis)) fiber token = requestOf m fiber token := rfl

theorem prepareExternalAnswer_internal_state (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    (prepareExternalAnswer table current answer state).1.timers = state.timers ∧
      (prepareExternalAnswer table current answer state).1.deferreds = state.deferreds := by
  unfold prepareExternalAnswer
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

theorem internalKeys_prepareExternalAnswer (m : NativeMachine) (table : RowTable)
    (current : Option NCode) (answer : Completion Val Err Defect FiberId Ann) :
    internalKeys { m with state := (prepareExternalAnswer table current answer m.state).1 } =
      internalKeys m := by
  simp only [internalKeys, (prepareExternalAnswer_internal_state table current answer m.state).1,
    (prepareExternalAnswer_internal_state table current answer m.state).2]

theorem requestOf_prepareExternalAnswer (m : NativeMachine) (table : RowTable)
    (current : Option NCode) (answer : Completion Val Err Defect FiberId Ann)
    (fiber : FiberId) (token : Nat) :
    requestOf { m with state := (prepareExternalAnswer table current answer m.state).1 } fiber token =
      requestOf m fiber token := rfl

theorem requestsOwned_prepareExternalAnswer {m : NativeMachine} (h : RequestsOwned m)
    (table : RowTable) (current : Option NCode) (answer : Completion Val Err Defect FiberId Ann) :
    RequestsOwned { m with state := (prepareExternalAnswer table current answer m.state).1 } := by
  intro fiber token request hr
  rw [internalKeys_prepareExternalAnswer]
  exact h fiber token request hr

theorem internalKeysBelow_prepareExternalAnswer {m : NativeMachine} (h : InternalKeysBelow m)
    (table : RowTable) (current : Option NCode) (answer : Completion Val Err Defect FiberId Ann) :
    InternalKeysBelow { m with state := (prepareExternalAnswer table current answer m.state).1 } := by
  intro key hk
  rw [internalKeys_prepareExternalAnswer] at hk
  exact h key hk

theorem registerExternal_internal_state (p : NativeEff) (table : RowTable)
    (op : NativeOp) (request : Val) (fiber : FiberId) (token : Nat) (state : Stores) :
    ((interpOf p table).registerAsync (.external op request) fiber token state).1.timers =
        state.timers ∧
      ((interpOf p table).registerAsync (.external op request) fiber token state).1.deferreds =
        state.deferreds := by
  cases op <;> simp only [interpOf]
  all_goals try trivial
  all_goals try exact ⟨rfl, rfl⟩
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact prepareExternalAnswer_internal_state _ _ _ _
      · exact ⟨rfl, rfl⟩

theorem interruptRecord_id (p : NativeEff) (table : RowTable) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (f : NFiber) :
    (interruptRecord (interpOf p table) who extra f).1.id = f.id := by
  cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running <;>
    simp [interruptRecord, FiberCore.interruptible, FiberCore.recordCause, he, hi, hr]

theorem interruptRecord_interrupted (p : NativeEff) (table : RowTable) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (f : NFiber) :
    Interrupted (interruptRecord (interpOf p table) who extra f).1 := by
  cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running <;>
    simp [interruptRecord, Interrupted, RunFiber.interruptPending,
      FiberCore.interruptible, FiberCore.recordCause, FiberCore.deferredInterrupt,
      FiberCore.interruptedCause, FiberCore.setDeferred, FiberCore.answerWith, he, hi, hr]

abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann

theorem requestOf_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target fiber : FiberId) (token : Nat) (rest : List NCmd) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.evaluate target) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simp only [driveStep, hf]
  | some f =>
    simp only [driveStep, hf]
    split
    · rfl
    · change requestOf (m.update { f with running := true, currentOpCount := 0 }) fiber token = _
      have hid := fiber_id_of_lookup hf
      by_cases he : target = fiber
      · subst fiber
        simp only [requestOf, fiber_lookup_update, hf, Option.map_some, ↓reduceIte]
        rfl
      · exact requestOf_update_other _ _ _ _ (by simpa only [hid] using he)

theorem driveStep_resume_wrong_key (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber target : FiberId) (token offered : Nat)
    (request : NativeOp × Val) (answer : NCode) (rest : List NCmd)
    (hr : requestOf m fiber token = some request)
    (hne : target ≠ fiber ∨ offered ≠ token) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token =
      some request := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, hp, _⟩ := requestOf_shape hr
  by_cases he : target = fiber
  · subst target
    have ht : token ≠ offered := Ne.symm (hne.resolve_left (by simp))
    simpa only [driveStep, hf, hp, ht, ↓reduceIte] using hr
  · cases hg : m.fiber? target with
    | none => simpa only [driveStep, hg] using hr
    | some g =>
      cases hpark : g.parked with
      | notParked => simpa only [driveStep, hg, hpark] using hr
      | withGuard t =>
        simp only [driveStep, hg, hpark]
        split
        · change requestOf (m.update _) fiber token = some request
          rw [requestOf_update_other _ _ _ _ (by simpa only [fiber_id_of_lookup hg] using he)]
          exact hr
        · exact hr

theorem timer_fireNext_key {κ : Type} (timers : TimerStore) (target : Nat)
    (answer : κ) (owed : Owed κ) (h : (timers.fireNext target answer).1 = some owed) :
    (owed.waiter, owed.token) ∈ wakeKeys timers.wake := by
  cases hd : TimerStore.dueMin target timers.wake.waiters with
  | none => rw [TimerStore.fireNext_none timers target answer hd] at h; cases h
  | some w =>
    rw [(TimerStore.fireNext_now timers target answer w hd).1] at h
    cases Option.some.inj h
    exact List.mem_append_left _ (List.mem_map.mpr ⟨w, TimerStore.dueMin_mem _ _ _ hd, rfl⟩)

theorem timer_clockStep_key {κ : Type} (timers : TimerStore) (millis : Nat)
    (answer : κ) (owed : Owed κ) (h : (timers.clockStep millis answer).1 = some owed) :
    (owed.waiter, owed.token) ∈ wakeKeys timers.wake := by
  unfold TimerStore.clockStep at h
  cases hf : timers.fireNext (timers.target.getD (timers.now + millis)) answer with
  | mk next state =>
    simp only [hf] at h
    cases next with
    | none => cases h
    | some o =>
      cases Option.some.inj h
      exact timer_fireNext_key timers _ answer owed (by rw [hf])

theorem clock_resume_not_external_key (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (token millis : Nat) (request : NativeOp × Val)
    (owned : RequestsOwned m) (hr : requestOf m fiber token = some request)
    (owed : Owed NCode) (ho : ((interpOf p table).clockStep millis m.state).1 = some owed) :
    owed.waiter ≠ fiber ∨ owed.token ≠ token := by
  have hk : (owed.waiter, owed.token) ∈ wakeKeys m.state.timers.wake := by
    change ((m.state.timers.clockStep millis (Prim.success Val.unit)).1.map
      (Owed.mapCode embed)) = some owed at ho
    obtain ⟨o, he, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact timer_clockStep_key _ millis (Prim.success Val.unit) o he
  by_cases hf : owed.waiter = fiber
  · right
    intro ht
    apply owned fiber token request hr
    simp only [internalKeys, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (by simpa only [hf, ht] using hk))))
  · exact Or.inl hf

theorem internalKeys_update_subset {m : NativeMachine} {f : NFiber}
    (hf : f ∈ m.fibers) (g : NFiber)
    (hobservers : g.observers = f.observers) (hdispatcher : g.dispatcher = f.dispatcher) :
    internalKeys (m.update g) ⊆ internalKeys m := by
  intro key hk
  simp only [internalKeys, RunMachine.update, List.mem_append] at hk ⊢
  rcases hk with (((ht | hc) | hd) | hr) | hfs
  · exact Or.inl (Or.inl (Or.inl (Or.inl ht)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
  · exact Or.inl (Or.inl (Or.inr hd))
  · exact Or.inl (Or.inr hr)
  · right
    obtain ⟨z, hz, hkz⟩ := List.mem_flatMap.mp hfs
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hz
    split at hkz
    · apply List.mem_flatMap.mpr
      exact ⟨f, hf, by simpa only [hobservers, hdispatcher] using hkz⟩
    · exact List.mem_flatMap.mpr ⟨old, hold, hkz⟩

theorem fiber_lookup_update_self {m : NativeMachine} {fiber : FiberId} {f : NFiber}
    (hf : m.fiber? fiber = some f) (g : NFiber) (hid : g.id = fiber) :
    (m.update g).fiber? fiber = some g := by
  rw [fiber_lookup_update, hf]
  simp only [Option.map_some, fiber_id_of_lookup hf, hid, ↓reduceIte]

/-- A local update rule, not an extra premise on the requested reachable-machine law. -/
theorem requestsOwned_update_disjoint_guard {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (token : Nat)
    (hid : g.id = f.id) (hp : g.parked = .withGuard token)
    (hobservers : g.observers = f.observers) (hdispatcher : g.dispatcher = f.dispatcher)
    (hkey : (g.id, token) ∉ internalKeys m) (owned : RequestsOwned m) :
    RequestsOwned (m.update g) := by
  have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
  have hsub := internalKeys_update_subset hmem g hobservers hdispatcher
  intro fiber offered request hr hk
  have oldKey := hsub hk
  by_cases he : g.id = fiber
  · obtain ⟨found, hfound, hpark, _⟩ := requestOf_shape hr
    have hg : (m.update g).fiber? fiber = some g :=
      fiber_lookup_update_self (by simpa only [← hid, he] using hf) g he
    rw [hg] at hfound
    cases Option.some.inj hfound
    have ht : token = offered := Parked.withGuard.inj (hp.symm.trans hpark)
    exact hkey (by simpa only [he, ht] using oldKey)
  · rw [requestOf_update_other _ _ _ _ he] at hr
    exact owned fiber offered request hr oldKey

theorem requestsOwned_update_fresh_guard {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber)
    (hid : g.id = f.id) (hp : g.parked = .withGuard m.nextToken)
    (hobservers : g.observers = f.observers) (hdispatcher : g.dispatcher = f.dispatcher)
    (bounds : InternalKeysBelow m) (owned : RequestsOwned m) :
    RequestsOwned (m.update g) :=
  requestsOwned_update_disjoint_guard hf g m.nextToken hid hp hobservers hdispatcher
    (fresh_key_not_internal bounds g.id) owned

theorem requestsOwned_update_unparked {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber)
    (hid : g.id = f.id) (hp : g.parked = .notParked)
    (hobservers : g.observers = f.observers) (hdispatcher : g.dispatcher = f.dispatcher)
    (owned : RequestsOwned m) : RequestsOwned (m.update g) := by
  have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
  have hsub := internalKeys_update_subset hmem g hobservers hdispatcher
  intro fiber offered request hr hk
  by_cases he : g.id = fiber
  · obtain ⟨found, hfound, hpark, _⟩ := requestOf_shape hr
    have hg : (m.update g).fiber? fiber = some g :=
      fiber_lookup_update_self (by simpa only [← hid, he] using hf) g he
    rw [hg] at hfound
    cases Option.some.inj hfound
    rw [hp] at hpark
    cases hpark
  · rw [requestOf_update_other _ _ _ _ he] at hr
    exact owned fiber offered request hr (hsub hk)

theorem requestsOwned_of_same_keys_and_fibers {m m' : NativeMachine}
    (hk : internalKeys m' = internalKeys m) (hf : m'.fibers = m.fibers)
    (owned : RequestsOwned m) : RequestsOwned m' := by
  intro fiber token request hr
  rw [hk]
  apply owned fiber token request
  simpa only [requestOf, RunMachine.fiber?, hf] using hr

theorem requestsOwned_settle_parked {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (token : Nat)
    (hid : g.id = f.id) (hp : g.parked = .withGuard token)
    (hobservers : g.observers = f.observers) (hdispatcher : g.dispatcher = f.dispatcher)
    (hkey : (g.id, token) ∉ internalKeys m) (owned : RequestsOwned m)
    (yielding : Bool) (rest : List NCmd) :
    RequestsOwned (settle f.id rest ⟨m, g, yielding, .parked, []⟩).1 := by
  simp only [settle]
  split
  · exact requestsOwned_update_unparked hf _ hid rfl hobservers hdispatcher owned
  · exact requestsOwned_update_disjoint_guard hf _ token hid hp hobservers hdispatcher hkey owned

/-- The actual external-registration branch, through `settle`, keeps ownership.
This checks fresh allocation; it does not assert that the other branches do. -/
theorem requestsOwned_external_park (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (rest : List NCmd)
    (op : NativeOp) (request : Val) (signal : Bool) (cancel : Option EffName)
    (hf : m.fiber? f.id = some f)
    (hc : f.frame.current = .async (.external op request) signal cancel)
    (hreg : ((interpOf p table).registerAsync (.external op request) f.id m.nextToken m.state).2 = none)
    (bounds : InternalKeysBelow m) (owned : RequestsOwned m) :
    RequestsOwned (settle f.id rest (evaluateNative p m f yielding table)).1 := by
  let state := ((interpOf p table).registerAsync (.external op request) f.id m.nextToken m.state).1
  let before : NativeMachine :=
    ({ m with state, nextToken := m.nextToken + 1 }).emit [RunEvent.parkedOn f.id m.nextToken]
  have hkeys : internalKeys before = internalKeys m := by
    simp only [before, state, internalKeys, RunMachine.emit,
      (registerExternal_internal_state p table op request f.id m.nextToken m.state).1,
      (registerExternal_internal_state p table op request f.id m.nextToken m.state).2]
  have howned : RequestsOwned before := requestsOwned_of_same_keys_and_fibers hkeys rfl owned
  have hlookup : before.fiber? f.id = some f := hf
  have hkey : (f.id, m.nextToken) ∉ internalKeys before := by
    rw [hkeys]
    exact fresh_key_not_internal bounds f.id
  have hpair : (interpOf p table).registerAsync (.external op request) f.id m.nextToken m.state =
      (state, none) := Prod.ext rfl hreg
  let name := (interpOf p table).cancelName
    (cancel.getD (interpOf p table).abortName) f.id m.nextToken
  let framed : NFiber := if signal || cancel.isSome then
    { f with frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack } }
    else f
  let parked := framed.park ⟨m.nextToken, none, [], [], .void, false⟩
  have heval : evaluateNative p m f yielding table =
      ⟨before, parked, yielding, .parked, []⟩ := by
    cases signal <;> cases cancel <;>
      simp [evaluateNative, hc, evaluatePrim, interpAt, hpair, before, parked, framed, name, RunFiber.park]
  have hid : parked.id = f.id := by
    dsimp only [parked, RunFiber.park, framed]
    split <;> rfl
  have hp : parked.parked = .withGuard m.nextToken := rfl
  have ho : parked.observers = f.observers := by
    dsimp only [parked, RunFiber.park, framed]
    split <;> rfl
  have hd : parked.dispatcher = f.dispatcher := by
    dsimp only [parked, RunFiber.park, framed]
    split <;> rfl
  rw [heval]
  exact requestsOwned_settle_parked hlookup parked m.nextToken hid hp ho hd
    (by simpa only [hid] using hkey) howned yielding rest

/-! Store operations move existing resume keys or register the caller's fresh key. -/

theorem wakeKeys_register_mem {α : Type} (wake : WakeList α) (fiber : FiberId)
    (token : Nat) (payload : α) (key : GuardKey) :
    key ∈ wakeKeys (wake.register fiber token payload) ↔
      key ∈ wakeKeys wake ∨ key = (fiber, token) := by
  simp only [wakeKeys, WakeList.register, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

theorem wakeKeys_cancel_subset {α : Type} (wake : WakeList α) (fiber : FiberId) (token : Nat) :
    wakeKeys (wake.cancel fiber token).1 ⊆ wakeKeys wake := by
  unfold WakeList.cancel
  split
  · intro key hk
    rcases List.mem_append.mp hk with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_left _ (List.mem_map.mpr ⟨w, (List.mem_filter.mp hw).1, rfl⟩)
    · exact List.mem_append_right _ h
  · exact List.Subset.refl _

def deferredKeys (store : DeferredStore) : List GuardKey :=
  store.cells.flatMap (fun c => wakeKeys c.wake) ++ store.due.map (fun o => (o.waiter, o.token))

theorem deferredKeys_cell {store : DeferredStore} {cell : DeferredKey} {c : DeferredCell}
    (hc : store.cellAt cell = some c) : wakeKeys c.wake ⊆ deferredKeys store := by
  intro key hk
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_of_getElem? hc, hk⟩)

theorem deferredKeys_setCell_subset (store : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (extra : List GuardKey)
    (hc : wakeKeys c.wake ⊆ deferredKeys store ++ extra) :
    deferredKeys (store.setCell cell c) ⊆ deferredKeys store ++ extra := by
  intro key hk
  rcases List.mem_append.mp hk with hcells | hdue
  · obtain ⟨found, hfound, hk⟩ := List.mem_flatMap.mp hcells
    rcases List.mem_or_eq_of_mem_set hfound with hold | heq
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨found, hold, hk⟩))
    · exact hc (by simpa only [heq] using hk)
  · exact List.mem_append_left _ (List.mem_append_right _ hdue)

theorem deferredKeys_register_subset (store : DeferredStore) (cell : DeferredKey)
    (fiber : FiberId) (token : Nat) :
    deferredKeys (store.register cell fiber token).1 ⊆ deferredKeys store ++ [(fiber, token)] := by
  unfold DeferredStore.register
  cases hc : store.cellAt cell with
  | none => exact fun _ h => List.mem_append_left _ h
  | some c =>
    simp only
    cases hd : c.completion with
    | some effect => exact fun _ h => List.mem_append_left _ h
    | none =>
      apply deferredKeys_setCell_subset
      intro key hk
      rcases (wakeKeys_register_mem c.wake fiber token () key).mp hk with hold | rfl
      · exact List.mem_append_left _ (deferredKeys_cell hc hold)
      · exact List.mem_append_right _ (List.mem_cons_self ..)

theorem deferredKeys_make (store : DeferredStore) : deferredKeys store.make.2 = deferredKeys store := by
  simp [deferredKeys, DeferredStore.make, wakeKeys, WakeList.empty]

theorem deferredKeys_cancel_subset (store : DeferredStore) (cell : DeferredKey)
    (fiber : FiberId) (token : Nat) :
    deferredKeys (store.cancel cell fiber token) ⊆ deferredKeys store := by
  unfold DeferredStore.cancel
  cases hc : store.cellAt cell with
  | none => exact List.Subset.refl _
  | some c =>
    have hnew : wakeKeys (c.wake.cancel fiber token).1 ⊆ deferredKeys store ++ [] := by
      intro key hk
      simpa only [List.append_nil] using deferredKeys_cell hc (wakeKeys_cancel_subset c.wake fiber token hk)
    simpa only [List.append_nil] using deferredKeys_setCell_subset store cell _ [] hnew

theorem deferredKeys_due_append (store : DeferredStore) (due : List (Owed Effect4.Machine.Program)) :
    deferredKeys { store with due := store.due ++ due } =
      deferredKeys store ++ due.map (fun o => (o.waiter, o.token)) := by
  simp only [deferredKeys, List.map_append, List.append_assoc]

theorem wakeKeys_wakeAll_subset {α : Type} (wake : WakeList α) :
    wakeKeys wake.wakeAll.2 ⊆ wakeKeys wake := by
  intro key hk
  exact List.mem_append_right _ hk

theorem deferredKeys_complete_subset (store : DeferredStore) (cell : DeferredKey)
    (code : Effect4.Machine.Program) :
    deferredKeys (store.complete cell code).1 ⊆ deferredKeys store := by
  unfold DeferredStore.complete
  cases hc : store.cellAt cell with
  | none => exact List.Subset.refl _
  | some c =>
    simp only
    cases hd : c.completion with
    | some previous => exact List.Subset.refl _
    | none =>
      have hnew : wakeKeys c.wake.wakeAll.2 ⊆ deferredKeys store ++ [] := by
        intro key hk
        simpa only [List.append_nil] using deferredKeys_cell hc (wakeKeys_wakeAll_subset c.wake hk)
      have hset : deferredKeys (store.setCell cell ⟨some code, c.wake.wakeAll.2⟩) ⊆
          deferredKeys store := by
        simpa only [List.append_nil] using deferredKeys_setCell_subset store cell _ [] hnew
      intro key hk
      rcases List.mem_append.mp hk with hcells | hdue
      · exact hset (List.mem_append_left _ hcells)
      · rw [List.map_append] at hdue
        rcases List.mem_append.mp hdue with hold | hnew
        · exact List.mem_append_right _ hold
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hnew
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ho
          apply deferredKeys_cell hc
          exact List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

theorem wakeKeys_runBatch_partition {α : Type} (wake : WakeList α) :
    wakeKeys wake = wakeKeys wake.runBatch.2 ++
      wake.runBatch.1.map (fun w => (w.fiber, w.token)) := by
  cases hb : wake.batch <;> simp [wakeKeys, WakeList.runBatch, hb]

theorem deferredKeys_wakeBatch_subset (store : DeferredStore) (cell : DeferredKey) :
    deferredKeys (store.wakeBatch cell) ⊆ deferredKeys store := by
  unfold DeferredStore.wakeBatch
  cases hc : store.cellAt cell with
  | none => exact List.Subset.refl _
  | some c =>
    simp only
    cases hd : c.completion with
    | some effect =>
      have hnew : wakeKeys c.wake.runBatch.2 ⊆ deferredKeys store ++ [] := by
        intro key hk
        apply List.mem_append_left
        apply deferredKeys_cell hc
        rw [wakeKeys_runBatch_partition]
        exact List.mem_append_left _ hk
      have hset : deferredKeys (store.setCell cell ⟨some effect, c.wake.runBatch.2⟩) ⊆
          deferredKeys store := by
        simpa only [List.append_nil] using deferredKeys_setCell_subset store cell _ [] hnew
      intro key hk
      rcases List.mem_append.mp hk with hcells | hdue
      · exact hset (List.mem_append_left _ hcells)
      · rw [List.map_append] at hdue
        rcases List.mem_append.mp hdue with hold | hnew
        · exact List.mem_append_right _ hold
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hnew
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ho
          apply deferredKeys_cell hc
          rw [wakeKeys_runBatch_partition]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    | none =>
      have hw : wakeKeys { c.wake.runBatch.2 with
          waiters := c.wake.runBatch.2.waiters ++ c.wake.runBatch.1 } = wakeKeys c.wake := by
        cases hb : c.wake.batch <;> simp [wakeKeys, WakeList.runBatch, hb]
      have hnew : wakeKeys { c.wake.runBatch.2 with
          waiters := c.wake.runBatch.2.waiters ++ c.wake.runBatch.1 } ⊆ deferredKeys store ++ [] := by
        rw [hw, List.append_nil]
        exact deferredKeys_cell hc
      simpa only [List.append_nil] using deferredKeys_setCell_subset store cell _ [] hnew

theorem deferredKeys_drain_partition (store : DeferredStore) :
    deferredKeys store = deferredKeys store.drainDue.2 ++
      store.drainDue.1.map (fun o => (o.waiter, o.token)) := by
  simp [deferredKeys, DeferredStore.drainDue]

def storeKeys (state : Stores) : List GuardKey :=
  wakeKeys state.timers.wake ++ deferredKeys state.deferreds

theorem storeKeys_mono {before after : Stores}
    (ht : wakeKeys after.timers.wake ⊆ wakeKeys before.timers.wake)
    (hd : deferredKeys after.deferreds ⊆ deferredKeys before.deferreds) :
    storeKeys after ⊆ storeKeys before := by
  intro key hk
  rcases List.mem_append.mp hk with h | h
  · exact List.mem_append_left _ (ht h)
  · exact List.mem_append_right _ (hd h)

/-- Every synchronous store operation transports or removes existing guard keys. -/
theorem syncOpStep_storeKeys {state after : Stores} {op : SyncOp} {value : Val}
    (h : syncOpStep op state = some (after, value)) : storeKeys after ⊆ storeKeys state := by
  cases op <;> unfold syncOpStep at h
  all_goals repeat' (first | dsimp only [Option.map] at h | split at h)
  all_goals cases h
  all_goals apply storeKeys_mono
  all_goals first
    | exact List.Subset.refl _
    | exact deferredKeys_complete_subset _ _ _
    | exact deferredKeys_cancel_subset _ _ _ _
    | exact wakeKeys_cancel_subset _ _ _
    | simp only [deferredKeys_make, List.Subset.refl]

abbrev NTask := Task EffName EffThunk Val Err Defect FiberId Ann
abbrev NBucket := Bucket EffName EffThunk Val Err Defect FiberId Ann

def bucketKeys (buckets : List NBucket) : List GuardKey :=
  buckets.flatMap fun b => b.tasks.flatMap taskKeys

def fiberKeys (fiber : NFiber) : List GuardKey :=
  fiber.observers.flatMap observerKeys ++ bucketKeys fiber.dispatcher.buckets

theorem internalKeys_fiber {m : NativeMachine} {f : NFiber} (hf : f ∈ m.fibers) :
    fiberKeys f ⊆ internalKeys m := by
  intro key hk
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨f, hf, hk⟩)

theorem internalKeys_update_add (m : NativeMachine) (g : NFiber) (extra : List GuardKey)
    (hg : fiberKeys g ⊆ internalKeys m ++ extra) :
    internalKeys (m.update g) ⊆ internalKeys m ++ extra := by
  intro key hk
  simp only [internalKeys, RunMachine.update, List.mem_append] at hk
  rcases hk with hstores | hfs
  · apply List.mem_append_left
    simp only [internalKeys, List.mem_append]
    exact Or.inl hstores
  · obtain ⟨z, hz, hkz⟩ := List.mem_flatMap.mp hfs
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hz
    split at hkz
    · exact hg hkz
    · exact List.mem_append_left _ (internalKeys_fiber hold hkz)

theorem bucketKeys_insert_mem (priority : Nat) (task : NTask) (buckets : List NBucket)
    (key : GuardKey) :
    key ∈ bucketKeys (Dispatcher.insert priority task buckets) ↔
      key ∈ bucketKeys buckets ∨ key ∈ taskKeys task := by
  induction buckets with
  | nil => simp [bucketKeys, Dispatcher.insert]
  | cons bucket rest ih =>
    simp only [Dispatcher.insert]
    split
    · simp [bucketKeys, or_left_comm, or_comm]
    · split
      · simp [bucketKeys, or_comm]
      · have h := or_congr (Iff.rfl (a := key ∈ bucket.tasks.flatMap taskKeys)) ih
        simpa only [bucketKeys, List.flatMap_cons, List.mem_append, or_assoc] using h

theorem internalKeys_postTask_subset (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) :
    internalKeys (m.postTask owner priority task) ⊆ internalKeys m ++ taskKeys task := by
  unfold RunMachine.postTask
  cases ho : m.fiber? owner with
  | none => exact fun _ h => List.mem_append_left _ h
  | some f =>
    change internalKeys (m.update { f with dispatcher := f.dispatcher.enqueue priority task }) ⊆ _
    apply internalKeys_update_add
    intro key hk
    have hm : f ∈ m.fibers := List.mem_of_find?_eq_some ho
    rcases List.mem_append.mp hk with hobs | htasks
    · exact List.mem_append_left _ (internalKeys_fiber hm (List.mem_append_left _ hobs))
    · rcases (bucketKeys_insert_mem priority task f.dispatcher.buckets key).mp htasks with hold | hnew
      · exact List.mem_append_left _ (internalKeys_fiber hm (List.mem_append_right _ hold))
      · exact List.mem_append_right _ hnew

theorem requestOf_update_view {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f)
    (g : NFiber) (hv : RequestView f g) (fiber : FiberId) (token : Nat) :
    requestOf (m.update g) fiber token = requestOf m fiber token := by
  by_cases he : g.id = fiber
  · have hlookup : m.fiber? fiber = some f := by simpa only [hv.1, he] using hf
    simp only [requestOf, fiber_lookup_update_self hlookup g he, hlookup]
    dsimp only [bind, Option.bind]
    rw [← hv.2.1, ← hv.2.2]
  · exact requestOf_update_other _ _ _ _ he

theorem requestOf_postTask (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) (fiber : FiberId) (token : Nat) :
    requestOf (m.postTask owner priority task) fiber token = requestOf m fiber token := by
  unfold RunMachine.postTask
  cases ho : m.fiber? owner with
  | none => rfl
  | some f =>
    change requestOf (m.update { f with dispatcher := f.dispatcher.enqueue priority task }) fiber token = _
    exact requestOf_update_view (f := f) (by simpa only [fiber_id_of_lookup ho] using ho)
      { f with dispatcher := f.dispatcher.enqueue priority task }
      ⟨rfl, rfl, rfl⟩ fiber token

theorem internalKeys_store_decomposition (m : NativeMachine) :
    internalKeys m = storeKeys m.state ++ m.races.map (fun r => (r.host, r.token)) ++
      m.fibers.flatMap fiberKeys := by
  simp only [internalKeys, storeKeys, deferredKeys, List.append_assoc]
  rfl

theorem internalKeys_state_subset (m : NativeMachine) (state : Stores)
    (hstate : storeKeys state ⊆ storeKeys m.state) :
    internalKeys { m with state } ⊆ internalKeys m := by
  intro key hk
  rw [internalKeys_store_decomposition] at hk ⊢
  rcases List.mem_append.mp hk with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (hstate h))
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  · exact List.mem_append_right _ h

theorem requestsOwned_state_subset (m : NativeMachine) (state : Stores)
    (hstate : storeKeys state ⊆ storeKeys m.state) (owned : RequestsOwned m) :
    RequestsOwned { m with state } := by
  intro fiber token request hr hk
  exact owned fiber token request hr (internalKeys_state_subset m state hstate hk)

theorem internalKeysBelow_state_subset (m : NativeMachine) (state : Stores)
    (hstate : storeKeys state ⊆ storeKeys m.state) (bounds : InternalKeysBelow m) :
    InternalKeysBelow { m with state } := by
  intro key hk
  exact bounds key (internalKeys_state_subset m state hstate hk)

theorem wakeList_storeKeys (state : Stores) (key : WakeKey) (phase : WakePhase) :
    storeKeys (state.wakeList key phase) ⊆ storeKeys state := by
  unfold Stores.wakeList
  cases key.kind <;> first
    | exact List.Subset.refl _
    | exact storeKeys_mono (List.Subset.refl _) (deferredKeys_wakeBatch_subset _ _)

def commandKeys : NCmd → List GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | .observe _ _ observer => observerKeys observer
  | _ => []

theorem requestOf_drainOwed (m : NativeMachine) (due : List (Owed NCode))
    (fiber : FiberId) (token : Nat) :
    requestOf (drainOwed m due).1 fiber token = requestOf m fiber token := by
  induction due generalizing m with
  | nil => rfl
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now => simpa only [drainOwed, hm] using ih m
    | scheduled owner priority =>
      simpa only [drainOwed, hm] using (ih _).trans (requestOf_postTask m owner priority
        (.resume owed.waiter owed.token owed.code) fiber token)

theorem drainOwed_commandKeys (m : NativeMachine) (due : List (Owed NCode)) :
    (drainOwed m due).2.flatMap commandKeys ⊆ due.map (fun o => (o.waiter, o.token)) := by
  induction due generalizing m with
  | nil => exact List.Subset.refl _
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now =>
      intro key hk
      simp only [drainOwed, hm, List.flatMap_cons, commandKeys, List.singleton_append,
        List.mem_cons] at hk
      rcases hk with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih m h)
    | scheduled owner priority =>
      simp only [drainOwed, hm]
      exact fun key hk => List.mem_cons_of_mem _ (ih _ hk)

theorem drainOwed_internalKeys (m : NativeMachine) (due : List (Owed NCode)) :
    internalKeys (drainOwed m due).1 ⊆ internalKeys m ++ due.map (fun o => (o.waiter, o.token)) := by
  induction due generalizing m with
  | nil => simpa only [drainOwed, List.map_nil, List.append_nil] using List.Subset.refl (internalKeys m)
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now =>
      intro key hk
      simp only [drainOwed, hm] at hk
      have hr := ih m hk
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    | scheduled owner priority =>
      intro key hk
      simp only [drainOwed, hm] at hk
      have hr := ih (m.postTask owner priority (.resume owed.waiter owed.token owed.code)) hk
      rcases List.mem_append.mp hr with hposted | hrest
      · have hp := internalKeys_postTask_subset m owner priority
          (.resume owed.waiter owed.token owed.code) hposted
        rcases List.mem_append.mp hp with hold | hnew
        · exact List.mem_append_left _ hold
        · exact List.mem_append_right _ ((List.mem_singleton.mp hnew) ▸ List.mem_cons_self ..)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hrest)

theorem dueResumes_keys_iff (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (key : GuardKey) :
    key ∈ internalKeys { m with state := ((interpOf p table).dueResumes m.state).2 } ++
        ((interpOf p table).dueResumes m.state).1.map (fun o => (o.waiter, o.token)) ↔
      key ∈ internalKeys m := by
  have hdue : ((interpOf p table).dueResumes m.state).1.map (fun o => (o.waiter, o.token)) =
      m.state.deferreds.due.map (fun o => (o.waiter, o.token)) := by
    change (m.state.deferreds.due.map (Owed.mapCode embed)).map _ = _
    rw [List.map_map]
    rfl
  rw [hdue]
  change key ∈ internalKeys { m with
    state := { m.state with deferreds := { m.state.deferreds with due := [] } } } ++ _ ↔ _
  simp only [internalKeys, List.map_nil, List.append_nil, List.mem_append]
  constructor
  · rintro (((hs | hr) | hf) | hd)
    · exact Or.inl (Or.inl (Or.inl hs))
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hf
    · exact Or.inl (Or.inl (Or.inr hd))
  · rintro (((hs | hd) | hr) | hf)
    · exact Or.inl (Or.inl (Or.inl hs))
    · exact Or.inr hd
    · exact Or.inl (Or.inl (Or.inr hr))
    · exact Or.inl (Or.inr hf)

theorem requestOf_driveStep_drainDue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (rest : List NCmd) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m .drainDue rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  change requestOf (drainOwed { m with state := ((interpOf p table).dueResumes m.state).2 }
    ((interpOf p table).dueResumes m.state).1).1 fiber token = _
  exact requestOf_drainOwed _ _ fiber token

theorem internalKeys_driveStep_drainDue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (rest : List NCmd) :
    letI := evaluatorFor p table
    internalKeys (driveStep (interpOf p table) m .drainDue rest).1 ⊆ internalKeys m := by
  letI := evaluatorFor p table
  intro key hk
  change key ∈ internalKeys (drainOwed
    { m with state := ((interpOf p table).dueResumes m.state).2 }
    ((interpOf p table).dueResumes m.state).1).1 at hk
  exact (dueResumes_keys_iff p table m key).mp (drainOwed_internalKeys _ _ hk)

theorem commandKeys_driveStep_drainDue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (rest : List NCmd) :
    letI := evaluatorFor p table
    (driveStep (interpOf p table) m .drainDue rest).2.flatMap commandKeys ⊆
      internalKeys m ++ rest.flatMap commandKeys := by
  letI := evaluatorFor p table
  intro key hk
  change key ∈ ((drainOwed { m with state := ((interpOf p table).dueResumes m.state).2 }
    ((interpOf p table).dueResumes m.state).1).2 ++ rest).flatMap commandKeys at hk
  rw [List.flatMap_append] at hk
  rcases List.mem_append.mp hk with hdue | hrest
  · apply List.mem_append_left
    apply (dueResumes_keys_iff p table m key).mp
    exact List.mem_append_right _ (drainOwed_commandKeys _ _ hdue)
  · exact List.mem_append_right _ hrest

theorem requestsOwned_driveStep_drainDue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (rest : List NCmd) (owned : RequestsOwned m) :
    letI := evaluatorFor p table
    RequestsOwned (driveStep (interpOf p table) m .drainDue rest).1 := by
  letI := evaluatorFor p table
  intro fiber token request hr hk
  rw [requestOf_driveStep_drainDue] at hr
  exact owned fiber token request hr (internalKeys_driveStep_drainDue p table m rest hk)

/-! A race registration's return writes the race host, so token separation alone
does not cover that command. The code below records the provenance obligation:
source compilation cannot forge a race-registration reference. The scheduler's
`beginRace` is the site that introduces one, for its own current fiber. -/

def raceSites : NCode → List Nat
  | .suspend (.park (.race race)) => [race]
  | .suspend (.store (.park (.race race))) => [race]
  | .onSuccess body _ => raceSites body
  | .onSuccessConst body next => raceSites body ++ raceSites next
  | .onFailure body _ => raceSites body
  | .onSuccessAndFailure body _ _ => raceSites body
  | .exitFrame body => raceSites body
  | .onExit body _ _ => raceSites body
  | _ => []

theorem raceSites_ofExit (exit : ExitV) : raceSites (Prim.ofExit exit) = [] := by
  cases exit <;> rfl

theorem raceSites_asyncRoute (op : NativeOp) (request : Term) (p : Point) :
    raceSites (asyncRoute op request p) = [] := by
  unfold asyncRoute
  split
  · split <;> rfl
  · repeat' first | split | rfl
  · repeat' first | split | rfl

theorem raceSites_compileEff (e : NativeEff) (p : Point) :
    raceSites (compileEff e p) = [] := by
  cases p
  rename_i path env fuel tape completed root
  cases e <;> cases fuel <;> unfold compileEff <;> dsimp only
  all_goals repeat' first
    | rfl
    | exact raceSites_asyncRoute _ _ _
    | exact raceSites_ofExit _
    | exact raceSites_compileEff _ _
    | split
termination_by sizeOf e
decreasing_by all_goals simp_all <;> decreasing_tactic

theorem raceSites_resolve (root : NativeEff) (p : Point) :
    raceSites (resolve root p) = [] := by
  unfold resolve
  split
  · exact raceSites_compileEff _ _
  · rfl

theorem raceSites_compileLayer (layer : LayerTerm NativeOp) (p : Point)
    (memo : MemoMapId) (scope : Nat) :
    raceSites (compileLayer layer p memo scope) = [] := by
  cases layer <;> simp only [compileLayer]
  all_goals first
    | exact raceSites_compileLayer _ _ _ _
    | rfl
    | (split <;> rfl)
termination_by sizeOf layer

theorem raceSites_resolveLayer (root : NativeEff) (p : Point) (memo : MemoMapId)
    (scope : Nat) : raceSites (resolveLayer root p memo scope) = [] := by
  unfold resolveLayer
  split
  · unfold resolveLayer.resolveLayerTerm
    repeat' first | split | exact raceSites_compileLayer _ _ _ _ | rfl
  · rfl

theorem raceSites_embed_ofExit (exit : ExitV) :
    raceSites (embed (Prim.ofExit exit)) = [] := by
  cases exit <;> rfl

theorem raceSites_finProgram (fin : FinName) (exit : ExitV) :
    raceSites (embed (finProgram fin exit)) = [] := by
  cases fin <;> unfold finProgram
  all_goals repeat' first | rfl | split

theorem raceSites_progOf (program : ProgName) : raceSites (embed (progOf program)) = [] := by
  cases program <;> unfold progOf
  all_goals repeat' first
    | rfl
    | exact raceSites_finProgram _ _
    | exact raceSites_progOf _
    | split
termination_by sizeOf program
decreasing_by all_goals simp_all <;> decreasing_tactic

theorem raceSites_store_contA (name : Name) (value : Val) :
    raceSites (embed (Effect4.Machine.contAOf name value)) = [] := by
  cases name <;> unfold Effect4.Machine.contAOf
  all_goals repeat' first
    | rfl
    | exact raceSites_embed_ofExit _
    | exact raceSites_progOf _
    | split

theorem raceSites_store_contE (name : Name) (cause : CauseV) :
    raceSites (embed (Effect4.Machine.contEOf name cause)) = [] := by
  cases name <;> unfold Effect4.Machine.contEOf
  all_goals first | rfl | exact raceSites_embed_ofExit _

theorem raceSites_completion (answer : Completion Val Err Defect FiberId Ann) :
    raceSites (embed (completionPrim answer)) = [] := by
  cases answer
  · exact raceSites_embed_ofExit _
  · rfl

theorem raceSites_cancelProgram (name : Name) :
    raceSites (embed (cancelProgram name)) = [] := by
  unfold cancelProgram
  repeat' first | rfl | split

theorem raceSites_cancelProgramOf (name : EffName) : raceSites (cancelProgramOf name) = [] := by
  unfold cancelProgramOf
  repeat' first | rfl | exact raceSites_cancelProgram _ | split

theorem raceSites_innerLayerAt (root : NativeEff) (p : Point) (memo : MemoMapId)
    (scope : Nat) : raceSites (innerLayerAt root p memo scope) = [] := by
  unfold innerLayerAt
  repeat' first
    | rfl
    | exact raceSites_resolveLayer _ _ _ _
    | exact raceSites_compileLayer _ _ _ _
    | split

theorem raceSites_regionCode (root : NativeEff) (region : Region) :
    raceSites (regionCode root region) = [] := by
  cases region <;> first
    | exact raceSites_resolve _ _
    | exact raceSites_resolveLayer _ _ _ _

theorem raceSites_contEOf (root : NativeEff) (name : EffName) (cause : CauseV) :
    raceSites (Effect4.Program.contEOf root name cause) = [] := by
  cases name <;> unfold Effect4.Program.contEOf
  all_goals repeat' first
    | rfl
    | exact raceSites_resolve _ _
    | exact raceSites_ofExit _
    | exact raceSites_store_contE _ _
    | split

set_option maxHeartbeats 800000 in
theorem raceSites_contAOf (root : NativeEff) (name : EffName) (value : Val) :
    raceSites (Effect4.Program.contAOf root name value) = [] := by
  cases name <;> unfold Effect4.Program.contAOf
  all_goals try simp only [raceSites, provideLayerWithK, provideLayerBodyK,
    updateThenK, buildWithScopeK, addCurrentMemoMapK, provideThenK, combineWithK,
    mergeContextsK, serviceLookupK, bindServiceK, constructionAt]
  all_goals repeat' first
    | simp only [raceSites, raceSites_resolve, raceSites_resolveLayer,
        raceSites_innerLayerAt, raceSites_regionCode, raceSites_ofExit,
        raceSites_store_contA, raceSites_finProgram]
    | rfl
    | split

theorem raceSites_suspendBodyAt (root : NativeEff) (thunk : EffThunk) :
    raceSites (suspendBodyAt root thunk) = [] := by
  cases thunk <;> unfold suspendBodyAt
  all_goals repeat' first
    | rfl
    | exact raceSites_resolve _ _
    | exact raceSites_compileEff _ _
    | exact raceSites_progOf _
    | split

def stepRaceSites : IterStep EffName EffThunk Val Err Defect FiberId Ann → List Nat
  | .resume next _ => raceSites next
  | _ => []

theorem raceSites_runStmts_yieldOf (root : NativeEff) (p : Point) (e : NativeEff)
    (bind : Bool) (fuel : Nat) (pc : List Nat) (env folded : List Val)
    (ih : ∀ pc env folded, stepRaceSites (runStmts root p fuel pc env folded).2 = []) :
    stepRaceSites (runStmts.yieldOf root p e bind fuel pc env folded).2 = [] := by
  have hc := raceSites_compileEff e
    { p with path := p.path ++ [0] ++ pc ++ [0, 0], env, fuel := fuel + 1 }
  cases bind <;>
    cases hcode : compileEff e
      { p with path := p.path ++ [0] ++ pc ++ [0, 0], env, fuel := fuel + 1 } <;>
    simp only [runStmts.yieldOf, hcode, stepRaceSites]
  all_goals first
    | exact ih _ _ _
    | simpa only [hcode] using hc

theorem raceSites_runStmts (root : NativeEff) (p : Point) (fuel : Nat)
    (pc : List Nat) (env folded : List Val) :
    stepRaceSites (runStmts root p fuel pc env folded).2 = [] := by
  induction fuel generalizing pc env folded with
  | zero => unfold runStmts; rfl
  | succ fuel ih =>
    unfold runStmts
    repeat' first
      | rfl
      | exact ih _ _ _
      | exact raceSites_runStmts_yieldOf root p _ _ fuel _ _ _ ih
      | split

theorem raceSites_closeDone (reasons : List (Reason Err Defect FiberId Ann)) :
    stepRaceSites (embedStep (closeDone reasons)) = [] := by
  cases reasons <;> rfl

theorem raceSites_closeSeqStep (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    stepRaceSites (embedStep (closeSeqStep remaining exit captured value)) = [] := by
  cases remaining
  · exact raceSites_closeDone _
  · exact raceSites_finProgram _ _

theorem raceSites_store_iterNext (name : Name) (value : Val) :
    stepRaceSites (embedStep (stores.iterNext name value).2) = [] := by
  cases name <;> first
    | rfl
    | exact raceSites_closeDone _
    | exact raceSites_closeSeqStep _ _ _ _

/-- The precise native hook premises for the independent frame-step lemma. -/
def HooksNoRace (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  (∀ name value, raceSites (interp.contA name value) = []) ∧
  (∀ name cause, raceSites (interp.contE name cause) = []) ∧
  (∀ thunk, raceSites (interp.suspendBody thunk) = []) ∧
  (∀ name value, raceSites (interp.loopBody name value) = []) ∧
  (∀ name cause, raceSites (interp.cancelThenFail name cause) = []) ∧
  (∀ name value, stepRaceSites (interp.iterNext name value).2 = [])

theorem hooksNoRace_interpOf (root : NativeEff) (table : RowTable) :
    HooksNoRace (interpOf root table).toPrimInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact raceSites_contAOf root
  · exact raceSites_contEOf root
  · exact raceSites_suspendBodyAt root
  · intro name value
    cases name <;> first | rfl | exact raceSites_resolve _ _
  · intro name cause
    exact raceSites_cancelProgramOf name
  · intro name value
    cases name <;> first
      | rfl
      | exact raceSites_runStmts _ _ _ _ _ _
      | exact raceSites_store_iterNext _ _

theorem hooksNoRace_interpAt (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) : HooksNoRace (interpAt root completed table).toPrimInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name value
    exact raceSites_contAOf root _ value
  · intro name cause
    exact raceSites_contEOf root _ cause
  · intro thunk
    exact raceSites_suspendBodyAt root _
  · intro name value
    cases name <;> first | rfl | exact raceSites_resolve _ _
  · intro name cause
    exact raceSites_cancelProgramOf name
  · intro name value
    cases name <;> first
      | rfl
      | exact raceSites_runStmts _ _ _ _ _ _
      | exact raceSites_store_iterNext _ _

def actionRaceSites : NAction → List Nat
  | .fork code _ => raceSites code
  | .forkIn code _ _ => raceSites code
  | .forkScoped code _ => raceSites code
  | .setInterruptible code _ => raceSites code
  | .raceAll codes => codes.flatMap raceSites
  | .closePar codes => codes.flatMap raceSites
  | _ => []

def optionActionRaceSites : Option NAction → List Nat
  | none => []
  | some action => actionRaceSites action

theorem raceSites_actionEntrants (es : Effs NativeOp) (p : Point) :
    (actionAt.entrants es p).flatMap raceSites = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    simp only [actionAt.entrants, List.flatMap_cons, raceSites_compileEff, List.nil_append]
    exact raceSites_actionEntrants _ _
termination_by sizeOf es

theorem raceSites_actionAt (root : NativeEff) (p : Point) :
    optionActionRaceSites (actionAt root p) = [] := by
  unfold actionAt
  repeat' first
    | rfl
    | dsimp only
    | exact raceSites_resolve _ _
    | exact raceSites_actionEntrants _ _
    | split

theorem raceSites_forkScopedAt (root : NativeEff) (p : Point) (scope : Nat) :
    optionActionRaceSites (forkScopedAt root p scope) = [] := by
  unfold forkScopedAt
  split
  · exact raceSites_resolve _ _
  · rfl

theorem raceSites_actionOf (name : ActionName) :
    actionRaceSites (embedAction (actionOf name)) = [] := by
  cases name <;> unfold actionOf
  all_goals first
    | rfl
    | exact raceSites_progOf _
    | skip
  all_goals change (List.map _ _).flatMap raceSites = []
  all_goals rw [List.flatMap_map, List.flatMap_map]
  all_goals apply List.flatMap_eq_nil_iff.mpr
  all_goals intro x hx
  all_goals first | exact raceSites_progOf _ | exact raceSites_finProgram _ _

theorem raceSites_withFiberOf (root : NativeEff) (table : RowTable) (thunk : EffThunk) :
    optionActionRaceSites ((interpOf root table).withFiberOf thunk) = [] := by
  cases thunk <;> simp only [interpOf]
  all_goals repeat' first
    | rfl
    | exact raceSites_actionAt _ _
    | exact raceSites_forkScopedAt _ _ _
    | exact raceSites_actionOf _
    | exact raceSites_resolve _ _
    | exact raceSites_resolveLayer _ _ _ _
    | split

def RaceCodeOwned (m : NativeMachine) (fiber : FiberId) (code : NCode) : Prop :=
  ∀ raceId ∈ raceSites code, ∃ race, m.race? raceId = some race ∧ race.host = fiber

theorem raceCodeOwned_of_no_sites (m : NativeMachine) (fiber : FiberId) (code : NCode)
    (h : raceSites code = []) : RaceCodeOwned m fiber code := by
  intro raceId hr
  rw [h] at hr
  cases hr

theorem raceCodeOwned_compileEff (m : NativeMachine) (fiber : FiberId)
    (e : NativeEff) (p : Point) : RaceCodeOwned m fiber (compileEff e p) :=
  raceCodeOwned_of_no_sites m fiber _ (raceSites_compileEff e p)

theorem raceCodeOwned_park_host (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (code : NCode) (raceId : Nat)
    (owned : RaceCodeOwned m fiber code)
    (hpark : (interpOf p table).parkOf code = some (.ok (.race raceId))) :
    ∃ race, m.race? raceId = some race ∧ race.host = fiber := by
  apply owned raceId
  cases code <;> try (simp [interpOf] at hpark)
  rename_i thunk
  cases thunk <;> try (simp at hpark)
  · rename_i kind
    cases kind <;> simp at hpark
    cases hpark
    exact List.mem_cons_self ..
  · rename_i thunk
    cases thunk <;> try (simp at hpark)
    rename_i kind
    cases kind <;> simp at hpark
    cases hpark
    exact List.mem_cons_self ..

abbrev NRace := Race EffName EffThunk Val Err Defect FiberId Ann

/-- Existing race references retain the same host as bookkeeping changes. -/
def RaceHostsPreserved (m n : NativeMachine) : Prop :=
  ∀ raceId race, m.race? raceId = some race →
    ∃ next, n.race? raceId = some next ∧ next.host = race.host

theorem raceCodeOwned_transport {m n : NativeMachine} (h : RaceHostsPreserved m n)
    {fiber : FiberId} {code : NCode} (owned : RaceCodeOwned m fiber code) :
    RaceCodeOwned n fiber code := by
  intro raceId hr
  obtain ⟨race, hm, hhost⟩ := owned raceId hr
  obtain ⟨next, hn, he⟩ := h raceId race hm
  exact ⟨next, hn, he.trans hhost⟩

theorem raceHostsPreserved_append (m : NativeMachine) (extra : List NRace) :
    RaceHostsPreserved m { m with races := m.races ++ extra } := by
  intro raceId race hm
  refine ⟨race, ?_, rfl⟩
  change m.races.find? (fun r => r.id = raceId) = some race at hm
  simp only [RunMachine.race?, List.find?_append, hm, Option.some_or]

theorem race_id_of_lookup {m : NativeMachine} {raceId : Nat} {race : NRace}
    (h : m.race? raceId = some race) : race.id = raceId :=
  of_decide_eq_true (List.find?_some (p := fun r : NRace => decide (r.id = raceId)) h)

theorem race_lookup_updateRace (m : NativeMachine) (race : NRace) (raceId : Nat) :
    (m.updateRace race).race? raceId =
      (m.race? raceId).map (fun old => if old.id = race.id then race else old) := by
  unfold RunMachine.updateRace RunMachine.race?
  rw [List.find?_map]
  have hp : (fun old : NRace => decide ((if old.id = race.id then race else old).id = raceId)) =
      (fun old : NRace => decide (old.id = raceId)) := by
    funext old
    split <;> simp_all
  rw [show ((fun r : NRace => decide (r.id = raceId)) ∘
      (fun old => if old.id = race.id then race else old)) = _ from hp]

theorem raceHostsPreserved_updateRace {m : NativeMachine} {race : NRace}
    (hr : m.race? race.id = some race) (next : NRace)
    (hid : next.id = race.id) (hhost : next.host = race.host) :
    RaceHostsPreserved m (m.updateRace next) := by
  intro raceId old hold
  by_cases he : old.id = next.id
  · have hlookup : m.race? race.id = some old := by
      simpa only [← hid, ← he, race_id_of_lookup hold] using hold
    have heq : old = race := Option.some.inj (hlookup.symm.trans hr)
    refine ⟨next, ?_, hhost.trans (congrArg Race.host heq.symm)⟩
    simp only [race_lookup_updateRace, hold, Option.map_some, he, ↓reduceIte]
  · refine ⟨old, ?_, rfl⟩
    simp only [race_lookup_updateRace, hold, Option.map_some, he, ↓reduceIte]

def RaceIdsBelow (m : NativeMachine) : Prop :=
  ∀ race ∈ m.races, race.id < m.nextRace

theorem raceIdsBelow_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    RaceIdsBelow (Api.load p compileFuel choices answers) := by
  intro race hr
  cases hr

theorem race_lookup_fresh {m : NativeMachine} (bounds : RaceIdsBelow m) :
    m.race? m.nextRace = none := by
  apply List.find?_eq_none.mpr
  intro race hr h
  exact (Nat.ne_of_lt (bounds race hr)) (of_decide_eq_true h)

theorem raceCodeOwned_beginRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (entrants : List NCode)
    (bounds : RaceIdsBelow m) :
    RaceCodeOwned (beginRace (interpOf p table) m f yielding entrants).machine f.id
      (beginRace (interpOf p table) m f yielding entrants).fiber.frame.current := by
  intro raceId hr
  change raceId ∈ [m.nextRace] at hr
  have hid := List.mem_singleton.mp hr
  subst raceId
  let race : NRace := ⟨m.nextRace, f.id, m.nextToken,
    { Supervision.RaceAllState.initial [] with remaining := entrants.length }, false, entrants, false⟩
  refine ⟨race, ?_, rfl⟩
  change (m.races ++ [race]).find? (fun r => r.id = m.nextRace) = some race
  have hf : m.races.find? (fun r => r.id = m.nextRace) = none := race_lookup_fresh bounds
  simp only [List.find?_append, hf, Option.none_or, List.find?_cons,
    show decide (race.id = m.nextRace) = true from decide_eq_true rfl]

/-! The global interface separates saved-state facts, the current command queue,
and resume keys still held by an outer dispatcher snapshot. None is a new public
premise: the pending obligation is to establish them from `Reachable`. -/

def RequestsBelow (m : NativeMachine) : Prop :=
  ∀ fiber token request, requestOf m fiber token = some request → token < m.nextToken

def PendingShape (f : NFiber) : Prop :=
  match f.parked with
  | .notParked => f.pending = []
  | .withGuard token => ∃ pending, f.pending = [pending] ∧ pending.token = token

def FrameCodeOwned (m : NativeMachine) (f : NFiber) : Prop :=
  RaceCodeOwned m f.id f.frame.current ∧
    ∀ code ∈ f.frame.stack, RaceCodeOwned m f.id code

def taskRaceSites : NTask → List Nat
  | .resume _ _ code => raceSites code
  | _ => []

def InternalCodeNoRace (m : NativeMachine) : Prop :=
  (∀ cell ∈ m.state.deferreds.cells, ∀ code ∈ cell.completion, raceSites (embed code) = []) ∧
  (∀ owed ∈ m.state.deferreds.due, raceSites (embed owed.code) = []) ∧
  (∀ f ∈ m.fibers, ∀ bucket ∈ f.dispatcher.buckets,
    ∀ task ∈ bucket.tasks, taskRaceSites task = []) ∧
  (∀ race ∈ m.races, ∀ code ∈ race.programs, raceSites code = [])

structure GuardState (m : NativeMachine) : Prop where
  fiberIds : (m.fibers.map RunFiber.id).Nodup
  fibersBelow : ∀ f ∈ m.fibers, f.id.value < m.nextId
  raceIds : (m.races.map Race.id).Nodup
  racesBelow : RaceIdsBelow m
  raceHosts : ∀ race ∈ m.races, ∃ f, m.fiber? race.host = some f
  keysBelow : InternalKeysBelow m
  requestsBelow : RequestsBelow m
  requestsOwned : RequestsOwned m
  pendingShape : ∀ f ∈ m.fibers, PendingShape f
  parkedIdle : ∀ f ∈ m.fibers, f.parked ≠ .notParked → f.running = false
  parkedBelow : ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → token < m.nextToken
  exited : ∀ f ∈ m.fibers, f.exit.isSome = true → f.parked = .notParked ∧ f.running = false
  deferredCause : ∀ f ∈ m.fibers, f.frame.deferredInterrupt = true →
    f.frame.interruptedCause.isSome = true
  frameCodes : ∀ f ∈ m.fibers, FrameCodeOwned m f
  internalCodes : InternalCodeNoRace m

/-- Keys already removed from a dispatcher are still reserved while its snapshot runs. -/
structure ReservedKeys (m : NativeMachine) (keys : List GuardKey) : Prop where
  below : ∀ key ∈ keys, key.2 < m.nextToken
  disjoint : ∀ fiber token request, requestOf m fiber token = some request → (fiber, token) ∉ keys

def ActiveAt (m : NativeMachine) (fiber : FiberId) : Prop :=
  ∃ f, m.fiber? fiber = some f ∧ f.running = true ∧ f.parked = .notParked

def commandOwner (m : NativeMachine) : NCmd → Option FiberId
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => some fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => some fiber
  | .registrationDone raceId _ => (m.race? raceId).map Race.host
  | _ => none

def CommandAuthority (p : NativeEff) (table : RowTable) (m : NativeMachine) : NCmd → Prop
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => ActiveAt m fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => ActiveAt m fiber
  | .registrationDone raceId _ =>
    ∃ race f, m.race? raceId = some race ∧ m.fiber? race.host = some f ∧
      f.running = true ∧ f.parked = .notParked ∧
      (interpOf p table).parkOf f.frame.current = some (.ok (.race raceId))
  | .launch raceId | .enrollRace raceId _ =>
    ∃ race, m.race? raceId = some race ∧ ActiveAt m race.host
  | .exitDone fiber => ∃ f, m.fiber? fiber = some f ∧ f.exit.isSome = true
  | _ => True

def commandRaceSites : NCmd → List Nat
  | .resume _ _ code => raceSites code
  | .afterInterrupt _ _ (.race raceId) => [raceId]
  | _ => []

structure GuardQueue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (commands : List NCmd) : Prop where
  authority : ∀ command ∈ commands, CommandAuthority p table m command
  owners : (commands.filterMap (commandOwner m)).Nodup
  keys : ReservedKeys m (commands.flatMap commandKeys)
  codeSites : ∀ command ∈ commands, commandRaceSites command = []

theorem reservedKeys_nil (m : NativeMachine) : ReservedKeys m [] := by
  constructor
  · intro key h; cases h
  · intro fiber token request hr h; cases h

theorem reservedKeys_internal (m : NativeMachine) (state : GuardState m) :
    ReservedKeys m (internalKeys m) := ⟨state.keysBelow, state.requestsOwned⟩

theorem guardQueue_nil (p : NativeEff) (table : RowTable) (m : NativeMachine) :
    GuardQueue p table m [] := by
  refine ⟨?_, List.nodup_nil, reservedKeys_nil m, ?_⟩
  · intro command h; cases h
  · intro command h; cases h

theorem requestsBelow_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    RequestsBelow (Api.load p compileFuel choices answers) := by
  intro fiber token request h
  rw [requestOf_load] at h
  cases h

theorem guardState_load (p : NativeEff) (compileFuel : Nat) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    GuardState (Api.load p compileFuel choices answers) := by
  constructor
  · change ([⟨0⟩] : List FiberId).Nodup
    simp
  · intro f hf
    have he := List.mem_singleton.mp hf
    subst f
    exact Nat.zero_lt_succ _
  · exact List.nodup_nil
  · exact raceIdsBelow_load p compileFuel choices answers
  · intro race hr; cases hr
  · exact internalKeysBelow_load p compileFuel choices answers
  · exact requestsBelow_load p compileFuel choices answers
  · exact requestsOwned_load p compileFuel choices answers
  · intro f hf
    have he := List.mem_singleton.mp hf
    subst f
    rfl
  · intro f hf hp
    have he := List.mem_singleton.mp hf
    subst f
    exact False.elim (hp rfl)
  · intro f hf token hp
    have he := List.mem_singleton.mp hf
    subst f
    cases hp
  · intro f hf he
    have heq := List.mem_singleton.mp hf
    subst f
    cases he
  · intro f hf he
    have heq := List.mem_singleton.mp hf
    subst f
    cases he
  · intro f hf
    have he := List.mem_singleton.mp hf
    subst f
    refine ⟨raceCodeOwned_compileEff _ _ _ _, ?_⟩
    intro code hc
    cases hc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro cell hc; cases hc
    · intro owed ho; cases ho
    · intro f hf bucket hb
      have he := List.mem_singleton.mp hf
      subst f
      cases hb
    · intro race hr; cases hr

theorem update_all (m : NativeMachine) (g : NFiber) (P : NFiber → Prop)
    (hold : ∀ f ∈ m.fibers, P f) (hg : P g) : ∀ f ∈ (m.update g).fibers, P f := by
  intro f hf
  obtain ⟨old, hm, he⟩ := List.mem_map.mp hf
  subst f
  split
  · exact hg
  · exact hold old hm

theorem fiberIds_update (m : NativeMachine) (g : NFiber) :
    (m.update g).fibers.map RunFiber.id = m.fibers.map RunFiber.id := by
  simp only [RunMachine.update, List.map_map]
  congr 1
  funext old
  dsimp only [Function.comp_def]
  split <;> simp_all

theorem guardState_setRunning {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f)
    (hp : f.parked = .notParked) (hexit : f.exit.isSome = false) (count : Nat) :
    GuardState (m.update { f with running := true, currentOpCount := count }) := by
  let g : NFiber := { f with running := true, currentOpCount := count }
  have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
  have hkeys := internalKeys_update_subset hmem g rfl rfl
  have hrequests := requestOf_update_view hf g ⟨rfl, rfl, rfl⟩
  constructor
  · rw [fiberIds_update]
    exact state.fiberIds
  · exact update_all m g _ state.fibersBelow (state.fibersBelow f hmem)
  · exact state.raceIds
  · exact state.racesBelow
  · intro race hr
    obtain ⟨old, hold⟩ := state.raceHosts race hr
    refine ⟨if old.id = g.id then g else old, ?_⟩
    simp only [fiber_lookup_update, hold, Option.map_some]
    rfl
  · intro key hk
    exact state.keysBelow key (hkeys hk)
  · intro fiber token request hr
    exact state.requestsBelow fiber token request ((hrequests fiber token) ▸ hr)
  · intro fiber token request hr hk
    exact state.requestsOwned fiber token request ((hrequests fiber token) ▸ hr) (hkeys hk)
  · exact update_all m g _ state.pendingShape (state.pendingShape f hmem)
  · apply update_all m g _ state.parkedIdle
    intro h
    exact False.elim (h hp)
  · exact update_all m g _ state.parkedBelow (state.parkedBelow f hmem)
  · apply update_all m g _ state.exited
    intro h
    have : false = true := hexit.symm.trans h
    cases this
  · exact update_all m g _ state.deferredCause (state.deferredCause f hmem)
  · exact update_all m g _ state.frameCodes (state.frameCodes f hmem)
  · refine ⟨state.internalCodes.1, state.internalCodes.2.1, ?_, state.internalCodes.2.2.2⟩
    exact update_all m g _ state.internalCodes.2.2.1 (state.internalCodes.2.2.1 f hmem)

theorem guardState_emit {m : NativeMachine} (state : GuardState m) (events) :
    GuardState (m.emit events) := by
  rcases state
  constructor <;> assumption

theorem guardState_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.evaluate target) rest).1 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using state
  | some f =>
    simp only [driveStep, hf]
    split
    · exact state
    · rename_i h
      have hg : f.exit.isSome = false ∧ f.running = false ∧ f.parked = .notParked := by
        simpa only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, not_or, Bool.not_eq_true,
          Decidable.not_not, and_assoc] using h
      exact guardState_emit (guardState_setRunning state
        (by simpa only [fiber_id_of_lookup hf] using hf) hg.2.2 hg.1 0) _

theorem reservedKeys_of_same_requests {m n : NativeMachine} {keys : List GuardKey}
    (old : ReservedKeys m keys) (hnext : m.nextToken ≤ n.nextToken)
    (hreq : ∀ fiber token, requestOf n fiber token = requestOf m fiber token) :
    ReservedKeys n keys := by
  refine ⟨fun key hk => Nat.lt_of_lt_of_le (old.below key hk) hnext, ?_⟩
  intro fiber token request hr
  exact old.disjoint fiber token request ((hreq fiber token) ▸ hr)

theorem reservedKeys_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.evaluate target) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · cases hf : m.fiber? target with
    | none => simp only [driveStep, hf, Nat.le_refl]
    | some f =>
      simp only [driveStep, hf]
      split <;> exact Nat.le_refl _
  · intro fiber token
    exact requestOf_driveStep_evaluate p table m target fiber token rest

theorem commandAuthority_owner_active (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (fiber : FiberId)
    (authority : CommandAuthority p table m command) (owner : commandOwner m command = some fiber) :
    ActiveAt m fiber := by
  cases command <;> simp only [commandOwner, Option.some.injEq] at owner
  all_goals try contradiction
  all_goals try (subst fiber; exact authority)
  obtain ⟨race, f, hr, hf, hrun, hpark, _⟩ := authority
  simp only [hr, Option.map_some, Option.some.injEq] at owner
  exact ⟨f, by simpa only [← owner] using hf, hrun, hpark⟩

def ControlsPreserved (m n : NativeMachine) : Prop :=
  ∀ fiber f, m.fiber? fiber = some f →
    (f.parked = .notParked ∨ f.exit.isSome = true) → ∃ g, n.fiber? fiber = some g ∧
    g.frame.current = f.frame.current ∧ g.parked = f.parked ∧ g.exit = f.exit ∧
    (f.running = true → g.running = true)

theorem controlsPreserved_setRunning {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (count : Nat) :
    ControlsPreserved m (m.update { f with running := true, currentOpCount := count }) := by
  intro fiber old hold _
  let g : NFiber := { f with running := true, currentOpCount := count }
  by_cases he : old.id = f.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [← he, fiber_id_of_lookup hold] using hold
    have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
    subst old
    refine ⟨g, ?_, rfl, rfl, rfl, fun _ => rfl⟩
    simp only [fiber_lookup_update, hold, Option.map_some, ↓reduceIte]
    rfl
  · refine ⟨old, ?_, rfl, rfl, rfl, fun h => h⟩
    simp only [fiber_lookup_update, hold, Option.map_some, he, ↓reduceIte]

theorem activeAt_transport {m n : NativeMachine} (controls : ControlsPreserved m n)
    {fiber : FiberId} (active : ActiveAt m fiber) : ActiveAt n fiber := by
  obtain ⟨f, hf, hrun, hpark⟩ := active
  obtain ⟨g, hg, _, hpark', _, hrun'⟩ := controls fiber f hf (Or.inl hpark)
  exact ⟨g, hg, hrun' hrun, hpark'.trans hpark⟩

theorem commandAuthority_transport (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} (controls : ControlsPreserved m n)
    (races : RaceHostsPreserved m n) (command : NCmd)
    (authority : CommandAuthority p table m command) : CommandAuthority p table n command := by
  cases command <;> try (exact True.intro)
  all_goals try (exact activeAt_transport controls authority)
  case launch raceId =>
    obtain ⟨race, hr, ha⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    exact ⟨next, hn, he ▸ activeAt_transport controls ha⟩
  case enrollRace raceId child =>
    obtain ⟨race, hr, ha⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    exact ⟨next, hn, he ▸ activeAt_transport controls ha⟩
  case registrationDone raceId yielding =>
    obtain ⟨race, f, hr, hf, hrun, hpark, hcode⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    obtain ⟨g, hg, hcurrent, hpark', _, hrun'⟩ := controls race.host f hf (Or.inl hpark)
    exact ⟨next, g, hn, he ▸ hg, hrun' hrun, hpark'.trans hpark, hcurrent ▸ hcode⟩
  case exitDone fiber =>
    obtain ⟨f, hf, he⟩ := authority
    obtain ⟨g, hg, _, _, hexit, _⟩ := controls fiber f hf (Or.inr he)
    exact ⟨g, hg, hexit ▸ he⟩

theorem commandOwner_transport (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} (races : RaceHostsPreserved m n) (command : NCmd)
    (authority : CommandAuthority p table m command) :
    commandOwner n command = commandOwner m command := by
  cases command <;> try rfl
  obtain ⟨race, f, hr, _⟩ := authority
  obtain ⟨next, hn, he⟩ := races _ race hr
  simp only [commandOwner, hr, hn, Option.map_some, he]

theorem reservedKeys_of_requests_subset {m n : NativeMachine} {keys : List GuardKey}
    (old : ReservedKeys m keys) (hnext : m.nextToken ≤ n.nextToken)
    (requests : ∀ fiber token request, requestOf n fiber token = some request →
      requestOf m fiber token = some request) : ReservedKeys n keys := by
  refine ⟨fun key hk => Nat.lt_of_lt_of_le (old.below key hk) hnext, ?_⟩
  intro fiber token request hr
  exact old.disjoint fiber token request (requests fiber token request hr)

theorem guardQueue_transport (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {commands : List NCmd}
    (queue : GuardQueue p table m commands) (controls : ControlsPreserved m n)
    (races : RaceHostsPreserved m n) (next : m.nextToken ≤ n.nextToken)
    (requests : ∀ fiber token request, requestOf n fiber token = some request →
      requestOf m fiber token = some request) :
    GuardQueue p table n commands := by
  refine ⟨fun c hc => commandAuthority_transport p table controls races c (queue.authority c hc),
    ?_, reservedKeys_of_requests_subset queue.keys next requests, queue.codeSites⟩
  have he : commands.filterMap (commandOwner n) = commands.filterMap (commandOwner m) := by
    have aux : ∀ cs : List NCmd,
        (∀ c ∈ cs, commandOwner n c = commandOwner m c) →
        cs.filterMap (commandOwner n) = cs.filterMap (commandOwner m) := by
      intro cs
      induction cs with
      | nil => intro _; rfl
      | cons c cs ih =>
        intro h
        simp only [List.filterMap_cons, h c (List.mem_cons_self ..),
          ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    exact aux commands (fun c hc => commandOwner_transport p table races c (queue.authority c hc))
  rw [he]
  exact queue.owners

theorem guardQueue_tail (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {command : NCmd} {rest : List NCmd}
    (queue : GuardQueue p table m (command :: rest)) : GuardQueue p table m rest := by
  refine ⟨fun c hc => queue.authority c (List.mem_cons_of_mem _ hc), ?_, ?_,
    fun c hc => queue.codeSites c (List.mem_cons_of_mem _ hc)⟩
  · have h := queue.owners
    cases he : commandOwner m command <;> simp only [List.filterMap_cons, he] at h
    · exact h
    · exact (List.nodup_cons.mp h).2
  · constructor
    · intro k hk
      exact queue.keys.below k (List.mem_append_right _ hk)
    · intro fiber token request hr hk
      exact queue.keys.disjoint fiber token request hr (List.mem_append_right _ hk)

theorem guardQueue_cons_loop (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (fiber : FiberId) (yielding : Bool)
    (queue : GuardQueue p table m rest) (active : ActiveAt m fiber)
    (fresh : fiber ∉ rest.filterMap (commandOwner m)) :
    GuardQueue p table m (.loop fiber yielding :: rest) := by
  refine ⟨?_, ?_, queue.keys, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with he | hm
    · subst c; exact active
    · exact queue.authority c hm
  · exact List.nodup_cons.mpr ⟨fresh, queue.owners⟩
  · intro c hc
    rcases List.mem_cons.mp hc with he | hm
    · subst c; rfl
    · exact queue.codeSites c hm

theorem guardQueue_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (queue : GuardQueue p table m (.evaluate target :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.evaluate target) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    simp only [driveStep, hf]
    split
    · exact tail
    · rename_i h
      have hg : f.exit.isSome = false ∧ f.running = false ∧ f.parked = .notParked := by
        simpa only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, not_or,
          Decidable.not_not, and_assoc] using h
      let g : NFiber := { f with running := true, currentOpCount := 0 }
      let n := (m.update g).emit [RunEvent.started target]
      have hf' : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
      have controls : ControlsPreserved m n := controlsPreserved_setRunning hf' 0
      have races : RaceHostsPreserved m n := fun _ race hr => ⟨race, hr, rfl⟩
      have after : GuardQueue p table n rest := guardQueue_transport p table tail controls races
        (Nat.le_refl _) (fun fiber token _ hr =>
          (requestOf_update_view hf' g ⟨rfl, rfl, rfl⟩ fiber token) ▸ hr)
      apply guardQueue_cons_loop p table target false after
      · refine ⟨g, ?_, rfl, hg.2.2⟩
        exact fiber_lookup_update_self hf g (by change f.id = target; exact fiber_id_of_lookup hf)
      · intro hm
        obtain ⟨c, hc, howner⟩ := List.mem_filterMap.mp hm
        rw [commandOwner_transport p table races c (tail.authority c hc)] at howner
        obtain ⟨old, hold, hrun, _⟩ :=
          commandAuthority_owner_active p table m c target (tail.authority c hc) howner
        have heq : old = f := Option.some.inj (hold.symm.trans hf)
        have : false = true := hg.2.1.symm.trans (heq ▸ hrun)
        cases this

structure FiberGuardState (m : NativeMachine) (f : NFiber) : Prop where
  below : f.id.value < m.nextId
  pending : PendingShape f
  idle : f.parked ≠ .notParked → f.running = false
  parkedBelow : ∀ token, f.parked = .withGuard token → token < m.nextToken
  exited : f.exit.isSome = true → f.parked = .notParked ∧ f.running = false
  deferredCause : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true
  codes : FrameCodeOwned m f
  tasks : ∀ bucket ∈ f.dispatcher.buckets, ∀ task ∈ bucket.tasks, taskRaceSites task = []

theorem guardState_fiber {m : NativeMachine} (state : GuardState m)
    {f : NFiber} (hf : f ∈ m.fibers) : FiberGuardState m f :=
  ⟨state.fibersBelow f hf, state.pendingShape f hf, state.parkedIdle f hf,
    state.parkedBelow f hf, state.exited f hf, state.deferredCause f hf,
    state.frameCodes f hf, state.internalCodes.2.2.1 f hf⟩

/-- A fiber replacement accounts for its new internal keys and its possible external guard. -/
theorem guardState_update {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (g : NFiber) (hid : g.id = f.id)
    (valid : FiberGuardState m g) (reserved : ReservedKeys m (fiberKeys g))
    (guardSafe : ∀ token request, g.parked = .withGuard token →
      externalRequest g.frame.current = some request →
      (g.id, token) ∉ internalKeys m ∧ (g.id, token) ∉ fiberKeys g) :
    GuardState (m.update g) := by
  have hkeys := internalKeys_update_add m g (fiberKeys g) (List.subset_append_right _ _)
  have hparked := update_all m g _ state.parkedBelow valid.parkedBelow
  constructor
  · rw [fiberIds_update]; exact state.fiberIds
  · exact update_all m g _ state.fibersBelow valid.below
  · exact state.raceIds
  · exact state.racesBelow
  · intro race hr
    obtain ⟨old, hold⟩ := state.raceHosts race hr
    refine ⟨if old.id = g.id then g else old, ?_⟩
    simp only [fiber_lookup_update, hold, Option.map_some]
  · intro key hk
    rcases List.mem_append.mp (hkeys hk) with h | h
    · exact state.keysBelow key h
    · exact reserved.below key h
  · intro fiber token request hr
    obtain ⟨found, hfound, hpark, _⟩ := requestOf_shape hr
    exact hparked found (List.mem_of_find?_eq_some hfound) token hpark
  · intro fiber token request hr hk
    rcases List.mem_append.mp (hkeys hk) with hk | hk
    all_goals
      by_cases he : g.id = fiber
      · obtain ⟨found, hfound, hpark, hrequest⟩ := requestOf_shape hr
        have hlookup : (m.update g).fiber? fiber = some g :=
          fiber_lookup_update_self (by simpa only [← hid, he] using hf) g he
        rw [hlookup] at hfound
        cases Option.some.inj hfound
        have safe := guardSafe token request hpark hrequest
        first
        | exact safe.1 (by simpa only [he] using hk)
        | exact safe.2 (by simpa only [he] using hk)
      · rw [requestOf_update_other _ _ _ _ he] at hr
        first
        | exact state.requestsOwned fiber token request hr hk
        | exact reserved.disjoint fiber token request hr hk
  · exact update_all m g _ state.pendingShape valid.pending
  · exact update_all m g _ state.parkedIdle valid.idle
  · exact hparked
  · exact update_all m g _ state.exited valid.exited
  · exact update_all m g _ state.deferredCause valid.deferredCause
  · exact update_all m g _ state.frameCodes valid.codes
  · refine ⟨state.internalCodes.1, state.internalCodes.2.1, ?_, state.internalCodes.2.2.2⟩
    exact update_all m g _ state.internalCodes.2.2.1 valid.tasks

theorem reservedKeys_fiber {m : NativeMachine} (state : GuardState m)
    {f : NFiber} (hf : f ∈ m.fibers) : ReservedKeys m (fiberKeys f) := by
  constructor
  · intro key hk; exact state.keysBelow key (internalKeys_fiber hf hk)
  · intro fiber token request hr hk
    exact state.requestsOwned fiber token request hr (internalKeys_fiber hf hk)

theorem guardState_update_unparked {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f) (g : NFiber)
    (hid : g.id = f.id) (valid : FiberGuardState m g)
    (reserved : ReservedKeys m (fiberKeys g)) (hpark : g.parked = .notParked) :
    GuardState (m.update g) := by
  apply guardState_update state hf g hid valid reserved
  intro token request hp _
  rw [hpark] at hp
  cases hp

theorem requestOf_update_unparked_subset (m : NativeMachine) (g : NFiber)
    (hpark : g.parked = .notParked) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hr : requestOf (m.update g) fiber token = some request) :
    requestOf m fiber token = some request := by
  by_cases he : g.id = fiber
  · obtain ⟨f, hf, hp, _⟩ := requestOf_shape hr
    rw [fiber_lookup_update] at hf
    cases hold : m.fiber? fiber with
    | none => simp only [hold, Option.map_none] at hf; cases hf
    | some old =>
      simp only [hold, Option.map_some, fiber_id_of_lookup hold, he, ↓reduceIte,
        Option.some.injEq] at hf
      subst f
      rw [hpark] at hp
      cases hp
  · exact (requestOf_update_other m g fiber token he) ▸ hr

theorem controlsPreserved_update_parked {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (hid : g.id = f.id)
    (hpark : f.parked ≠ .notParked) (hexit : f.exit.isSome = false) :
    ControlsPreserved m (m.update g) := by
  intro fiber old hold eligible
  by_cases he : old.id = g.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [← hid, ← he, fiber_id_of_lookup hold] using hold
    have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
    subst old
    rcases eligible with hp | hx
    · exact False.elim (hpark hp)
    · rw [hexit] at hx; cases hx
  · refine ⟨old, ?_, rfl, rfl, rfl, fun h => h⟩
    simp only [fiber_lookup_update, hold, Option.map_some, he, ↓reduceIte]

theorem guardQueue_cons_evaluate (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (fiber : FiberId)
    (queue : GuardQueue p table m rest) : GuardQueue p table m (.evaluate fiber :: rest) := by
  refine ⟨?_, queue.owners, queue.keys, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with he | hm
    · subst c; trivial
    · exact queue.authority c hm
  · intro c hc
    rcases List.mem_cons.mp hc with he | hm
    · subst c; rfl
    · exact queue.codeSites c hm

theorem guardState_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode)
    (rest : List NCmd) (state : GuardState m) (answerSites : raceSites answer = []) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.resume target token answer) rest).1 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using state
  | some f =>
    cases hp : f.parked with
    | notParked => simpa only [driveStep, hf, hp] using state
    | withGuard parkedToken =>
      simp only [driveStep, hf, hp]
      split
      · rename_i he
        subst parkedToken
        have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
        have old := guardState_fiber state hmem
        have hrun : f.running = false := old.idle (by rw [hp]; intro h; cases h)
        have hshape := old.pending
        simp only [PendingShape, hp] at hshape
        obtain ⟨pending, hpend, ht⟩ := hshape
        let g : NFiber := { f with
          parked := .notParked
          pending := f.pending.filter (fun p => p.token ≠ token)
          frame := { f.frame with current := answer } }
        have valid : FiberGuardState m g := by
          refine ⟨old.below, ?_, ?_, ?_, ?_, old.deferredCause, ?_, old.tasks⟩
          · change f.pending.filter (fun p => p.token ≠ token) = []
            simp only [hpend, List.filter_cons, ht, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ↓reduceIte, List.filter_nil]
          · intro h; exact False.elim (h rfl)
          · intro offered h; cases h
          · intro _; exact ⟨rfl, hrun⟩
          · exact ⟨raceCodeOwned_of_no_sites m f.id answer answerSites, old.codes.2⟩
        exact guardState_emit (guardState_update_unparked (f := f) state
          (by simpa only [fiber_id_of_lookup hf] using hf) g rfl valid
          (reservedKeys_fiber (f := f) state hmem) rfl) _
      · exact state

theorem guardQueue_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode)
    (rest : List NCmd) (state : GuardState m)
    (queue : GuardQueue p table m (.resume target token answer :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.resume target token answer) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    cases hp : f.parked with
    | notParked => simpa only [driveStep, hf, hp] using tail
    | withGuard parkedToken =>
      simp only [driveStep, hf, hp]
      split
      · rename_i he
        subst parkedToken
        have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
        have hexit : f.exit.isSome = false := by
          cases hx : f.exit.isSome with
          | false => rfl
          | true =>
            have hn := (state.exited f hmem hx).1
            rw [hp] at hn; cases hn
        let g : NFiber := { f with
          parked := .notParked
          pending := f.pending.filter (fun p => p.token ≠ token)
          frame := { f.frame with current := answer } }
        let n := (m.update g).emit [RunEvent.resumedWith target token answer]
        have controls : ControlsPreserved m n := controlsPreserved_update_parked (f := f)
          (by simpa only [fiber_id_of_lookup hf] using hf) g rfl
          (by rw [hp]; intro h; cases h) hexit
        have races : RaceHostsPreserved m n := fun _ race hr => ⟨race, hr, rfl⟩
        exact guardQueue_cons_evaluate p table target (guardQueue_transport p table tail
          controls races (Nat.le_refl _) (requestOf_update_unparked_subset m g rfl))
      · exact tail

theorem reservedKeys_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode)
    (rest : List NCmd) (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.resume target token answer) rest).1 keys := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using reserved
  | some f =>
    cases hp : f.parked with
    | notParked => simpa only [driveStep, hf, hp] using reserved
    | withGuard parkedToken =>
      simp only [driveStep, hf, hp]
      split
      · refine reservedKeys_of_requests_subset reserved ?_ ?_
        · exact Nat.le_refl _
        · exact requestOf_update_unparked_subset m _ rfl
      · exact reserved

/-- Deferred completions are native store programs with no scheduler race sites. -/
def StoredCodeNoRace (code : Effect4.Machine.Program) : Prop := raceSites (embed code) = []

def DeferredCodes (d : DeferredStore) : Prop :=
  (∀ cell ∈ d.cells, ∀ code, cell.completion = some code → StoredCodeNoRace code) ∧
    ∀ owed ∈ d.due, StoredCodeNoRace owed.code

theorem deferredCodes_cellAt {d : DeferredStore} (hd : DeferredCodes d) {cell : DeferredKey}
    {c : DeferredCell} (h : d.cellAt cell = some c) :
    ∀ p, c.completion = some p → StoredCodeNoRace p :=
  hd.1 c (List.mem_of_getElem? h)

theorem deferredCodes_make {d : DeferredStore} (hd : DeferredCodes d) : DeferredCodes (d.make).2 := by
  refine ⟨fun cell hc p hp => ?_, hd.2⟩
  simp only [DeferredStore.make, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hd.1 cell hc p hp
  · cases hp

theorem deferredCodes_setCell {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    {c : DeferredCell} (hc : ∀ p, c.completion = some p → StoredCodeNoRace p) :
    DeferredCodes (d.setCell cell c) := by
  refine ⟨fun cell' hc' p hp => ?_, hd.2⟩
  rcases List.mem_or_eq_of_mem_set hc' with hm | rfl
  · exact hd.1 cell' hm p hp
  · exact hc p hp

theorem deferredCodes_register {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    (waiter : FiberId) (token : Nat) :
    DeferredCodes (d.register cell waiter token).1 ∧
      ∀ p, (d.register cell waiter token).2 = some p → StoredCodeNoRace p := by
  unfold DeferredStore.register
  cases hc : d.cellAt cell with
  | none => exact ⟨hd, fun p hp => by cases hp⟩
  | some c =>
    dsimp only
    cases hcomp : c.completion with
    | some effect =>
      dsimp only
      exact ⟨hd, fun p hp => by rw [← Option.some.inj hp]; exact deferredCodes_cellAt hd hc _ hcomp⟩
    | none =>
      dsimp only
      refine ⟨deferredCodes_setCell hd cell (fun p hp => ?_), fun p hp => by cases hp⟩
      simp only at hp
      cases hp

theorem deferredCodes_cancel {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    (waiter : FiberId) (token : Nat) : DeferredCodes (d.cancel cell waiter token) := by
  unfold DeferredStore.cancel
  cases hc : d.cellAt cell with
  | none => exact hd
  | some c =>
    dsimp only
    exact deferredCodes_setCell hd cell (fun p hp => deferredCodes_cellAt hd hc p hp)

theorem deferredCodes_complete {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    {effect : Effect4.Machine.Program} (he : StoredCodeNoRace effect) :
    DeferredCodes (d.complete cell effect).1 := by
  unfold DeferredStore.complete
  cases hc : d.cellAt cell with
  | none => exact hd
  | some c =>
    dsimp only
    cases hcomp : c.completion with
    | some _ => exact hd
    | none =>
      dsimp only
      refine ⟨fun cell' hc' p hp => ?_, fun e he' => ?_⟩
      · simp only [DeferredStore.setCell] at hc'
        rcases List.mem_or_eq_of_mem_set hc' with hm | rfl
        · exact hd.1 cell' hm p hp
        · rw [← Option.some.inj hp]; exact he
      · simp only [List.mem_append, List.mem_map] at he'
        rcases he' with hm | ⟨w, _, rfl⟩
        · exact hd.2 e hm
        · exact he

/-- A batch wake on a Deferred's list owes its batch the stored completion, which is shaped. -/
theorem deferredCodes_wakeBatch {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey) :
    DeferredCodes (d.wakeBatch cell) := by
  unfold DeferredStore.wakeBatch
  cases hc : d.cellAt cell with
  | none => exact hd
  | some c =>
    dsimp only
    have hcm : c ∈ d.cells := List.mem_of_getElem? hc
    cases hcomp : c.completion with
    | some e =>
      dsimp only
      have he : StoredCodeNoRace e := hd.1 c hcm e hcomp
      refine ⟨fun cell' hc' p hp => ?_, fun x hx => ?_⟩
      · simp only [DeferredStore.setCell] at hc'
        rcases List.mem_or_eq_of_mem_set hc' with hm | rfl
        · exact hd.1 cell' hm p hp
        · simp only at hp; exact (Option.some.inj hp) ▸ he
      · simp only [List.mem_append, List.mem_map] at hx
        rcases hx with hm | ⟨w, _, rfl⟩
        · exact hd.2 x hm
        · exact he
    | none =>
      dsimp only
      refine ⟨fun cell' hc' p hp => ?_, hd.2⟩
      simp only [DeferredStore.setCell] at hc'
      rcases List.mem_or_eq_of_mem_set hc' with hm | rfl
      · exact hd.1 cell' hm p hp
      · simp only at hp; exact nomatch hp

theorem deferredCodes_wakeList {s : Stores} (codes : DeferredCodes s.deferreds)
    (key : WakeKey) (phase : WakePhase) : DeferredCodes (s.wakeList key phase).deferreds := by
  unfold Stores.wakeList
  split
  · exact deferredCodes_wakeBatch codes _
  · exact codes

theorem deferredCodes_drainDue {d : DeferredStore} (codes : DeferredCodes d) :
    DeferredCodes d.drainDue.2 ∧ ∀ owed ∈ d.drainDue.1, StoredCodeNoRace owed.code :=
  ⟨⟨codes.1, fun _ h => by cases h⟩, codes.2⟩

theorem syncOpStep_deferredCodes {state after : Stores} {op : SyncOp} {value : Val}
    (codes : DeferredCodes state.deferreds) (h : syncOpStep op state = some (after, value)) :
    DeferredCodes after.deferreds := by
  cases op <;> unfold syncOpStep at h
  all_goals repeat' (first | dsimp only [Option.map] at h | split at h)
  all_goals cases h
  all_goals first
    | exact codes
    | exact deferredCodes_make codes
    | exact deferredCodes_cancel codes _ _ _
    | apply deferredCodes_complete codes
  all_goals first
    | exact raceSites_completion _
    | exact raceSites_embed_ofExit _

theorem guardState_withState {m : NativeMachine} (state : GuardState m) (stores : Stores)
    (keys : storeKeys stores ⊆ storeKeys m.state) (codes : DeferredCodes stores.deferreds) :
    GuardState { m with state := stores } := by
  constructor
  · exact state.fiberIds
  · exact state.fibersBelow
  · exact state.raceIds
  · exact state.racesBelow
  · exact state.raceHosts
  · exact internalKeysBelow_state_subset m stores keys state.keysBelow
  · exact state.requestsBelow
  · exact requestsOwned_state_subset m stores keys state.requestsOwned
  · exact state.pendingShape
  · exact state.parkedIdle
  · exact state.parkedBelow
  · exact state.exited
  · exact state.deferredCause
  · exact state.frameCodes
  · exact ⟨codes.1, codes.2, state.internalCodes.2.2⟩

theorem guardState_driveStep_wake (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (key : WakeKey) (phase : WakePhase) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.wake key phase) rest).1 := by
  exact guardState_withState state _ (wakeList_storeKeys m.state key phase)
    (deferredCodes_wakeList ⟨state.internalCodes.1, state.internalCodes.2.1⟩ key phase)

theorem guardQueue_driveStep_wake (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (key : WakeKey) (phase : WakePhase) (rest : List NCmd)
    (queue : GuardQueue p table m (.wake key phase :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.wake key phase) rest
    GuardQueue p table result.1 result.2 := by
  rcases guardQueue_tail p table queue with ⟨ha, ho, ⟨hb, hd⟩, hc⟩
  exact ⟨ha, ho, ⟨hb, hd⟩, hc⟩

theorem reservedKeys_driveStep_wake (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (key : WakeKey) (phase : WakePhase) (rest : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.wake key phase) rest).1 keys := by
  rcases reserved
  constructor <;> assumption

theorem requestOf_of_shape {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} {f : NFiber} (hf : m.fiber? fiber = some f)
    (hpark : f.parked = .withGuard token)
    (hrequest : externalRequest f.frame.current = some request) :
    requestOf m fiber token = some request := by
  cases hc : f.frame.current <;> simp_all [externalRequest, requestOf, guard]
  rename_i register signal cancel
  cases register <;> simp_all

theorem guardState_update_view {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f) (g : NFiber)
    (valid : FiberGuardState m g) (view : RequestView f g) (keys : fiberKeys g = fiberKeys f) :
    GuardState (m.update g) := by
  have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
  apply guardState_update (f := f) state hf g view.1.symm valid
  · rw [keys]; exact reservedKeys_fiber state hmem
  · intro token request hp hr
    have oldRequest : requestOf m f.id token = some request :=
      requestOf_of_shape hf (view.2.1.trans hp) (view.2.2 ▸ hr)
    have hsafe := state.requestsOwned f.id token request oldRequest
    refine ⟨view.1 ▸ hsafe, ?_⟩
    intro hk
    rw [keys] at hk
    exact hsafe (view.1 ▸ internalKeys_fiber hmem hk)

theorem reservedKeys_subset {m : NativeMachine} {keys more : List GuardKey}
    (reserved : ReservedKeys m more) (subset : keys ⊆ more) : ReservedKeys m keys :=
  ⟨fun key hk => reserved.below key (subset hk),
    fun fiber token request hr hk => reserved.disjoint fiber token request hr (subset hk)⟩

theorem guardQueue_replaceHead (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {command : NCmd} {rest : List NCmd}
    (queue : GuardQueue p table m (command :: rest)) (front : List NCmd)
    (authority : ∀ c ∈ front, CommandAuthority p table m c)
    (owners : front.filterMap (commandOwner m) = (commandOwner m command).toList)
    (keys : front.flatMap commandKeys ⊆ commandKeys command)
    (sites : ∀ c ∈ front, commandRaceSites c = []) :
    GuardQueue p table m (front ++ rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hf | hr
    · exact authority c hf
    · exact queue.authority c (List.mem_cons_of_mem _ hr)
  · have h := queue.owners
    rw [List.filterMap_append, owners]
    cases he : commandOwner m command <;>
      simpa only [List.filterMap_cons, he, Option.toList_none, Option.toList_some,
        List.nil_append, List.cons_append] using h
  · apply reservedKeys_subset queue.keys
    intro key hk
    rw [List.flatMap_append] at hk
    rcases List.mem_append.mp hk with hf | hr
    · exact List.mem_append_left _ (keys hf)
    · exact List.mem_append_right _ hr
  · intro c hc
    rcases List.mem_append.mp hc with hf | hr
    · exact sites c hf
    · exact queue.codeSites c (List.mem_cons_of_mem _ hr)

theorem guardState_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).1 := by
  letI := evaluatorFor p table
  cases remaining <;> simp only [driveStep]
  · exact state
  · split
    · exact state
    · split <;> exact state

theorem guardQueue_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd)
    (queue : GuardQueue p table m (.raceCancel raceId host yielding remaining visited :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have active : ActiveAt m host := queue.authority _ (List.mem_cons_self ..)
  cases remaining <;> simp only [driveStep]
  · apply guardQueue_replaceHead p table queue [.afterInterrupt host yielding (.awaitAll visited)]
    · intro c hc; rcases List.mem_singleton.mp hc with rfl; exact active
    · rfl
    · exact List.Subset.refl _
    · intro c hc; rcases List.mem_singleton.mp hc with rfl; rfl
  · rename_i target more
    split
    · apply guardQueue_replaceHead p table queue [.afterInterrupt host yielding (.awaitAll visited)]
      · intro c hc; rcases List.mem_singleton.mp hc with rfl; exact active
      · rfl
      · exact List.Subset.refl _
      · intro c hc; rcases List.mem_singleton.mp hc with rfl; rfl
    · split
      · apply guardQueue_replaceHead p table queue
          [.interruptTarget target (some host) ((interpOf p table).stackAnnotations host),
            .raceCancel raceId host yielding more (visited ++ [target])]
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · trivial
          · exact active
        · rfl
        · exact List.Subset.refl _
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> rfl
      · apply guardQueue_replaceHead p table queue [.raceCancel raceId host yielding more visited]
        · intro c hc; rcases List.mem_singleton.mp hc with rfl; exact active
        · rfl
        · exact List.Subset.refl _
        · intro c hc; rcases List.mem_singleton.mp hc with rfl; rfl

theorem reservedKeys_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).1 keys := by
  letI := evaluatorFor p table
  cases remaining <;> simp only [driveStep]
  · exact reserved
  · split
    · exact reserved
    · split <;> exact reserved

theorem reservedKeys_append {m : NativeMachine} {left right : List GuardKey}
    (hl : ReservedKeys m left) (hr : ReservedKeys m right) : ReservedKeys m (left ++ right) := by
  constructor
  · intro key hk
    rcases List.mem_append.mp hk with h | h
    · exact hl.below key h
    · exact hr.below key h
  · intro fiber token request hreq hk
    rcases List.mem_append.mp hk with h | h
    · exact hl.disjoint fiber token request hreq h
    · exact hr.disjoint fiber token request hreq h

theorem guardState_update_preserved_request {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f) (g : NFiber)
    (valid : FiberGuardState m g) (view : RequestView f g)
    (reserved : ReservedKeys m (fiberKeys g)) : GuardState (m.update g) := by
  apply guardState_update (f := f) state hf g view.1.symm valid reserved
  intro token request hp hr
  have oldRequest : requestOf m f.id token = some request :=
    requestOf_of_shape hf (view.2.1.trans hp) (view.2.2 ▸ hr)
  exact ⟨view.1 ▸ state.requestsOwned f.id token request oldRequest,
    view.1 ▸ reserved.disjoint f.id token request oldRequest⟩

theorem guardState_arm {m : NativeMachine} (state : GuardState m) (owner : FiberId) :
    GuardState (m.arm owner) := by
  rcases state
  constructor <;> assumption

theorem guardState_halt {m : NativeMachine} (state : GuardState m) (why : Stuck) :
    GuardState (m.halt why) := by
  rcases state
  constructor <;> assumption

theorem dispatcher_insert_tasks (priority : Nat) (task : NTask) (buckets : List NBucket)
    (candidate : NTask) :
    candidate ∈ (Dispatcher.insert priority task buckets).flatMap Bucket.tasks ↔
      candidate ∈ buckets.flatMap Bucket.tasks ∨ candidate = task := by
  induction buckets with
  | nil => simp [Dispatcher.insert]
  | cons bucket rest ih =>
    simp only [Dispatcher.insert]
    split
    · simp [or_left_comm, or_comm]
    · split
      · simp [or_comm]
      · have h := or_congr (Iff.rfl (a := candidate ∈ bucket.tasks)) ih
        simpa only [List.flatMap_cons, List.mem_append, or_assoc] using h

theorem guardState_postTask {m : NativeMachine} (state : GuardState m)
    (owner : FiberId) (priority : Nat) (task : NTask)
    (reserved : ReservedKeys m (taskKeys task)) (sites : taskRaceSites task = []) :
    GuardState (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  cases ho : m.fiber? owner with
  | none => exact guardState_halt state _
  | some f =>
    have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some ho
    have old := guardState_fiber state hmem
    let g : NFiber := { f with dispatcher := f.dispatcher.enqueue priority task }
    have valid : FiberGuardState m g := by
      refine ⟨old.below, old.pending, old.idle, old.parkedBelow, old.exited,
        old.deferredCause, old.codes, ?_⟩
      intro bucket hb candidate hc
      have hm := List.mem_flatMap.mpr ⟨bucket, hb, hc⟩
      rcases (dispatcher_insert_tasks priority task f.dispatcher.buckets candidate).mp hm with hm | he
      · obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hm
        exact old.tasks b hb candidate hc
      · exact he ▸ sites
    have newKeys : ReservedKeys m (fiberKeys g) := by
      apply reservedKeys_subset (reservedKeys_append (reservedKeys_internal m state) reserved)
      intro key hk
      rcases List.mem_append.mp hk with hobs | htasks
      · exact List.mem_append_left _ (internalKeys_fiber hmem (List.mem_append_left _ hobs))
      · rcases (bucketKeys_insert_mem priority task f.dispatcher.buckets key).mp htasks with hold | hnew
        · exact List.mem_append_left _ (internalKeys_fiber hmem (List.mem_append_right _ hold))
        · exact List.mem_append_right _ hnew
    exact guardState_emit (guardState_arm (guardState_update_preserved_request (f := f) state
      (by simpa only [fiber_id_of_lookup ho] using ho) g valid ⟨rfl, rfl, rfl⟩ newKeys) owner) _

theorem controlsPreserved_update_fields {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (view : RequestView f g)
    (exit : g.exit = f.exit) (running : f.running = true → g.running = true) :
    ControlsPreserved m (m.update g) := by
  intro fiber old hold _
  by_cases he : old.id = g.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [view.1, ← he, fiber_id_of_lookup hold] using hold
    have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
    subst old
    refine ⟨g, ?_, view.2.2.symm, view.2.1.symm, exit, running⟩
    simp only [fiber_lookup_update, hold, Option.map_some, he, ↓reduceIte]
  · refine ⟨old, ?_, rfl, rfl, rfl, fun h => h⟩
    simp only [fiber_lookup_update, hold, Option.map_some, he, ↓reduceIte]

theorem controlsPreserved_postTask (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) : ControlsPreserved m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  cases ho : m.fiber? owner with
  | none => exact fun _ f hf _ => ⟨f, hf, rfl, rfl, rfl, fun h => h⟩
  | some f =>
    exact controlsPreserved_update_fields (f := f)
      (by simpa only [fiber_id_of_lookup ho] using ho)
      { f with dispatcher := f.dispatcher.enqueue priority task }
      ⟨rfl, rfl, rfl⟩ rfl (fun h => h)

theorem nextToken_postTask (m : NativeMachine) (owner : FiberId) (priority : Nat) (task : NTask) :
    (m.postTask owner priority task).nextToken = m.nextToken := by
  unfold RunMachine.postTask
  split <;> rfl

theorem raceHostsPreserved_postTask (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) : RaceHostsPreserved m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split <;> exact fun _ race hr => ⟨race, hr, rfl⟩

theorem reservedKeys_postTask {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (owner : FiberId) (priority : Nat) (task : NTask) :
    ReservedKeys (m.postTask owner priority task) keys := by
  refine reservedKeys_of_same_requests reserved ?_ (requestOf_postTask m owner priority task)
  rw [nextToken_postTask]
  exact Nat.le_refl _

theorem guardQueue_postTask (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {commands : List NCmd} (queue : GuardQueue p table m commands)
    (owner : FiberId) (priority : Nat) (task : NTask) :
    GuardQueue p table (m.postTask owner priority task) commands := by
  apply guardQueue_transport p table queue (controlsPreserved_postTask m owner priority task)
    (raceHostsPreserved_postTask m owner priority task)
  · rw [nextToken_postTask]
    exact Nat.le_refl _
  · intro fiber token request hr
    exact (requestOf_postTask m owner priority task fiber token) ▸ hr

theorem nextToken_drainOwed (m : NativeMachine) (due : List (Owed NCode)) :
    (drainOwed m due).1.nextToken = m.nextToken := by
  induction due generalizing m with
  | nil => rfl
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now => simpa only [drainOwed, hm] using ih m
    | scheduled owner priority =>
      simpa only [drainOwed, hm] using
        (ih _).trans (nextToken_postTask m owner priority (.resume owed.waiter owed.token owed.code))

theorem reservedKeys_drainOwed {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (due : List (Owed NCode)) :
    ReservedKeys (drainOwed m due).1 keys := by
  refine reservedKeys_of_same_requests reserved ?_ (requestOf_drainOwed m due)
  rw [nextToken_drainOwed]
  exact Nat.le_refl _

theorem guardState_drainOwed {m : NativeMachine} (state : GuardState m)
    (due : List (Owed NCode))
    (reserved : ReservedKeys m (due.map fun d => (d.waiter, d.token)))
    (sites : ∀ d ∈ due, raceSites d.code = []) : GuardState (drainOwed m due).1 := by
  induction due generalizing m with
  | nil => exact state
  | cons owed rest ih =>
    have tail : ReservedKeys m (rest.map fun d => (d.waiter, d.token)) :=
      reservedKeys_subset reserved (fun _ h => List.mem_cons_of_mem _ h)
    have tailSites := fun d hd => sites d (List.mem_cons_of_mem _ hd)
    cases hm : owed.mode with
    | now => simpa only [drainOwed, hm] using ih state tail tailSites
    | scheduled owner priority =>
      have head : ReservedKeys m (taskKeys (.resume owed.waiter owed.token owed.code)) := by
        apply reservedKeys_subset reserved
        intro key hk
        have he := List.mem_singleton.mp hk
        exact he ▸ List.mem_cons_self ..
      have posted := guardState_postTask state owner priority
        (.resume owed.waiter owed.token owed.code) head (sites owed (List.mem_cons_self ..))
      simpa only [drainOwed, hm] using ih posted
        (reservedKeys_postTask tail owner priority (.resume owed.waiter owed.token owed.code)) tailSites

theorem guardQueue_drainOwed_rest (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (due : List (Owed NCode)) : GuardQueue p table (drainOwed m due).1 commands := by
  induction due generalizing m with
  | nil => exact queue
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now => simpa only [drainOwed, hm] using ih queue
    | scheduled owner priority =>
      simpa only [drainOwed, hm] using ih
        (guardQueue_postTask p table queue owner priority (.resume owed.waiter owed.token owed.code))

theorem drainOwed_commands (m : NativeMachine) (due : List (Owed NCode)) :
    ∀ command ∈ (drainOwed m due).2,
      ∃ owed ∈ due, command = .resume owed.waiter owed.token owed.code := by
  induction due generalizing m with
  | nil => intro command hc; cases hc
  | cons owed rest ih =>
    cases hm : owed.mode with
    | now =>
      intro command hc
      simp only [drainOwed, hm, List.mem_cons] at hc
      rcases hc with he | hc
      · exact ⟨owed, List.mem_cons_self .., he⟩
      · obtain ⟨d, hd, he⟩ := ih m command hc
        exact ⟨d, List.mem_cons_of_mem _ hd, he⟩
    | scheduled owner priority =>
      intro command hc
      simp only [drainOwed, hm] at hc
      obtain ⟨d, hd, he⟩ := ih _ command hc
      exact ⟨d, List.mem_cons_of_mem _ hd, he⟩

theorem guardQueue_drainOwed (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (due : List (Owed NCode))
    (reserved : ReservedKeys m (due.map fun d => (d.waiter, d.token)))
    (sites : ∀ d ∈ due, raceSites d.code = []) :
    GuardQueue p table (drainOwed m due).1 (drainOwed m due).2 := by
  constructor
  · intro command hc
    obtain ⟨owed, _, rfl⟩ := drainOwed_commands m due command hc
    trivial
  · have hnone : (drainOwed m due).2.filterMap (commandOwner (drainOwed m due).1) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro command hc
      obtain ⟨owed, _, rfl⟩ := drainOwed_commands m due command hc
      rfl
    rw [hnone]
    exact List.nodup_nil
  · exact reservedKeys_subset (reservedKeys_drainOwed reserved due) (drainOwed_commandKeys m due)
  · intro command hc
    obtain ⟨owed, hd, rfl⟩ := drainOwed_commands m due command hc
    exact sites owed hd

theorem guardQueue_append_noOwners (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {front rest : List NCmd}
    (left : GuardQueue p table m front) (right : GuardQueue p table m rest)
    (owners : front.filterMap (commandOwner m) = []) :
    GuardQueue p table m (front ++ rest) := by
  constructor
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact left.authority c h
    · exact right.authority c h
  · simpa only [List.filterMap_append, owners, List.nil_append] using right.owners
  · simpa only [List.flatMap_append] using reservedKeys_append left.keys right.keys
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact left.codeSites c h
    · exact right.codeSites c h

theorem guardState_dueResumes (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (state : GuardState m) :
    GuardState { m with state := ((interpOf p table).dueResumes m.state).2 } := by
  apply guardState_withState state
  · refine storeKeys_mono ?_ ?_
    · exact List.Subset.refl _
    · intro key hk
      rw [deferredKeys_drain_partition m.state.deferreds]
      exact List.mem_append_left _ hk
  · exact (deferredCodes_drainDue ⟨state.internalCodes.1, state.internalCodes.2.1⟩).1

theorem reservedKeys_dueResumes (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (state : GuardState m) :
    ReservedKeys { m with state := ((interpOf p table).dueResumes m.state).2 }
      (((interpOf p table).dueResumes m.state).1.map fun d => (d.waiter, d.token)) := by
  constructor
  · intro key hk
    exact state.keysBelow key ((dueResumes_keys_iff p table m key).mp (List.mem_append_right _ hk))
  · intro fiber token request hr hk
    exact state.requestsOwned fiber token request hr
      ((dueResumes_keys_iff p table m (fiber, token)).mp (List.mem_append_right _ hk))

theorem codeSites_dueResumes (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (state : GuardState m) : ∀ owed ∈ ((interpOf p table).dueResumes m.state).1,
      raceSites owed.code = [] := by
  intro owed ho
  change owed ∈ m.state.deferreds.due.map (Owed.mapCode embed) at ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
  exact state.internalCodes.2.1 d hd

theorem guardState_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m .drainDue rest).1 := by
  exact guardState_drainOwed (guardState_dueResumes p table m state) _
    (reservedKeys_dueResumes p table m state) (codeSites_dueResumes p table m state)

theorem guardQueue_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (state : GuardState m)
    (queue : GuardQueue p table m (.drainDue :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m .drainDue rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  let before : NativeMachine := { m with state := ((interpOf p table).dueResumes m.state).2 }
  let due := ((interpOf p table).dueResumes m.state).1
  have tail : GuardQueue p table before rest := by
    rcases guardQueue_tail p table queue with ⟨ha, ho, ⟨hb, hd⟩, hc⟩
    exact ⟨ha, ho, ⟨hb, hd⟩, hc⟩
  apply guardQueue_append_noOwners p table
    (guardQueue_drainOwed p table before due (reservedKeys_dueResumes p table m state)
      (codeSites_dueResumes p table m state))
    (guardQueue_drainOwed_rest p table tail due)
  apply List.filterMap_eq_nil_iff.mpr
  intro command hc
  obtain ⟨owed, _, rfl⟩ := drainOwed_commands before due command hc
  rfl

theorem reservedKeys_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m .drainDue rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_drainOwed
  rcases reserved with ⟨hb, hd⟩
  exact ⟨hb, hd⟩

theorem fiberGuardState_interruptRecord (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (old : FiberGuardState m f)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    FiberGuardState m (interruptRecord (interpOf p table) who extra f).1 := by
  cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running
  all_goals simp only [interruptRecord, FiberCore.interruptible, FiberCore.recordCause,
    FiberCore.interruptedCause, FiberCore.setDeferred, FiberCore.answerWith,
    he, hi, hr, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact old | skip
  all_goals refine ⟨old.below, ?_, ?_, ?_, ?_, ?_, ?_, old.tasks⟩
  all_goals first
    | exact old.pending
    | simpa only [hr] using old.idle
    | exact old.parkedBelow
    | simpa only [he, hr] using old.exited
    | exact old.deferredCause
    | exact old.codes
    | rfl
    | solve | intro h; exact False.elim (h rfl)
    | solve | intro token h; cases h
    | solve | intro h; simp only [Option.isSome_none] at h; cases h
    | solve | intro _; rfl
    | exact ⟨raceCodeOwned_of_no_sites m f.id _ rfl, old.codes.2⟩

theorem guardState_interruptRecord (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    GuardState (m.update (interruptRecord (interpOf p table) who extra f).1) := by
  have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
  have valid := fiberGuardState_interruptRecord p table (guardState_fiber state hmem) who extra
  cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running
  all_goals simp only [interruptRecord, FiberCore.interruptible, FiberCore.recordCause,
    FiberCore.interruptedCause, FiberCore.setDeferred, FiberCore.answerWith,
    he, hi, hr, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] at valid ⊢
  all_goals first
    | exact guardState_update_view (f := f) state hf _ valid ⟨rfl, rfl, rfl⟩ rfl
    | exact guardState_update_unparked (f := f) state hf _ rfl valid
        (reservedKeys_fiber (f := f) state hmem) rfl

theorem requestOf_interruptRecord_subset (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f)
    (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hrequest : requestOf (m.update (interruptRecord (interpOf p table) who extra f).1)
      fiber token = some request) : requestOf m fiber token = some request := by
  let g := (interruptRecord (interpOf p table) who extra f).1
  by_cases hpark : g.parked = .notParked
  · exact requestOf_update_unparked_subset m g hpark fiber token request hrequest
  · have view : RequestView f g := by
      cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running <;>
        simp [g, interruptRecord, RequestView, FiberCore.interruptible, FiberCore.recordCause,
          FiberCore.setDeferred, FiberCore.answerWith, he, hi, hr] at hpark ⊢
    exact (requestOf_update_view (f := f) hf g view fiber token) ▸ hrequest

theorem guardState_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.interruptTarget target who extra) rest).1 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using state
  | some f =>
    simp only [driveStep, hf]
    exact guardState_emit (guardState_interruptRecord p table (f := f) state
      (by simpa only [fiber_id_of_lookup hf] using hf) who extra) _

theorem reservedKeys_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.interruptTarget target who extra) rest).1 keys := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using reserved
  | some f =>
    simp only [driveStep, hf]
    refine reservedKeys_of_requests_subset reserved ?_ ?_
    · exact Nat.le_refl _
    · exact requestOf_interruptRecord_subset p table (f := f)
        (by simpa only [fiber_id_of_lookup hf] using hf) who extra

theorem requestOrInterrupted_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hrequest : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    let after := (driveStep (interpOf p table) m (.interruptTarget target who extra) rest).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => exact Or.inl (by simpa only [driveStep, hf] using hrequest)
  | some f =>
    simp only [driveStep, hf]
    let g := (interruptRecord (interpOf p table) who extra f).1
    have hid : g.id = target := (interruptRecord_id p table who extra f).trans (fiber_id_of_lookup hf)
    by_cases he : target = fiber
    · right
      refine ⟨g, ?_, interruptRecord_interrupted p table who extra f⟩
      exact he ▸ fiber_lookup_update_self hf g hid
    · left
      exact (requestOf_update_other m g fiber token (fun h => he (hid.symm.trans h))) ▸ hrequest

/-- The fields actually read by command authority, restricted to active or exited fibers. -/
structure CommandControlsPreserved (m n : NativeMachine) : Prop where
  active : ∀ fiber f, m.fiber? fiber = some f → f.running = true → f.parked = .notParked →
    ∃ g, n.fiber? fiber = some g ∧ g.running = true ∧ g.parked = .notParked ∧
      g.frame.current = f.frame.current
  exited : ∀ fiber f, m.fiber? fiber = some f → f.exit.isSome = true →
    ∃ g, n.fiber? fiber = some g ∧ g.exit.isSome = true

theorem commandControls_activeAt {m n : NativeMachine} (controls : CommandControlsPreserved m n)
    {fiber : FiberId} (active : ActiveAt m fiber) : ActiveAt n fiber := by
  obtain ⟨f, hf, hrun, hpark⟩ := active
  obtain ⟨g, hg, hrun', hpark', _⟩ := controls.active fiber f hf hrun hpark
  exact ⟨g, hg, hrun', hpark'⟩

theorem commandAuthority_transport_commands (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} (controls : CommandControlsPreserved m n)
    (races : RaceHostsPreserved m n) (command : NCmd)
    (authority : CommandAuthority p table m command) : CommandAuthority p table n command := by
  cases command <;> try (exact True.intro)
  all_goals try (exact commandControls_activeAt controls authority)
  case launch raceId =>
    obtain ⟨race, hr, ha⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    exact ⟨next, hn, he ▸ commandControls_activeAt controls ha⟩
  case enrollRace raceId child =>
    obtain ⟨race, hr, ha⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    exact ⟨next, hn, he ▸ commandControls_activeAt controls ha⟩
  case registrationDone raceId yielding =>
    obtain ⟨race, f, hr, hf, hrun, hpark, hcode⟩ := authority
    obtain ⟨next, hn, he⟩ := races raceId race hr
    obtain ⟨g, hg, hrun', hpark', hcurrent⟩ := controls.active race.host f hf hrun hpark
    exact ⟨next, g, hn, he ▸ hg, hrun', hpark', hcurrent ▸ hcode⟩
  case exitDone fiber =>
    obtain ⟨f, hf, he⟩ := authority
    exact controls.exited fiber f hf he

theorem commandControls_interruptRecord (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    CommandControlsPreserved m (m.update (interruptRecord (interpOf p table) who extra f).1) := by
  let g := (interruptRecord (interpOf p table) who extra f).1
  have hid : g.id = f.id := interruptRecord_id p table who extra f
  constructor
  · intro fiber old hold hrun hpark
    by_cases he : old.id = f.id
    · have hlookup : m.fiber? f.id = some old := by
        simpa only [← he, fiber_id_of_lookup hold] using hold
      have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
      subst old
      refine ⟨g, fiber_lookup_update_self hold g (hid.trans (fiber_id_of_lookup hold)), ?_⟩
      cases hx : f.exit <;> cases hi : f.frame.interruptible <;>
        simp [g, interruptRecord, FiberCore.interruptible, FiberCore.recordCause,
          FiberCore.setDeferred, hx, hi, hrun, hpark]
    · refine ⟨old, ?_, hrun, hpark, rfl⟩
      change (m.update g).fiber? fiber = some old
      simp only [fiber_lookup_update, hold, Option.map_some, hid, he, ↓reduceIte]
  · intro fiber old hold hexit
    by_cases he : old.id = f.id
    · have hlookup : m.fiber? f.id = some old := by
        simpa only [← he, fiber_id_of_lookup hold] using hold
      have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
      subst old
      have hg : g = f := by simp only [g, interruptRecord, hexit, ↓reduceIte]
      refine ⟨f, ?_, hexit⟩
      change (m.update g).fiber? fiber = some f
      simpa only [hg] using fiber_lookup_update_self hold g (hid.trans (fiber_id_of_lookup hold))
    · refine ⟨old, ?_, hexit⟩
      change (m.update g).fiber? fiber = some old
      simp only [fiber_lookup_update, hold, Option.map_some, hid, he, ↓reduceIte]

theorem guardQueue_interruptRecord (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    {f : NFiber} (hf : m.fiber? f.id = some f) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    GuardQueue p table (m.update (interruptRecord (interpOf p table) who extra f).1) commands := by
  refine ⟨?_, queue.owners, ?_, queue.codeSites⟩
  · intro command hc
    exact commandAuthority_transport_commands p table
      (commandControls_interruptRecord p table hf who extra)
      (fun _ race hr => ⟨race, hr, rfl⟩) command (queue.authority command hc)
  · refine reservedKeys_of_requests_subset queue.keys ?_ ?_
    · exact Nat.le_refl _
    · exact requestOf_interruptRecord_subset p table hf who extra

theorem guardQueue_emit (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (events) : GuardQueue p table (m.emit events) commands := by
  rcases queue with ⟨ha, ho, ⟨hb, hd⟩, hc⟩
  exact ⟨ha, ho, ⟨hb, hd⟩, hc⟩

theorem guardQueue_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (queue : GuardQueue p table m (.interruptTarget target who extra :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.interruptTarget target who extra) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    have after := guardQueue_emit p table (guardQueue_interruptRecord p table tail
      (f := f) (by simpa only [fiber_id_of_lookup hf] using hf) who extra)
      [RunEvent.interruptRecorded who target]
    simp only [driveStep, hf]
    split
    · exact guardQueue_cons_evaluate p table target after
    · exact after

theorem guardQueue_snoc_evaluate (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (fiber : FiberId) : GuardQueue p table m (commands ++ [.evaluate fiber]) := by
  constructor
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact queue.authority c h
    · obtain rfl := List.mem_singleton.mp h; trivial
  · simpa only [List.filterMap_append, List.filterMap_cons, commandOwner,
      List.filterMap_nil, List.append_nil] using queue.owners
  · simpa only [List.flatMap_append, List.flatMap_cons, commandKeys,
      List.flatMap_nil, List.nil_append, List.append_nil] using queue.keys
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact queue.codeSites c h
    · obtain rfl := List.mem_singleton.mp h; rfl

theorem guardState_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (state : GuardState m) :
    GuardState (interruptEach (interpOf p table) who extra targets (m, commands)).1 := by
  induction targets generalizing m commands with
  | nil => exact state
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, hf] using ih m commands state
    | some f =>
      have next := guardState_emit (guardState_interruptRecord p table (f := f) state
        (by simpa only [fiber_id_of_lookup hf] using hf) (some who) extra)
        [RunEvent.interruptRecorded (some who) target]
      simpa only [interruptEach, List.foldl_cons, hf] using ih _ _ next

theorem guardQueue_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (queue : GuardQueue p table m commands) :
    let result := interruptEach (interpOf p table) who extra targets (m, commands)
    GuardQueue p table result.1 result.2 := by
  induction targets generalizing m commands with
  | nil => exact queue
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, hf] using ih m commands queue
    | some f =>
      have after := guardQueue_emit p table (guardQueue_interruptRecord p table queue
        (f := f) (by simpa only [fiber_id_of_lookup hf] using hf) (some who) extra)
        [RunEvent.interruptRecorded (some who) target]
      have next : GuardQueue p table
          ((m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
            [RunEvent.interruptRecorded (some who) target])
          (commands ++ (if (interruptRecord (interpOf p table) (some who) extra f).2 then
            [.evaluate target] else [])) := by
        split
        · exact guardQueue_snoc_evaluate p table after target
        · simpa only [List.append_nil] using after
      simpa only [interruptEach, List.foldl_cons, hf] using ih _ _ next

theorem requestOf_interruptEach_subset (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val)
    (hrequest : requestOf (interruptEach (interpOf p table) who extra targets (m, commands)).1
      fiber token = some request) : requestOf m fiber token = some request := by
  induction targets generalizing m commands with
  | nil => exact hrequest
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none =>
      apply ih m commands
      simpa only [interruptEach, List.foldl_cons, hf] using hrequest
    | some f =>
      simp only [interruptEach, List.foldl_cons, hf] at hrequest
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra f).2 then
        [.evaluate target] else [])
      have hr := ih next pending hrequest
      exact requestOf_interruptRecord_subset p table (f := f)
        (by simpa only [fiber_id_of_lookup hf] using hf) (some who) extra
        fiber token request hr

theorem nextToken_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) :
    (interruptEach (interpOf p table) who extra targets (m, commands)).1.nextToken = m.nextToken := by
  induction targets generalizing m commands with
  | nil => rfl
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, hf] using ih m commands
    | some f =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra f).2 then
        [.evaluate target] else [])
      have hn : next.nextToken = m.nextToken := rfl
      simpa only [interruptEach, List.foldl_cons, hf] using (ih next pending).trans hn

theorem reservedKeys_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    ReservedKeys (interruptEach (interpOf p table) who extra targets (m, commands)).1 keys := by
  refine reservedKeys_of_requests_subset reserved ?_
    (requestOf_interruptEach_subset p table who extra targets m commands)
  rw [nextToken_interruptEach]
  exact Nat.le_refl _

theorem pending_lookup_guard {m : NativeMachine} (state : GuardState m)
    {f : NFiber} (hf : f ∈ m.fibers) {token : Nat} {pending}
    (hp : f.pending.find? (fun p => p.token = token) = some pending) :
    f.parked = .withGuard token ∧ f.pending = [pending] := by
  have shape := state.pendingShape f hf
  cases hpark : f.parked with
  | notParked =>
    simp only [PendingShape, hpark] at shape
    rw [shape] at hp
    cases hp
  | withGuard offered =>
    simp only [PendingShape, hpark] at shape
    obtain ⟨only, hlist, htoken⟩ := shape
    have hmem : pending ∈ f.pending := List.mem_of_find?_eq_some hp
    rw [hlist] at hmem
    have he := List.mem_singleton.mp hmem
    subst pending
    have ht : only.token = token := of_decide_eq_true
      (List.find?_some (p := fun q : Pending EffName Val Err Defect FiberId Ann =>
        decide (q.token = token)) hp)
    exact ⟨by rw [← ht, htoken], hlist⟩

theorem pending_reserved_noExternal {m : NativeMachine} (state : GuardState m)
    {f : NFiber} (hf : m.fiber? f.id = some f) {token : Nat} {pending}
    (hp : f.pending.find? (fun p => p.token = token) = some pending)
    (reserved : ReservedKeys m [(f.id, token)]) : externalRequest f.frame.current = none := by
  have guard := (pending_lookup_guard state (List.mem_of_find?_eq_some hf) hp).1
  cases hc : externalRequest f.frame.current with
  | none => rfl
  | some request =>
    exact False.elim (reserved.disjoint f.id token request
      (requestOf_of_shape hf guard hc) (List.mem_cons_self ..))

theorem guardState_update_noExternal {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f) (g : NFiber)
    (hid : g.id = f.id) (valid : FiberGuardState m g)
    (reserved : ReservedKeys m (fiberKeys g)) (code : externalRequest g.frame.current = none) :
    GuardState (m.update g) := by
  apply guardState_update (f := f) state hf g hid valid reserved
  intro token request _ hr
  rw [code] at hr
  cases hr

theorem guardState_increaseTokens {m : NativeMachine} (state : GuardState m)
    (next : Nat) (bound : m.nextToken ≤ next) : GuardState { m with nextToken := next } := by
  constructor
  · exact state.fiberIds
  · exact state.fibersBelow
  · exact state.raceIds
  · exact state.racesBelow
  · exact state.raceHosts
  · exact fun key hk => Nat.lt_of_lt_of_le (state.keysBelow key hk) bound
  · exact fun fiber token request hr => Nat.lt_of_lt_of_le
      (state.requestsBelow fiber token request hr) bound
  · exact state.requestsOwned
  · exact state.pendingShape
  · exact state.parkedIdle
  · exact fun f hf token hp => Nat.lt_of_lt_of_le (state.parkedBelow f hf token hp) bound
  · exact state.exited
  · exact state.deferredCause
  · exact state.frameCodes
  · exact state.internalCodes

theorem internalKeys_state_add (m : NativeMachine) (stores : Stores) :
    internalKeys { m with state := stores } ⊆ internalKeys m ++ storeKeys stores := by
  intro key hk
  rw [internalKeys_store_decomposition] at hk
  rcases List.mem_append.mp hk with hs | hf
  · rcases List.mem_append.mp hs with hs | hr
    · exact List.mem_append_right _ hs
    · apply List.mem_append_left
      rw [internalKeys_store_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ hr)
  · apply List.mem_append_left
    rw [internalKeys_store_decomposition]
    exact List.mem_append_right _ hf

theorem guardState_withStoreKeys {m : NativeMachine} (state : GuardState m)
    (stores : Stores) (keys : ReservedKeys m (storeKeys stores))
    (codes : DeferredCodes stores.deferreds) : GuardState { m with state := stores } := by
  have subset := internalKeys_state_add m stores
  constructor
  · exact state.fiberIds
  · exact state.fibersBelow
  · exact state.raceIds
  · exact state.racesBelow
  · exact state.raceHosts
  · intro key hk
    rcases List.mem_append.mp (subset hk) with h | h
    · exact state.keysBelow key h
    · exact keys.below key h
  · exact state.requestsBelow
  · intro fiber token request hr hk
    rcases List.mem_append.mp (subset hk) with h | h
    · exact state.requestsOwned fiber token request hr h
    · exact keys.disjoint fiber token request hr h
  · exact state.pendingShape
  · exact state.parkedIdle
  · exact state.parkedBelow
  · exact state.exited
  · exact state.deferredCause
  · exact state.frameCodes
  · exact ⟨codes.1, codes.2, state.internalCodes.2.2⟩

theorem reservedKeys_fresh {m : NativeMachine} (state : GuardState m) (fiber : FiberId) :
    ReservedKeys { m with nextToken := m.nextToken + 1 } [(fiber, m.nextToken)] := by
  constructor
  · intro key hk
    obtain rfl := List.mem_singleton.mp hk
    exact Nat.lt_succ_self _
  · intro target token request hr hk
    have he := List.mem_singleton.mp hk
    have ht : token = m.nextToken := congrArg Prod.snd he
    have bound := state.requestsBelow target token request hr
    rw [ht] at bound
    exact Nat.lt_irrefl _ bound

theorem guardState_storeFresh {m : NativeMachine} (state : GuardState m)
    (stores : Stores) (fiber : FiberId)
    (keys : storeKeys stores ⊆ storeKeys m.state ++ [(fiber, m.nextToken)])
    (codes : DeferredCodes stores.deferreds) :
    GuardState { m with state := stores, nextToken := m.nextToken + 1 } := by
  let grown : NativeMachine := { m with nextToken := m.nextToken + 1 }
  have sg : GuardState grown := guardState_increaseTokens state _ (Nat.le_succ _)
  have oldKeys : ReservedKeys grown (storeKeys m.state) := by
    apply reservedKeys_subset (reservedKeys_internal grown sg)
    intro key hk
    rw [internalKeys_store_decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ hk)
  exact guardState_withStoreKeys sg stores
    (reservedKeys_subset (reservedKeys_append oldKeys (reservedKeys_fresh state fiber)) keys) codes

theorem frameCodeOwned_transport {m n : NativeMachine} (races : RaceHostsPreserved m n)
    {f : NFiber} (code : FrameCodeOwned m f) : FrameCodeOwned n f :=
  ⟨raceCodeOwned_transport races code.1, fun c hc => raceCodeOwned_transport races (code.2 c hc)⟩

theorem raceIds_update (m : NativeMachine) (race : NRace) :
    (m.updateRace race).races.map Race.id = m.races.map Race.id := by
  simp only [RunMachine.updateRace, List.map_map]
  congr 1
  funext old
  dsimp only [Function.comp_def]
  split <;> simp_all

theorem internalKeys_updateRace_subset {m : NativeMachine} {race : NRace}
    (hr : race ∈ m.races) (next : NRace) (host : next.host = race.host)
    (token : next.token = race.token) : internalKeys (m.updateRace next) ⊆ internalKeys m := by
  intro key hk
  rw [internalKeys_store_decomposition] at hk ⊢
  rcases List.mem_append.mp hk with hs | hf
  · rcases List.mem_append.mp hs with hs | hraces
    · exact List.mem_append_left _ (List.mem_append_left _ hs)
    · apply List.mem_append_left
      apply List.mem_append_right
      obtain ⟨r, hm, he⟩ := List.mem_map.mp hraces
      obtain ⟨old, hold, hreplace⟩ := List.mem_map.mp hm
      subst r
      split at he
      · rw [host, token] at he
        exact List.mem_map.mpr ⟨race, hr, he⟩
      · exact List.mem_map.mpr ⟨old, hold, he⟩
  · exact List.mem_append_right _ hf

theorem guardState_updateRace {m : NativeMachine} {race : NRace} (state : GuardState m)
    (hr : m.race? race.id = some race) (next : NRace) (id : next.id = race.id)
    (host : next.host = race.host) (token : next.token = race.token)
    (programs : ∀ code ∈ next.programs, raceSites code = []) : GuardState (m.updateRace next) := by
  have hmem : race ∈ m.races := List.mem_of_find?_eq_some hr
  have subset := internalKeys_updateRace_subset hmem next host token
  have transport := raceHostsPreserved_updateRace hr next id host
  constructor
  · exact state.fiberIds
  · exact state.fibersBelow
  · rw [raceIds_update]; exact state.raceIds
  · intro r hr'
    obtain ⟨old, hold, he⟩ := List.mem_map.mp hr'
    subst r
    split
    · exact id ▸ state.racesBelow race hmem
    · exact state.racesBelow old hold
  · intro r hr'
    obtain ⟨old, hold, he⟩ := List.mem_map.mp hr'
    subst r
    split
    · exact host ▸ state.raceHosts race hmem
    · exact state.raceHosts old hold
  · exact fun key hk => state.keysBelow key (subset hk)
  · exact state.requestsBelow
  · exact fun fiber token request hr hk => state.requestsOwned fiber token request hr (subset hk)
  · exact state.pendingShape
  · exact state.parkedIdle
  · exact state.parkedBelow
  · exact state.exited
  · exact state.deferredCause
  · exact fun f hf => frameCodeOwned_transport transport (state.frameCodes f hf)
  · refine ⟨state.internalCodes.1, state.internalCodes.2.1, state.internalCodes.2.2.1, ?_⟩
    intro r hr'
    obtain ⟨old, hold, he⟩ := List.mem_map.mp hr'
    subst r
    split
    · exact programs
    · exact state.internalCodes.2.2.2 old hold

theorem reservedKeys_updateRace {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (race : NRace) : ReservedKeys (m.updateRace race) keys := by
  rcases reserved with ⟨hb, hd⟩
  exact ⟨hb, hd⟩

theorem guardQueue_updateRace (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    {race : NRace} (hr : m.race? race.id = some race) (next : NRace)
    (id : next.id = race.id) (host : next.host = race.host) :
    GuardQueue p table (m.updateRace next) commands := by
  apply guardQueue_transport p table (n := m.updateRace next) queue
    (fun _ f hf _ => ⟨f, hf, rfl, rfl, rfl, fun h => h⟩)
    (raceHostsPreserved_updateRace hr next id host)
  · exact Nat.le_refl _
  · exact fun _ _ _ h => h

-- Exit publication and cleared-fiber observations.

theorem requestOf_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.exitDone target) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simp only [driveStep, hf]
  | some f =>
    simp only [driveStep, hf]
    exact requestOf_update_view (f := f) (by simpa only [fiber_id_of_lookup hf] using hf)
      (f.cleared (interpOf p table)) ⟨rfl, rfl, rfl⟩ fiber token

theorem controlsPreserved_cleared (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f) :
    ControlsPreserved m (m.update (f.cleared (interpOf p table))) := by
  intro fiber old hold _
  let g := f.cleared (interpOf p table)
  by_cases he : old.id = f.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [← he, fiber_id_of_lookup hold] using hold
    have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
    subst old
    refine ⟨g, ?_, rfl, rfl, rfl, fun h => h⟩
    simp only [fiber_lookup_update, hold, Option.map_some]
    simp only [g, RunFiber.cleared, ↓reduceIte]
  · refine ⟨old, ?_, rfl, rfl, rfl, fun h => h⟩
    simp only [fiber_lookup_update, hold, Option.map_some]
    simp only [RunFiber.cleared, he, ↓reduceIte]

theorem guardState_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.exitDone target)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.exitDone target) rest).1 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using state
  | some f =>
    simp only [driveStep, hf]
    have hmem := List.mem_of_find?_eq_some hf
    have old := guardState_fiber state hmem
    obtain ⟨f', hf', hexit⟩ := authority
    rw [hf] at hf'
    cases Option.some.inj hf'
    have hpark := (old.exited hexit).1
    let g := f.cleared (interpOf p table)
    have valid : FiberGuardState m g := by
      refine ⟨old.below, old.pending, old.idle, old.parkedBelow, old.exited,
        old.deferredCause, ⟨old.codes.1, ?_⟩, old.tasks⟩
      intro code hc
      cases hc
    have reserved : ReservedKeys m (fiberKeys g) := by
      have r := reservedKeys_fiber state hmem
      constructor
      · intro key hk
        exact r.below key (List.mem_append_right _ hk)
      · intro fiber token request hr hk
        exact r.disjoint fiber token request hr (List.mem_append_right _ hk)
    exact guardState_update_unparked (f := f) state
      (by simpa only [fiber_id_of_lookup hf] using hf) g rfl valid reserved hpark

theorem guardQueue_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (queue : GuardQueue p table m (.exitDone target :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.exitDone target) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    simp only [driveStep, hf]
    apply guardQueue_transport p table tail
      (controlsPreserved_cleared p table (f := f) (by simpa only [fiber_id_of_lookup hf] using hf))
      (fun _ race hr => ⟨race, hr, rfl⟩) (Nat.le_refl _)
    intro fiber token request hr
    rw [requestOf_update_view (f := f)
      (by simpa only [fiber_id_of_lookup hf] using hf)
      (f.cleared (interpOf p table)) ⟨rfl, rfl, rfl⟩] at hr
    exact hr

theorem reservedKeys_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.exitDone target) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · cases hf : m.fiber? target <;> simp only [driveStep, hf] <;> exact Nat.le_refl _
  · exact requestOf_driveStep_exitDone p table m target rest


theorem interruptedAt_cleared (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    InterruptedAt (m.update (f.cleared (interpOf p table))) fiber := by
  obtain ⟨old, hold, interrupted⟩ := h
  by_cases he : old.id = f.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [← he, fiber_id_of_lookup hold] using hold
    have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
    subst old
    refine ⟨f.cleared (interpOf p table), ?_, interrupted⟩
    simp only [fiber_lookup_update, hold, Option.map_some, RunFiber.cleared, ↓reduceIte]
  · refine ⟨old, ?_, interrupted⟩
    simp only [fiber_lookup_update, hold, Option.map_some, RunFiber.cleared, he, ↓reduceIte]

theorem interruptedAt_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.exitDone target) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using h
  | some f =>
    simpa only [driveStep, hf] using interruptedAt_cleared p table (f := f)
      (by simpa only [fiber_id_of_lookup hf] using hf) fiber h



-- Child tracking changes no guard observation.

theorem guardState_modify_view {m : NativeMachine} (state : GuardState m)
    (target : FiberId) (k : NFiber → NFiber)
    (valid : ∀ f ∈ m.fibers, FiberGuardState m (k f))
    (view : ∀ f, RequestView f (k f)) (keys : ∀ f, fiberKeys (k f) = fiberKeys f) :
    GuardState (m.modify target k) := by
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => exact state
  | some f =>
    exact guardState_update_view (f := f) state
      (by simpa only [fiber_id_of_lookup hf] using hf) (k f)
      (valid f (List.mem_of_find?_eq_some hf)) (view f) (keys f)

theorem guardQueue_modify_fields (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (target : FiberId) (k : NFiber → NFiber) (view : ∀ f, RequestView f (k f))
    (exit : ∀ f, (k f).exit = f.exit) (running : ∀ f, f.running = true → (k f).running = true) :
    GuardQueue p table (m.modify target k) commands := by
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => exact queue
  | some f =>
    have hf' : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    apply guardQueue_transport p table queue
      (controlsPreserved_update_fields hf' (k f) (view f) (exit f) (running f))
      (fun _ race hr => ⟨race, hr, rfl⟩) (Nat.le_refl _)
    intro fiber token request hr
    rw [requestOf_update_view hf' (k f) (view f)] at hr
    exact hr

theorem reservedKeys_modify_view {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (target : FiberId) (k : NFiber → NFiber)
    (view : ∀ f, RequestView f (k f)) : ReservedKeys (m.modify target k) keys := by
  apply reservedKeys_of_same_requests reserved
  · unfold RunMachine.modify
    cases hf : m.fiber? target <;> exact Nat.le_refl _
  · exact fun fiber token => requestOf_modify_view m target fiber token k view

theorem interruptedAt_modify_view {m : NativeMachine} (target : FiberId) (k : NFiber → NFiber)
    (id : ∀ f, (k f).id = f.id) (mark : ∀ f, Interrupted f → Interrupted (k f))
    (fiber : FiberId) (h : InterruptedAt m fiber) : InterruptedAt (m.modify target k) fiber := by
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => exact h
  | some f =>
    obtain ⟨old, hold, interrupted⟩ := h
    by_cases he : old.id = f.id
    · have hlookup : m.fiber? target = some old := by
        rw [← fiber_id_of_lookup hf, ← he, fiber_id_of_lookup hold]
        exact hold
      have heq : old = f := Option.some.inj (hlookup.symm.trans hf)
      subst old
      refine ⟨k f, ?_, mark f interrupted⟩
      simp only [fiber_lookup_update, hold, Option.map_some, id f, ↓reduceIte]
    · refine ⟨old, ?_, interrupted⟩
      simp only [fiber_lookup_update, hold, Option.map_some, id f, he, ↓reduceIte]

theorem fiberGuardState_children {m : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (children : List FiberId) :
    FiberGuardState m { f with children := children } := by
  rcases valid
  constructor <;> assumption

theorem fiberGuardState_observers {m : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (observers : List Observer) :
    FiberGuardState m { f with observers := observers } := by
  rcases valid
  constructor <;> assumption

def trackedChild (m : NativeMachine) (parent child : FiberId) : NativeMachine :=
  (m.modify parent fun f => { f with children := f.children ++ [child] }).modify child
    fun f => { f with observers := f.observers ++ [.untrackChild parent] }

theorem guardState_trackedChild {m : NativeMachine} (state : GuardState m)
    (parent child : FiberId) : GuardState (trackedChild m parent child) := by
  have first : GuardState (m.modify parent fun f => { f with children := f.children ++ [child] }) :=
    guardState_modify_view state parent (fun f => { f with children := f.children ++ [child] })
      (fun f hf => fiberGuardState_children (guardState_fiber state hf) (f.children ++ [child]))
      (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl)
  apply guardState_modify_view first child (fun f => { f with observers := f.observers ++ [.untrackChild parent] })
    (fun f hf => fiberGuardState_observers (guardState_fiber first hf) (f.observers ++ [.untrackChild parent]))
    (fun _ => ⟨rfl, rfl, rfl⟩)
  intro f
  simp only [fiberKeys, List.flatMap_append, List.flatMap_cons, observerKeys,
    List.flatMap_nil, List.append_nil]

theorem guardQueue_trackedChild (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (parent child : FiberId) : GuardQueue p table (trackedChild m parent child) commands :=
  guardQueue_modify_fields p table
    (guardQueue_modify_fields p table queue parent (fun f => { f with children := f.children ++ [child] }) (fun _ => ⟨rfl, rfl, rfl⟩)
      (fun _ => rfl) (fun _ h => h)) child (fun f => { f with observers := f.observers ++ [.untrackChild parent] }) (fun _ => ⟨rfl, rfl, rfl⟩)
    (fun _ => rfl) (fun _ h => h)

theorem reservedKeys_trackedChild {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (parent child : FiberId) :
    ReservedKeys (trackedChild m parent child) keys :=
  reservedKeys_modify_view
    (reservedKeys_modify_view reserved parent (fun f => { f with children := f.children ++ [child] }) (fun _ => ⟨rfl, rfl, rfl⟩))
    child (fun f => { f with observers := f.observers ++ [.untrackChild parent] }) (fun _ => ⟨rfl, rfl, rfl⟩)

theorem requestOf_trackedChild (m : NativeMachine) (parent child fiber : FiberId) (token : Nat) :
    requestOf (trackedChild m parent child) fiber token = requestOf m fiber token := by
  unfold trackedChild
  rw [requestOf_modify_view _ child fiber token (fun f => { f with observers := f.observers ++ [.untrackChild parent] }) (fun _ => ⟨rfl, rfl, rfl⟩),
    requestOf_modify_view m parent fiber token (fun f => { f with children := f.children ++ [child] }) (fun _ => ⟨rfl, rfl, rfl⟩)]

theorem interruptedAt_trackedChild {m : NativeMachine} (parent child fiber : FiberId)
    (h : InterruptedAt m fiber) : InterruptedAt (trackedChild m parent child) fiber :=
  interruptedAt_modify_view child (fun f => { f with observers := f.observers ++ [.untrackChild parent] }) (fun _ => rfl) (fun _ h => h) fiber
    (interruptedAt_modify_view parent (fun f => { f with children := f.children ++ [child] }) (fun _ => rfl) (fun _ h => h) fiber h)

theorem guardState_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.trackChild parent child) rest).1 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? child with
  | none => simpa only [driveStep, hf] using state
  | some f =>
    simp only [driveStep, hf]
    split
    · exact state
    · exact guardState_trackedChild state parent child

theorem guardQueue_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd)
    (queue : GuardQueue p table m (.trackChild parent child :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.trackChild parent child) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hf : m.fiber? child with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    simp only [driveStep, hf]
    split
    · exact tail
    · exact guardQueue_trackedChild p table tail parent child

theorem reservedKeys_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.trackChild parent child) rest).1 keys := by
  letI := evaluatorFor p table
  cases hf : m.fiber? child with
  | none => simpa only [driveStep, hf] using reserved
  | some f =>
    simp only [driveStep, hf]
    split
    · exact reserved
    · exact reservedKeys_trackedChild reserved parent child

theorem requestOf_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.trackChild parent child) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  cases hf : m.fiber? child with
  | none => simp only [driveStep, hf]
  | some f =>
    simp only [driveStep, hf]
    split
    · rfl
    · exact requestOf_trackedChild m parent child fiber token

theorem interruptedAt_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.trackChild parent child) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? child with
  | none => simpa only [driveStep, hf] using h
  | some f =>
    simp only [driveStep, hf]
    split
    · exact h
    · exact interruptedAt_trackedChild parent child fiber h


-- Scope linking preserves guard ownership.

theorem scopeLinkFiber_guardStores (p : NativeEff) (table : RowTable)
    (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {before after : Stores} {key : Nat}
    (h : (interpOf p table).scopeLinkFiber mode scope fiber before = some (after, key)) :
    after.timers = before.timers ∧ after.deferreds = before.deferreds := by
  dsimp only [interpOf] at h
  cases he : before.scopes.entryAt scope with
  | none => rw [he] at h; cases h
  | some entry =>
    rw [he] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem guardState_scopeLinkFiber (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m)
    (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {after : Stores} {key : Nat}
    (h : (interpOf p table).scopeLinkFiber mode scope fiber m.state = some (after, key)) :
    GuardState { m with state := after } := by
  have hs := scopeLinkFiber_guardStores p table mode scope fiber h
  apply guardState_withState state
  · simp only [storeKeys, hs.1, hs.2]
    exact List.Subset.refl _
  · rw [hs.2]
    exact ⟨state.internalCodes.1, state.internalCodes.2.1⟩

theorem guardQueue_withState (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (state : Stores) : GuardQueue p table { m with state := state } commands := by
  rcases queue with ⟨ha, ho, ⟨hb, hd⟩, hc⟩
  exact ⟨ha, ho, ⟨hb, hd⟩, hc⟩

theorem reservedKeys_withState {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (state : Stores) :
    ReservedKeys { m with state := state } keys := by
  rcases reserved with ⟨hb, hd⟩
  exact ⟨hb, hd⟩

theorem interruptedAt_update_interruptRecord (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {target : FiberId} {f : NFiber} (hf : m.fiber? target = some f)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    InterruptedAt (m.update (interruptRecord (interpOf p table) who extra f).1) fiber := by
  let g := (interruptRecord (interpOf p table) who extra f).1
  have hid : g.id = target := (interruptRecord_id p table who extra f).trans (fiber_id_of_lookup hf)
  by_cases he : target = fiber
  · refine ⟨g, ?_, interruptRecord_interrupted p table who extra f⟩
    exact he ▸ fiber_lookup_update_self hf g hid
  · obtain ⟨old, hold, interrupted⟩ := h
    refine ⟨old, ?_, interrupted⟩
    change (m.update g).fiber? fiber = some old
    simp only [fiber_lookup_update, hold, Option.map_some, hid,
      fiber_id_of_lookup hold, Ne.symm he, ↓reduceIte]

theorem requestOrInterrupted_linkScope (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hrequest : requestOf m fiber token = some request) :
    requestOf (linkScope (interpOf p table) m mode scope target who extra).1 fiber token = some request ∨
      InterruptedAt (linkScope (interpOf p table) m mode scope target who extra).1 fiber := by
  unfold linkScope
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => exact Or.inl hrequest
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact Or.inl hrequest
      | some f =>
        let g := (interruptRecord (interpOf p table) who extra f).1
        have hid : g.id = target := (interruptRecord_id p table who extra f).trans (fiber_id_of_lookup hf)
        by_cases he : target = fiber
        · right
          refine ⟨g, ?_, interruptRecord_interrupted p table who extra f⟩
          exact he ▸ fiber_lookup_update_self hf g hid
        · left
          exact (requestOf_update_other m g fiber token (fun h => he (hid.symm.trans h))) ▸ hrequest
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact Or.inl hrequest
      | some f =>
        simp only []
        split
        · exact Or.inl hrequest
        · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => exact Or.inl hrequest
          | some result =>
            rcases result with ⟨state, key⟩
            simp only []
            left
            exact (requestOf_modify_view ({ m with state := state } : NativeMachine)
              target fiber token
              (fun f => { f with observers := f.observers ++ [.dropScopeFinalizer scope key] })
              (fun _ => ⟨rfl, rfl, rfl⟩)).trans hrequest

theorem interruptedAt_linkScope (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    InterruptedAt (linkScope (interpOf p table) m mode scope target who extra).1 fiber := by
  unfold linkScope
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => exact h
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact h
      | some f => exact interruptedAt_update_interruptRecord p table hf who extra fiber h
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact h
      | some f =>
        simp only []
        split
        · exact h
        · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => exact h
          | some result =>
            rcases result with ⟨state, key⟩
            simp only []
            exact interruptedAt_modify_view target
              (fun f => { f with observers := f.observers ++ [.dropScopeFinalizer scope key] })
              (fun _ => rfl) (fun _ h => h) fiber h


theorem guardQueue_halt (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (queue : GuardQueue p table m rest) (why : Stuck) :
    GuardQueue p table (m.halt why) rest := by
  rcases queue with ⟨ha, ho, ⟨hb, hd⟩, hc⟩
  exact ⟨ha, ho, ⟨hb, hd⟩, hc⟩

theorem guardState_linkScope (p : NativeEff) (table : RowTable)
    {m : NativeMachine} (state : GuardState m)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    GuardState (linkScope (interpOf p table) m mode scope target who extra).1 := by
  unfold linkScope
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => exact guardState_halt state _
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact guardState_halt state _
      | some f =>
        exact guardState_emit (guardState_interruptRecord p table (f := f) state
          (by simpa only [fiber_id_of_lookup hf] using hf) who extra) _
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact guardState_halt state _
      | some f =>
        simp only []
        split
        · exact state
        · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => exact guardState_halt state _
          | some result =>
            rcases result with ⟨after, key⟩
            simp only []
            have valid := guardState_scopeLinkFiber p table state mode scope target hl
            apply guardState_emit
            apply guardState_modify_view valid target
              (fun g => { g with observers := g.observers ++ [.dropScopeFinalizer scope key] })
              (fun g hg => fiberGuardState_observers (guardState_fiber valid hg)
                (g.observers ++ [.dropScopeFinalizer scope key])) (fun _ => ⟨rfl, rfl, rfl⟩)
            intro g
            simp only [fiberKeys, List.flatMap_append, List.flatMap_cons, observerKeys,
              List.flatMap_nil, List.append_nil]

theorem guardQueue_linkScope (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (queue : GuardQueue p table m rest)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    let result := linkScope (interpOf p table) m mode scope target who extra
    GuardQueue p table result.1 (result.2 ++ rest) := by
  unfold linkScope
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => exact guardQueue_halt p table queue _
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact guardQueue_halt p table queue _
      | some f =>
        have after := guardQueue_emit p table (guardQueue_interruptRecord p table (f := f) queue
          (by simpa only [fiber_id_of_lookup hf] using hf) who extra)
          [RunEvent.scopeClosedOnLink scope target, RunEvent.interruptRecorded who target]
        simp only []
        split
        · exact guardQueue_cons_evaluate p table target after
        · exact after
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact guardQueue_halt p table queue _
      | some f =>
        simp only []
        split
        · exact queue
        · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => exact guardQueue_halt p table queue _
          | some result =>
            rcases result with ⟨after, key⟩
            simp only []
            exact guardQueue_emit p table
              (guardQueue_modify_fields p table (guardQueue_withState p table queue after) target
                (fun g => { g with observers := g.observers ++ [.dropScopeFinalizer scope key] })
                (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl) (fun _ h => h)) _

theorem reservedKeys_halt {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (why : Stuck) : ReservedKeys (m.halt why) keys := by
  rcases reserved with ⟨hb, hd⟩
  exact ⟨hb, hd⟩

theorem reservedKeys_emit {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (events) : ReservedKeys (m.emit events) keys := by
  rcases reserved with ⟨hb, hd⟩
  exact ⟨hb, hd⟩

theorem reservedKeys_linkScope (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {keys : List GuardKey} (reserved : ReservedKeys m keys)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ReservedKeys (linkScope (interpOf p table) m mode scope target who extra).1 keys := by
  unfold linkScope
  cases hs : (interpOf p table).scopeStatus scope m.state with
  | none => exact reservedKeys_halt reserved _
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact reservedKeys_halt reserved _
      | some f =>
        apply reservedKeys_of_requests_subset reserved
        · exact Nat.le_refl _
        · exact requestOf_interruptRecord_subset p table (f := f)
            (by simpa only [fiber_id_of_lookup hf] using hf) who extra
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact reservedKeys_halt reserved _
      | some f =>
        simp only []
        split
        · exact reserved
        · cases hl : (interpOf p table).scopeLinkFiber mode scope target m.state with
          | none => exact reservedKeys_halt reserved _
          | some result =>
            rcases result with ⟨after, key⟩
            simp only []
            exact reservedKeys_emit (reservedKeys_modify_view (reservedKeys_withState reserved after) target
              (fun g => { g with observers := g.observers ++ [.dropScopeFinalizer scope key] })
              (fun _ => ⟨rfl, rfl, rfl⟩)) _

theorem guardState_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.link mode scope target who extra) rest).1 :=
  guardState_linkScope p table state mode scope target who extra

theorem guardQueue_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (queue : GuardQueue p table m (.link mode scope target who extra :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.link mode scope target who extra) rest
    GuardQueue p table result.1 result.2 :=
  guardQueue_linkScope p table (guardQueue_tail p table queue) mode scope target who extra

theorem reservedKeys_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.link mode scope target who extra) rest).1 keys :=
  reservedKeys_linkScope p table reserved mode scope target who extra

theorem requestOrInterrupted_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hrequest : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    let after := (driveStep (interpOf p table) m (.link mode scope target who extra) rest).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber :=
  requestOrInterrupted_linkScope p table m mode scope target who extra fiber token request hrequest

theorem interruptedAt_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (fiber : FiberId) (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.link mode scope target who extra) rest).1 fiber :=
  interruptedAt_linkScope p table m mode scope target who extra fiber h


-- Spawn-agent checked spawn/launchEntrant/forkFinalizers helpers.
abbrev spawnAppend (m : NativeMachine) (child : NFiber) : NativeMachine :=
  { m with fibers := m.fibers ++ [child], nextId := m.nextId + 1 }

theorem fiber_lookup_spawnAppend_old (m : NativeMachine) (child : NFiber)
    {fiber : FiberId} {f : NFiber} (hf : m.fiber? fiber = some f) :
    (spawnAppend m child).fiber? fiber = some f := by
  change m.fibers.find? _ = some f at hf
  simp only [RunMachine.fiber?, List.find?_append, hf, Option.some_or]

theorem requestOf_spawnAppend (m : NativeMachine) (child : NFiber)
    (idle : child.parked = .notParked) (fiber : FiberId) (token : Nat) :
    requestOf (spawnAppend m child) fiber token = requestOf m fiber token := by
  cases hf : m.fiber? fiber with
  | some f =>
    exact requestOf_eq_of_fiber_eq fiber token
      ((fiber_lookup_spawnAppend_old m child hf).trans hf.symm)
  | none =>
    change m.fibers.find? _ = none at hf
    simp only [requestOf, RunMachine.fiber?, List.find?_append, hf,
      Option.none_or, List.find?_cons, List.find?_nil]
    split <;> simp [idle, guard]

theorem interruptedAt_spawnAppend {m : NativeMachine} (child : NFiber)
    {fiber : FiberId} (hi : InterruptedAt m fiber) :
    InterruptedAt (spawnAppend m child) fiber := by
  obtain ⟨f, hf, hi⟩ := hi
  exact ⟨f, fiber_lookup_spawnAppend_old m child hf, hi⟩

theorem controlsPreserved_spawnAppend (m : NativeMachine) (child : NFiber) :
    ControlsPreserved m (spawnAppend m child) := by
  intro fiber f hf _
  exact ⟨f, fiber_lookup_spawnAppend_old m child hf, rfl, rfl, rfl, fun h => h⟩

theorem raceHostsPreserved_spawnAppend (m : NativeMachine) (child : NFiber) :
    RaceHostsPreserved m (spawnAppend m child) := by
  intro raceId race hr
  exact ⟨race, hr, rfl⟩

theorem internalKeys_spawnAppend (m : NativeMachine) (child : NFiber)
    (keys : fiberKeys child = []) : internalKeys (spawnAppend m child) = internalKeys m := by
  simp only [internalKeys, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  change _ ++ (_ ++ fiberKeys child) = _
  rw [keys, List.append_nil]

theorem guardState_spawnAppend {m : NativeMachine} (state : GuardState m)
    (child : NFiber) (fresh : child.id.value = m.nextId)
    (valid : FiberGuardState { m with nextId := m.nextId + 1 } child)
    (idle : child.parked = .notParked) (keys : fiberKeys child = []) :
    GuardState (spawnAppend m child) := by
  have hall (P : NFiber → Prop) (old : ∀ f ∈ m.fibers, P f) (new : P child) :
      ∀ f ∈ (spawnAppend m child).fibers, P f := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact old f hf
    · have he : f = child := List.mem_singleton.mp hf
      exact he ▸ new
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨state.fiberIds, by simp, ?_⟩
    intro id hid other hother heq
    have he : id = child.id := heq.trans (List.mem_singleton.mp hother)
    obtain ⟨f, hf, hfid⟩ := List.mem_map.mp hid
    have bound := state.fibersBelow f hf
    have : f.id.value = m.nextId := congrArg FiberId.value (hfid.trans he) |>.trans fresh
    omega
  · exact hall _ (fun f hf => Nat.lt_trans (state.fibersBelow f hf) (Nat.lt_succ_self _)) valid.below
  · exact state.raceIds
  · exact state.racesBelow
  · intro race hr
    obtain ⟨f, hf⟩ := state.raceHosts race hr
    exact ⟨f, fiber_lookup_spawnAppend_old m child hf⟩
  · intro key hk
    rw [internalKeys_spawnAppend m child keys] at hk
    exact state.keysBelow key hk
  · intro fiber token request hr
    rw [requestOf_spawnAppend m child idle] at hr
    exact state.requestsBelow fiber token request hr
  · intro fiber token request hr hk
    rw [requestOf_spawnAppend m child idle] at hr
    rw [internalKeys_spawnAppend m child keys] at hk
    exact state.requestsOwned fiber token request hr hk
  · exact hall _ state.pendingShape valid.pending
  · exact hall _ state.parkedIdle valid.idle
  · exact hall _ state.parkedBelow valid.parkedBelow
  · exact hall _ state.exited valid.exited
  · exact hall _ state.deferredCause valid.deferredCause
  · exact hall _ state.frameCodes valid.codes
  · exact ⟨state.internalCodes.1, state.internalCodes.2.1,
      hall _ state.internalCodes.2.2.1 valid.tasks, state.internalCodes.2.2.2⟩

theorem fiberGuardState_freshChild (m : NativeMachine) (code : NCode)
    (sites : raceSites code = []) (flag : Bool) (budget : Nat × Bool) (ctx : Ctx) :
    FiberGuardState { m with nextId := m.nextId + 1 }
      (RunFiber.make ⟨m.nextId⟩ code flag budget ctx) := by
  constructor
  · exact Nat.lt_succ_self _
  · rfl
  · intro _; rfl
  · intro token h; cases h
  · intro h; cases h
  · intro h; cases h
  · constructor
    · exact raceCodeOwned_of_no_sites _ _ code sites
    · intro code h; cases h
  · intro bucket h; cases h

abbrev spawnedChild (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) : NFiber :=
  RunFiber.make ⟨m.nextId⟩ code
    (match options.maskMode with
    | .interruptible => true
    | .uninterruptible => false
    | .inherit => parent.frame.interruptible)
    ((interpOf p table).budgetOf parent.context) parent.context

theorem spawn_machine (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    (spawn (interpOf p table) m parent code options).1 =
      (spawnAppend m (spawnedChild p table m parent code options)).emit
        [.forked parent.id ⟨m.nextId⟩ options.daemon] := rfl

theorem requestOf_spawn (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions)
    (fiber : FiberId) (token : Nat) :
    requestOf (spawn (interpOf p table) m parent code options).1 fiber token =
      requestOf m fiber token :=
  requestOf_spawnAppend m (spawnedChild p table m parent code options) rfl fiber token

theorem interruptedAt_spawn (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions)
    {fiber : FiberId} (hi : InterruptedAt m fiber) :
    InterruptedAt (spawn (interpOf p table) m parent code options).1 fiber :=
  interruptedAt_spawnAppend (spawnedChild p table m parent code options) hi

theorem guardState_spawn (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (state : GuardState m) (parent : NFiber) (code : NCode)
    (sites : raceSites code = []) (options : Supervision.ForkOptions) :
    GuardState (spawn (interpOf p table) m parent code options).1 := by
  rw [spawn_machine]
  apply guardState_emit
  apply guardState_spawnAppend state _ rfl
  · exact fiberGuardState_freshChild m code sites _ _ _
  · rfl
  · rfl

theorem reservedKeys_spawn (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {keys : List GuardKey} (reserved : ReservedKeys m keys)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    ReservedKeys (spawn (interpOf p table) m parent code options).1 keys :=
  reservedKeys_of_same_requests reserved (Nat.le_refl _) (requestOf_spawn p table m parent code options)

theorem guardQueue_spawn (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {rest : List NCmd} (queue : GuardQueue p table m rest)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    GuardQueue p table (spawn (interpOf p table) m parent code options).1 rest := by
  apply guardQueue_transport p table queue
  · exact controlsPreserved_spawnAppend m (spawnedChild p table m parent code options)
  · exact raceHostsPreserved_spawnAppend m (spawnedChild p table m parent code options)
  · exact Nat.le_refl _
  · intro fiber token request hr
    rw [requestOf_spawn] at hr
    exact hr

theorem fiber_lookup_nextId_none {m : NativeMachine} (state : GuardState m) :
    m.fiber? ⟨m.nextId⟩ = none := by
  apply List.find?_eq_none.mpr
  intro f hf
  intro he
  have he := of_decide_eq_true he
  have hb := state.fibersBelow f hf
  have hv := congrArg FiberId.value he
  simp only at hv
  omega

theorem spawn_parent_unchanged (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    (spawn (interpOf p table) m parent code options).2.1 = parent := rfl

theorem spawn_child_fresh (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (state : GuardState m) (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    m.fiber? (spawn (interpOf p table) m parent code options).2.2 = none :=
  fiber_lookup_nextId_none state

theorem spawn_child_below (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    (spawn (interpOf p table) m parent code options).2.2.value <
      (spawn (interpOf p table) m parent code options).1.nextId := Nat.lt_succ_self _

theorem spawn_child_lookup (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (state : GuardState m) (parent : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    (spawn (interpOf p table) m parent code options).1.fiber?
      (spawn (interpOf p table) m parent code options).2.2 =
        some (spawnedChild p table m parent code options) := by
  have hf := fiber_lookup_nextId_none state
  change m.fibers.find? _ = none at hf
  simp only [spawn, RunMachine.emit, RunMachine.fiber?, List.find?_append,
    hf, Option.none_or, List.find?_cons, RunFiber.make, decide_true]
  rfl

theorem spawn_child_raceSites (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : NFiber) (code : NCode) (sites : raceSites code = [])
    (options : Supervision.ForkOptions) :
    raceSites (spawnedChild p table m parent code options).frame.current = [] := sites

theorem requestOf_launchEntrant (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (raceId : Nat) (host : NFiber) (code : NCode) (fiber : FiberId) (token : Nat) :
    requestOf (launchEntrant (interpOf p table) raceId m host code).1 fiber token =
      requestOf m fiber token :=
  requestOf_spawn p table m host code ⟨true, true, .interruptible⟩ fiber token

theorem interruptedAt_launchEntrant (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (raceId : Nat) (host : NFiber) (code : NCode) {fiber : FiberId}
    (hi : InterruptedAt m fiber) :
    InterruptedAt (launchEntrant (interpOf p table) raceId m host code).1 fiber :=
  interruptedAt_spawn p table host code ⟨true, true, .interruptible⟩ hi

theorem guardState_launchEntrant (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (state : GuardState m) (raceId : Nat) (host : NFiber) (code : NCode)
    (sites : raceSites code = []) :
    GuardState (launchEntrant (interpOf p table) raceId m host code).1 :=
  guardState_spawn p table state host code sites ⟨true, true, .interruptible⟩

theorem guardQueue_launchEntrant (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {rest : List NCmd} (queue : GuardQueue p table m rest)
    (raceId : Nat) (host : NFiber) (code : NCode) :
    GuardQueue p table (launchEntrant (interpOf p table) raceId m host code).1 rest :=
  guardQueue_spawn p table queue host code ⟨true, true, .interruptible⟩

theorem reservedKeys_launchEntrant (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {keys : List GuardKey} (reserved : ReservedKeys m keys)
    (raceId : Nat) (host : NFiber) (code : NCode) :
    ReservedKeys (launchEntrant (interpOf p table) raceId m host code).1 keys :=
  reservedKeys_spawn p table reserved host code ⟨true, true, .interruptible⟩

theorem requestOf_forkFinalizers (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (host : NFiber) (programs : List NCode) (fiber : FiberId) (token : Nat) :
    requestOf (forkFinalizers (interpOf p table) m host programs).1 fiber token =
      requestOf m fiber token := by
  induction programs generalizing m with
  | nil => rfl
  | cons code programs ih =>
    simp only [forkFinalizers]
    exact (ih _).trans (requestOf_spawn p table m host code ⟨true, true, .inherit⟩ fiber token)

theorem interruptedAt_forkFinalizers (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (host : NFiber) (programs : List NCode) {fiber : FiberId}
    (hi : InterruptedAt m fiber) :
    InterruptedAt (forkFinalizers (interpOf p table) m host programs).1 fiber := by
  induction programs generalizing m with
  | nil => exact hi
  | cons code programs ih =>
    exact ih (interruptedAt_spawn p table host code ⟨true, true, .inherit⟩ hi)

theorem guardState_forkFinalizers (p : NativeEff) (table : RowTable) {m : NativeMachine}
    (state : GuardState m) (host : NFiber) (programs : List NCode)
    (sites : ∀ code ∈ programs, raceSites code = []) :
    GuardState (forkFinalizers (interpOf p table) m host programs).1 := by
  induction programs generalizing m with
  | nil => exact state
  | cons code programs ih =>
    exact ih (guardState_spawn p table state host code (sites code (List.mem_cons_self ..)) ⟨true, true, .inherit⟩)
      (fun code hc => sites code (List.mem_cons_of_mem _ hc))

theorem guardQueue_forkFinalizers (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {rest : List NCmd} (queue : GuardQueue p table m rest)
    (host : NFiber) (programs : List NCode) :
    GuardQueue p table (forkFinalizers (interpOf p table) m host programs).1 rest := by
  induction programs generalizing m with
  | nil => exact queue
  | cons code programs ih => exact ih (guardQueue_spawn p table queue host code ⟨true, true, .inherit⟩)

theorem reservedKeys_forkFinalizers (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {keys : List GuardKey} (reserved : ReservedKeys m keys)
    (host : NFiber) (programs : List NCode) :
    ReservedKeys (forkFinalizers (interpOf p table) m host programs).1 keys := by
  induction programs generalizing m with
  | nil => exact reserved
  | cons code programs ih => exact ih (reservedKeys_spawn p table reserved host code ⟨true, true, .inherit⟩)



/-- Installing a scheduler-owned observer reserves exactly its callback keys. -/
theorem guardState_addObserver {m : NativeMachine} (state : GuardState m)
    (target : FiberId) (observer : Observer) (reserved : ReservedKeys m (observerKeys observer)) :
    GuardState (m.modify target fun f => { f with observers := f.observers ++ [observer] }) := by
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => exact state
  | some f =>
    have fm := List.mem_of_find?_eq_some hf
    apply guardState_update_preserved_request (f := f) state
      (by simpa only [fiber_id_of_lookup hf] using hf)
      { f with observers := f.observers ++ [observer] }
      (fiberGuardState_observers (guardState_fiber state fm) _) ⟨rfl, rfl, rfl⟩
    apply reservedKeys_subset (reservedKeys_append (reservedKeys_fiber state fm) reserved)
    intro key hk
    simpa only [fiberKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_append, or_assoc, or_left_comm, or_comm] using hk

theorem guardQueue_addObserver (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (target : FiberId) (observer : Observer) :
    GuardQueue p table (m.modify target fun f => { f with observers := f.observers ++ [observer] })
      commands :=
  guardQueue_modify_fields p table queue target
    (fun f => { f with observers := f.observers ++ [observer] })
    (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl) (fun _ h => h)

theorem reservedKeys_addObserver {m : NativeMachine} {keys : List GuardKey}
    (reserved : ReservedKeys m keys) (target : FiberId) (observer : Observer) :
    ReservedKeys (m.modify target fun f => { f with observers := f.observers ++ [observer] }) keys :=
  reservedKeys_modify_view reserved target
    (fun f => { f with observers := f.observers ++ [observer] }) (fun _ => ⟨rfl, rfl, rfl⟩)

theorem requestOf_addObserver (m : NativeMachine) (target : FiberId) (observer : Observer)
    (fiber : FiberId) (token : Nat) :
    requestOf (m.modify target fun f => { f with observers := f.observers ++ [observer] })
      fiber token = requestOf m fiber token :=
  requestOf_modify_view m target fiber token
    (fun f => { f with observers := f.observers ++ [observer] }) (fun _ => ⟨rfl, rfl, rfl⟩)

theorem interruptedAt_addObserver {m : NativeMachine} (target : FiberId) (observer : Observer)
    {fiber : FiberId} (interrupted : InterruptedAt m fiber) :
    InterruptedAt (m.modify target fun f => { f with observers := f.observers ++ [observer] }) fiber :=
  interruptedAt_modify_view target (fun f => { f with observers := f.observers ++ [observer] })
    (fun _ => rfl) (fun _ h => h) fiber interrupted

theorem raceSites_exitValue (p : NativeEff) (table : RowTable) (exit : ExitV)
    (mode : Supervision.ObserverMode) : raceSites ((interpOf p table).exitValue exit mode) = [] := by
  cases mode <;> cases exit <;> rfl

theorem raceSites_raceSettle (p : NativeEff) (table : RowTable) (race : Nat)
    (cleanup : Bool) (exit : ExitV) :
    raceSites ((interpOf p table).raceSettle race cleanup exit) = [] := by
  change raceSites (embed (raceSettleProgram race cleanup exit)) = []
  unfold raceSettleProgram
  split
  · rfl
  · exact raceSites_embed_ofExit exit

theorem raceSites_countdownResume (p : NativeEff) (table : RowTable)
    (resumeWith : Resume EffName) (exits : List ExitV) :
    raceSites (countdownPark.resumePrim (interpOf p table) resumeWith exits) = [] := by
  cases resumeWith <;> rfl

theorem guardQueue_snoc_resume (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    (fiber : FiberId) (token : Nat) (code : NCode)
    (reserved : ReservedKeys m [(fiber, token)]) (sites : raceSites code = []) :
    GuardQueue p table m (commands ++ [.resume fiber token code]) := by
  constructor
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact queue.authority c hc
    · obtain rfl := List.mem_singleton.mp hc; trivial
  · simpa only [List.filterMap_append, List.filterMap_cons, commandOwner,
      List.filterMap_nil, List.append_nil] using queue.owners
  · simpa only [List.flatMap_append, List.flatMap_cons, commandKeys,
      List.flatMap_nil, List.append_nil] using reservedKeys_append queue.keys reserved
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact queue.codeSites c hc
    · obtain rfl := List.mem_singleton.mp hc; exact sites

theorem reservedKeys_race {m : NativeMachine} (state : GuardState m)
    {race : NRace} (hr : race ∈ m.races) : ReservedKeys m [(race.host, race.token)] := by
  apply reservedKeys_subset (reservedKeys_internal m state)
  intro key hk
  obtain rfl := List.mem_singleton.mp hk
  rw [internalKeys_store_decomposition]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨race, hr, rfl⟩))



end Effect4.Program.Guard
