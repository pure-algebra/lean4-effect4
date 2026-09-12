import Effect4.Laws.Program.Guard.Core

/-! Single-fiber guard equality, internal proof support only.
Proof graph: singleton GuardState -> Held -> inert command/store/dispatcher steps
-> raw non-cancellation decision -> finite tape-prefix induction.
The recorded interrupt cause and deferred-interrupt flag are unrestricted.
-/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace Effect4.Program.Guard.SingleGuard
open Effect4 Effect4.Machine Effect4.Program

/-- Every available fiber has the protected identity and remains on its guard. -/
def Only (m : NativeMachine) (fiber : FiberId) (token : Nat) : Prop :=
  ∀ f ∈ m.fibers, f.id = fiber ∧ f.parked = .withGuard token

/-- A smaller internal invariant; its premises follow from the dispatched contract. -/
structure Held (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) : Prop where
  only : Only m fiber token
  request : requestOf m fiber token = some request
  key : (fiber, token) ∉ internalKeys m

def QuietCmd (fiber : FiberId) (token : Nat) : NCmd → Prop
  | .evaluate _ | .drainDue | .wake _ _ => True
  | .resume target offered _ => (target, offered) ≠ (fiber, token)
  | _ => False

def QuietQueue (fiber : FiberId) (token : Nat) (commands : List NCmd) : Prop :=
  ∀ c ∈ commands, QuietCmd fiber token c

def NoCancel : NativeDecision → Prop
  | .interruptFrom _ _ _ => False
  | _ => True

theorem held_of_singleton {m : NativeMachine} {f : NFiber} {fiber : FiberId}
    {token : Nat} {request : NativeOp × Val} (state : GuardState m)
    (single : m.fibers = [f]) (hr : requestOf m fiber token = some request) :
    Held m fiber token request := by
  obtain ⟨g, hg, hpark, _⟩ := requestOf_shape hr
  have hmem := List.mem_of_find?_eq_some hg
  rw [single] at hmem
  have he : g = f := List.mem_singleton.mp hmem
  subst g
  refine ⟨?_, hr, state.requestsOwned fiber token request hr⟩
  intro g hmem
  rw [single] at hmem
  have he : g = f := List.mem_singleton.mp hmem
  subst g
  exact ⟨fiber_id_of_lookup hg, hpark⟩

theorem only_update {m : NativeMachine} {fiber : FiberId} {token : Nat}
    (h : Only m fiber token) (g : NFiber)
    (hg : g.id = fiber ∧ g.parked = .withGuard token) : Only (m.update g) fiber token :=
  update_all m g _ h hg

theorem held_update_view {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request)
    {f : NFiber} (hf : m.fiber? f.id = some f) (g : NFiber) (view : RequestView f g)
    (keys : fiberKeys g ⊆ internalKeys m) : Held (m.update g) fiber token request := by
  have old := h.only f (List.mem_of_find?_eq_some hf)
  refine ⟨only_update h.only g ⟨view.1.symm.trans old.1, view.2.1.symm.trans old.2⟩,
    (requestOf_update_view hf g view fiber token).trans h.request, ?_⟩
  intro hk
  have hk := internalKeys_update_add m g [] (by simpa using keys) hk
  exact h.key (by simpa using hk)

theorem held_same_fields {m n : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request)
    (fibers : n.fibers = m.fibers) (keys : internalKeys n ⊆ internalKeys m) :
    Held n fiber token request := by
  refine ⟨?_, ?_, fun hk => h.key (keys hk)⟩
  · intro f hf; exact h.only f (fibers ▸ hf)
  · have he : n.fiber? fiber = m.fiber? fiber := by simp only [RunMachine.fiber?, fibers]
    exact (requestOf_eq_of_fiber_eq fiber token he).trans h.request

theorem held_emit {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request) (events) :
    Held (m.emit events) fiber token request := ⟨h.only, h.request, h.key⟩

theorem held_disarm {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request) (owner : FiberId) :
    Held (m.disarm owner) fiber token request := ⟨h.only, h.request, h.key⟩

theorem held_withState {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request) (stores : Stores)
    (keys : storeKeys stores ⊆ storeKeys m.state) : Held { m with state := stores } fiber token request :=
  held_same_fields h rfl (internalKeys_state_subset m stores keys)

theorem held_postTask {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request)
    (owner : FiberId) (priority : Nat) (task : NTask)
    (safe : (fiber, token) ∉ taskKeys task) :
    Held (m.postTask owner priority task) fiber token request := by
  refine ⟨?_, (requestOf_postTask m owner priority task fiber token).trans h.request, ?_⟩
  · unfold RunMachine.postTask
    cases ho : m.fiber? owner with
    | none => exact h.only
    | some f =>
      exact only_update h.only _ (h.only f (List.mem_of_find?_eq_some ho))
  · intro hk
    rcases List.mem_append.mp (internalKeys_postTask_subset m owner priority task hk) with hk | hk
    · exact h.key hk
    · exact safe hk

theorem held_drainOwed {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (h : Held m fiber token request)
    (due : List (Owed NCode))
    (safe : ∀ owed ∈ due, (owed.waiter, owed.token) ≠ (fiber, token)) :
    Held (drainOwed m due).1 fiber token request ∧
      QuietQueue fiber token (drainOwed m due).2 := by
  induction due generalizing m with
  | nil => exact ⟨h, fun c hc => by cases hc⟩
  | cons owed due ih =>
    have head := safe owed (List.mem_cons_self ..)
    have tail := fun d hd => safe d (List.mem_cons_of_mem _ hd)
    cases hm : owed.mode with
    | now =>
      simp only [drainOwed, hm]
      have next := ih h tail
      refine ⟨next.1, ?_⟩
      intro c hc
      change c ∈ .resume owed.waiter owed.token owed.code :: (drainOwed m due).2 at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact head
      · exact next.2 c hc
    | scheduled owner priority =>
      have hp := held_postTask h owner priority (.resume owed.waiter owed.token owed.code)
        (by simpa only [taskKeys, List.mem_singleton] using Ne.symm head)
      simpa only [drainOwed, hm] using ih hp tail

theorem evaluate_inert (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} (h : Only m fiber token) (target : FiberId) (rest : List NCmd) :
    letI := evaluatorFor p table
    driveStep (interpOf p table) m (.evaluate target) rest = (m, rest) := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simp only [driveStep, hf]
  | some f =>
    have hp := (h f (List.mem_of_find?_eq_some hf)).2
    simp [driveStep, hf, hp]

theorem resume_inert (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} (h : Only m fiber token) (target : FiberId)
    (offered : Nat) (code : NCode) (rest : List NCmd)
    (safe : (target, offered) ≠ (fiber, token)) :
    letI := evaluatorFor p table
    driveStep (interpOf p table) m (.resume target offered code) rest = (m, rest) := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simp only [driveStep, hf]
  | some f =>
    have ho := h f (List.mem_of_find?_eq_some hf)
    have hid : target = fiber := (fiber_id_of_lookup hf).symm.trans ho.1
    have ht : token ≠ offered := by
      intro ht
      exact safe (Prod.ext hid ht.symm)
    simp only [driveStep, hf, ho.2, ht, ↓reduceIte]

theorem held_driveStep (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (cmd : NCmd) (rest : List NCmd)
    (quiet : QuietCmd fiber token cmd) (queue : QuietQueue fiber token rest) :
    letI := evaluatorFor p table
    Held (driveStep (interpOf p table) m cmd rest).1 fiber token request ∧
      QuietQueue fiber token (driveStep (interpOf p table) m cmd rest).2 := by
  letI := evaluatorFor p table
  cases cmd <;> simp only [QuietCmd] at quiet
  all_goals try contradiction
  case evaluate target => rw [evaluate_inert p table h.only]; exact ⟨h, queue⟩
  case resume target offered code => rw [resume_inert p table h.only target offered code rest quiet]; exact ⟨h, queue⟩
  case wake key phase => exact ⟨held_withState h _ (wakeList_storeKeys m.state key phase), queue⟩
  case drainDue =>
    let stores := ((interpOf p table).dueResumes m.state).2
    let due := ((interpOf p table).dueResumes m.state).1
    have hs : Held { m with state := stores } fiber token request := by
      apply held_same_fields (n := { m with state := stores }) h rfl
      intro key hk
      exact (dueResumes_keys_iff p table m key).mp (List.mem_append_left _ hk)
    have safe : ∀ owed ∈ due, (owed.waiter, owed.token) ≠ (fiber, token) := by
      intro owed ho he
      apply h.key
      apply (dueResumes_keys_iff p table m (fiber, token)).mp
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨owed, ho, he⟩
    have next := held_drainOwed hs due safe
    refine ⟨next.1, ?_⟩
    intro c hc
    change c ∈ (drainOwed { m with state := stores } due).2 ++ rest at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact next.2 c hc
    · exact queue c hc

theorem held_driveState (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (commands : List NCmd) (quiet : QuietQueue fiber token commands) :
    letI := evaluatorFor p table
    Held (driveState (interpOf p table) fuel m commands).1 fiber token request ∧
      QuietQueue fiber token (driveState (interpOf p table) fuel m commands).2 := by
  letI := evaluatorFor p table
  induction fuel generalizing m commands with
  | zero => exact ⟨h, quiet⟩
  | succ fuel ih =>
    cases commands with
    | nil => exact ⟨h, quiet⟩
    | cons c rest =>
      simp only [driveState]
      split
      · exact ⟨h, quiet⟩
      · have step := held_driveStep p table h c rest (quiet c (List.mem_cons_self ..))
          (fun c hc => quiet c (List.mem_cons_of_mem _ hc))
        exact ih step.1 _ step.2

theorem quiet_taskCmds {fiber : FiberId} {token : Nat} (task : NTask)
    (safe : (fiber, token) ∉ taskKeys task) : QuietQueue fiber token (taskCmds task) := by
  cases task <;> simp_all [taskCmds, QuietQueue, QuietCmd, taskKeys, Ne.symm]

theorem held_fireStep (p : NativeEff) (table : RowTable) (fuel : Nat) (owner : FiberId)
    (acc : NativeMachine × Bool) {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held acc.1 fiber token request) (task : NTask) (safe : (fiber, token) ∉ taskKeys task) :
    letI := evaluatorFor p table
    Held (fireStep (interpOf p table) fuel owner acc task).1 fiber token request := by
  letI := evaluatorFor p table
  unfold fireStep
  split
  · exact (held_driveState p table fuel (held_emit h [.ranTask owner task]) (taskCmds task) (quiet_taskCmds task safe)).1
  · exact h

theorem held_fireFold (p : NativeEff) (table : RowTable) (fuel : Nat) (owner : FiberId)
    (tasks : List NTask) (acc : NativeMachine × Bool)
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held acc.1 fiber token request)
    (safe : ∀ task ∈ tasks, (fiber, token) ∉ taskKeys task) :
    letI := evaluatorFor p table
    Held (tasks.foldl (fireStep (interpOf p table) fuel owner) acc).1 fiber token request := by
  letI := evaluatorFor p table
  induction tasks generalizing acc with
  | nil => exact h
  | cons task tasks ih =>
    exact ih _ (held_fireStep p table fuel owner acc h task (safe task (List.mem_cons_self ..)))
      (fun task ht => safe task (List.mem_cons_of_mem _ ht))

theorem held_fireState (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (owner : FiberId) :
    letI := evaluatorFor p table
    Held (fireState (interpOf p table) fuel m owner).1 fiber token request := by
  letI := evaluatorFor p table
  unfold fireState
  cases hf : m.fiber? owner with
  | none => exact h
  | some f =>
    have memf := List.mem_of_find?_eq_some hf
    have self : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    have hp : Held (m.update { f with dispatcher := f.dispatcher.drain.2 }) fiber token request := by
      apply held_update_view h self { f with dispatcher := f.dispatcher.drain.2 } ⟨rfl, rfl, rfl⟩
      intro key hk
      have hobs : key ∈ f.observers.flatMap observerKeys := by
        simpa only [fiberKeys, bucketKeys, Dispatcher.drain, List.flatMap_nil, List.append_nil] using hk
      exact internalKeys_fiber memf (List.mem_append_left _ hobs)
    apply held_fireFold p table fuel owner _ _ (held_disarm hp owner)
    intro task ht hk
    apply h.key
    apply internalKeys_fiber memf
    apply List.mem_append_right
    obtain ⟨tasks, htasks, ht⟩ := List.mem_flatten.mp ht
    obtain ⟨bucket, hb, rfl⟩ := List.mem_map.mp htasks
    exact List.mem_flatMap.mpr ⟨bucket, hb, List.mem_flatMap.mpr ⟨task, ht, hk⟩⟩

theorem held_flushAllState (p : NativeEff) (table : RowTable) (fuel rounds : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) :
    letI := evaluatorFor p table
    Held (flushAllState (interpOf p table) fuel rounds m).1 fiber token request := by
  letI := evaluatorFor p table
  induction rounds generalizing m with
  | zero => exact h
  | succ rounds ih =>
    simp only [flushAllState]
    split
    · exact h
    · split
      · exact h
      · split
        · exact ih (held_fireState p table fuel h _)
        · exact held_fireState p table fuel h _

theorem timer_fireNext_keys (timers : TimerStore) (target : Nat) (code : Effect4.Machine.Program) :
    wakeKeys (timers.fireNext target code).2.wake ⊆ wakeKeys timers.wake := by
  cases hd : TimerStore.dueMin target timers.wake.waiters with
  | none => simp only [TimerStore.fireNext_none timers target code hd]; exact List.Subset.refl _
  | some chosen =>
    simp only [TimerStore.fireNext, WakeList.wakeBy, hd]
    intro key hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
      exact List.mem_append_left _ (List.mem_map.mpr ⟨w, List.mem_of_mem_erase hw, rfl⟩)
    · exact List.mem_append_right _ hk

theorem timer_clockStep_keys (timers : TimerStore) (millis : Nat) (code : Effect4.Machine.Program) :
    wakeKeys (timers.clockStep millis code).2.wake ⊆ wakeKeys timers.wake := by
  have hs := timer_fireNext_keys timers (timers.target.getD (timers.now + millis)) code
  unfold TimerStore.clockStep
  cases hc : timers.fireNext (timers.target.getD (timers.now + millis)) code with
  | mk owed after =>
    rw [hc] at hs
    cases owed <;> simpa only [hc] using hs

theorem clockStep_storeKeys (p : NativeEff) (table : RowTable) (stores : Stores) (millis : Nat) :
    storeKeys ((interpOf p table).clockStep millis stores).2 ⊆ storeKeys stores := by
  change storeKeys { stores with timers := (stores.timers.clockStep millis (Prim.success Val.unit)).2 } ⊆ _
  exact storeKeys_mono (timer_clockStep_keys stores.timers millis (Prim.success Val.unit)) (List.Subset.refl _)

theorem clockStep_owed_safe (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (millis : Nat) (owed : Owed NCode)
    (ho : ((interpOf p table).clockStep millis m.state).1 = some owed) :
    (owed.waiter, owed.token) ≠ (fiber, token) := by
  have hk : (owed.waiter, owed.token) ∈ wakeKeys m.state.timers.wake := by
    change ((m.state.timers.clockStep millis (Prim.success Val.unit)).1.map
      (Owed.mapCode embed)) = some owed at ho
    obtain ⟨o, he, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact timer_clockStep_key _ millis (Prim.success Val.unit) o he
  intro he
  apply h.key
  simp only [internalKeys, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (he ▸ hk))))

theorem held_advanceState (p : NativeEff) (table : RowTable) (fuel millis rounds : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) :
    letI := evaluatorFor p table
    Held (advanceState (interpOf p table) fuel millis rounds m).1 fiber token request := by
  letI := evaluatorFor p table
  induction rounds generalizing m with
  | zero => exact h
  | succ rounds ih =>
    simp only [advanceState]
    split
    · exact h
    · cases hc : (interpOf p table).clockStep millis m.state with
      | mk owed stores =>
        have hs : Held { m with state := stores } fiber token request := by
          apply held_withState h stores
          have hk := clockStep_storeKeys p table m.state millis
          simpa only [hc] using hk
        cases owed with
        | none => exact hs
        | some owed =>
          dsimp only
          have safe := clockStep_owed_safe p table h millis owed (by rw [hc])
          have drained := held_drainOwed hs [owed] (by
            intro d hd
            have he : d = owed := List.mem_singleton.mp hd
            exact he ▸ safe)
          have driven := held_driveState p table fuel drained.1
            ((drainOwed { m with state := stores } [owed]).2 ++ [.drainDue]) (by
              intro c hc
              rcases List.mem_append.mp hc with hc | hc
              · exact drained.2 c hc
              · have he : c = .drainDue := List.mem_singleton.mp hc
                exact he ▸ True.intro)
          split
          · have flushed := held_flushAllState p table fuel fuel driven.1
            split
            · exact ih flushed
            · exact flushed
          · exact driven.1

theorem held_prepareAsyncAnswer (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (target : FiberId) (offered : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    Held { m with state := (prepareAsyncAnswer (interpOf p table) m target offered answer).1 }
      fiber token request := by
  refine ⟨h.only, h.request, ?_⟩
  have hk : internalKeys { m with state :=
      (prepareAsyncAnswer (interpOf p table) m target offered answer).1 } = internalKeys m := by
    unfold prepareAsyncAnswer
    split
    · rfl
    · exact internalKeys_prepareExternalAnswer m table _ answer
  rw [hk]
  exact h.key

theorem held_yieldVerdict (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (target : FiberId) (verdict : Bool) :
    Held (steppedBy p fuel table m (.yieldVerdict target verdict)) fiber token request := by
  change Held (m.modify target fun f => { f with yieldOverride := some verdict }) fiber token request
  unfold RunMachine.modify
  cases hf : m.fiber? target with
  | none => exact h
  | some f =>
    have self : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    exact held_update_view h self { f with yieldOverride := some verdict } ⟨rfl, rfl, rfl⟩
      (internalKeys_fiber (f := f) (List.mem_of_find?_eq_some hf))

theorem held_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (d : NativeDecision)
    (noCancel : NoCancel d) (otherAnswer : NotKeyAnswer fiber token d) :
    Held (steppedBy p fuel table m d) fiber token request := by
  cases d with
  | fire owner => exact held_fireState p table fuel h owner
  | flush => exact held_flushAllState p table fuel fuel h
  | evaluate target =>
    exact (held_driveState p table fuel h [.evaluate target, .drainDue] (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact True.intro)).1
  | yieldVerdict target verdict => exact held_yieldVerdict p table fuel h target verdict
  | answerAsync target offered answer =>
    have different := (notKeyAnswer_answer_iff fiber target token offered answer).mp otherAnswer
    have safe : (target, offered) ≠ (fiber, token) := by
      intro he
      rcases different with ht | hk
      · exact ht (Prod.mk.inj he).1
      · exact hk (Prod.mk.inj he).2
    cases fuel with
    | zero => exact h
    | succ fuel =>
      exact (held_driveState p table (fuel + 1) (held_prepareAsyncAnswer p table h target offered answer)
        [.resume target offered (prepareAsyncAnswer (interpOf p table) m target offered answer).2, .drainDue]
        (by
          intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact safe
          · exact True.intro)).1
  | interruptFrom who annotations target => exact False.elim noCancel
  | installMiddleware => exact ⟨h.only, h.request, h.key⟩
  | advance millis => exact held_advanceState p table fuel millis fuel h

/-- The exact dispatched internal equality clause. There is no cause, decision
admission, command-sufficiency, or additional public-law premise. -/
theorem requestOf_singleton_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {f : NFiber} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (state : GuardState m) (single : m.fibers = [f])
    (hr : requestOf m fiber token = some request) (d : NativeDecision)
    (noCancel : NoCancel d) (otherAnswer : NotKeyAnswer fiber token d) :
    requestOf (steppedBy p fuel table m d) fiber token = some request :=
  (held_steppedBy p table fuel (held_of_singleton state single hr) d noCancel otherAnswer).request

theorem noCancel_iff (d : NativeDecision) :
    NoCancel d ↔ ∀ who annotations target, d ≠ .interruptFrom who annotations target := by
  cases d <;> simp [NoCancel]

/-- Prefix entries retain their independent command budgets and raw decisions. -/
theorem held_executePrefix (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (history : Prefix)
    (safe : ∀ entry ∈ history, NoCancel entry.2 ∧ NotKeyAnswer fiber token entry.2) :
    Held (executePrefix p table m history) fiber token request := by
  induction history generalizing m with
  | nil => exact h
  | cons entry history ih =>
    have head := safe entry (List.mem_cons_self ..)
    exact ih (held_steppedBy p table entry.1 h entry.2 head.1 head.2)
      (fun entry he => safe entry (List.mem_cons_of_mem _ he))

theorem requestOf_singleton_executePrefix (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (state : GuardState m) (single : m.fibers = [f])
    (hr : requestOf m fiber token = some request) (history : Prefix)
    (safe : ∀ entry ∈ history, NoCancel entry.2 ∧ NotKeyAnswer fiber token entry.2) :
    requestOf (executePrefix p table m history) fiber token = some request :=
  (held_executePrefix p table (held_of_singleton state single hr) history safe).request

theorem requestOf_singleton_takePrefix (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (state : GuardState m) (single : m.fibers = [f])
    (hr : requestOf m fiber token = some request) (history : Prefix) (length : Nat)
    (safe : ∀ entry ∈ history, NoCancel entry.2 ∧ NotKeyAnswer fiber token entry.2) :
    requestOf (executePrefix p table m (history.take length)) fiber token = some request :=
  requestOf_singleton_executePrefix p table state single hr _
    (fun entry he => safe entry (List.mem_of_mem_take he))

end Effect4.Program.Guard.SingleGuard
