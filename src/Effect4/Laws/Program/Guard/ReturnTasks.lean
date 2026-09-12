import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Interruption

/-! Returned-fiber task and key bounds for guard preservation.
Proof graph: dispatcher insertion -> primitive/action branches -> native evaluation
-> iteration. Machine-state preservation and settling belong to their owners.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.ReturnTasks
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NAction := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx

def TaskCodes (f : NFiber) : Prop :=
  ∀ bucket ∈ f.dispatcher.buckets, ∀ task ∈ bucket.tasks, taskRaceSites task = []

/-- A new key must be accompanied by the exact fresh park. -/
structure Returned (m : NativeMachine) (f g : NFiber) : Prop where
  tasks : TaskCodes f → TaskCodes g
  keys : ∀ key ∈ fiberKeys g, key ∈ fiberKeys f ∨
    (key = (f.id, m.nextToken) ∧ g.parked = .withGuard m.nextToken)
  external : ∀ request, externalRequest g.frame.current = some request → fiberKeys g = fiberKeys f

theorem taskCodes_enqueue (f : NFiber) (priority : Nat) (task : NTask)
    (old : TaskCodes f) (sites : taskRaceSites task = []) :
    ∀ bucket ∈ (f.dispatcher.enqueue priority task).buckets,
      ∀ candidate ∈ bucket.tasks, taskRaceSites candidate = [] := by
  intro bucket hb candidate hc
  have hm : candidate ∈ (Dispatcher.insert priority task f.dispatcher.buckets).flatMap Bucket.tasks :=
    List.mem_flatMap.mpr ⟨bucket, hb, hc⟩
  rcases (dispatcher_insert_tasks priority task f.dispatcher.buckets candidate).mp hm with hm | he
  · obtain ⟨bucket, hb, hc⟩ := List.mem_flatMap.mp hm
    exact old bucket hb candidate hc
  · exact he ▸ sites

theorem bucketKeys_insert_empty (priority : Nat) (task : NTask) (buckets : List NBucket)
    (empty : taskKeys task = []) :
    bucketKeys (Dispatcher.insert priority task buckets) = bucketKeys buckets := by
  induction buckets with
  | nil => simp [Dispatcher.insert, bucketKeys, empty]
  | cons bucket buckets ih =>
    simp only [Dispatcher.insert]
    split
    · simp [bucketKeys, empty]
    · split
      · simp [bucketKeys, empty]
      · change _ ++ bucketKeys (Dispatcher.insert priority task buckets) = _
        rw [ih]
        rfl

theorem returned_same (m : NativeMachine) (f g : NFiber)
    (observers : g.observers = f.observers) (dispatcher : g.dispatcher = f.dispatcher) :
    Returned m f g := by
  have keys : fiberKeys g = fiberKeys f := by simp only [fiberKeys, observers, dispatcher]
  refine ⟨?_, ?_, fun _ _ => keys⟩
  · intro h; simpa only [TaskCodes, dispatcher] using h
  · intro key hk; exact Or.inl (keys ▸ hk)

theorem returned_start (m : NativeMachine) (f g : NFiber) (child : FiberId)
    (observers : g.observers = f.observers)
    (dispatcher : g.dispatcher = f.dispatcher.enqueue 0 (.start child)) : Returned m f g := by
  have keys : fiberKeys g = fiberKeys f := by
    simp only [fiberKeys, observers, dispatcher, Dispatcher.enqueue]
    rw [bucketKeys_insert_empty 0 (.start child) f.dispatcher.buckets rfl]
  refine ⟨?_, ?_, fun _ _ => keys⟩
  · intro h
    simpa only [TaskCodes, dispatcher] using taskCodes_enqueue f 0 (.start child) h rfl
  · intro key hk; exact Or.inl (keys ▸ hk)

theorem returned_yield (m : NativeMachine) (f g : NFiber) (priority : Nat) (value : Val)
    (observers : g.observers = f.observers)
    (dispatcher : g.dispatcher = f.dispatcher.enqueue priority (.resume f.id m.nextToken (.success value)))
    (parked : g.parked = .withGuard m.nextToken)
    (current : g.frame.current = .success value) : Returned m f g := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simpa only [TaskCodes, dispatcher] using
      taskCodes_enqueue f priority (.resume f.id m.nextToken (.success value)) h rfl
  · intro key hk
    simp only [fiberKeys, observers, dispatcher, Dispatcher.enqueue, List.mem_append] at hk
    rcases hk with ho | ht
    · exact Or.inl (List.mem_append_left _ ho)
    · rcases (bucketKeys_insert_mem priority (.resume f.id m.nextToken (.success value))
        f.dispatcher.buckets key).mp ht with old | fresh
      · exact Or.inl (List.mem_append_right _ old)
      · exact Or.inr ⟨List.mem_singleton.mp fresh, parked⟩
  · intro request h
    simp only [current, externalRequest] at h
    cases h

theorem stepFrame_returned (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Returned m f (evaluatePrim.stepFrame interp m f yielding).fiber := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact returned_same _ _ _ rfl rfl

theorem finalizerOr_returned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Returned m f (evaluatePrim.finalizerOr interp m f yielding exit).fiber := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact returned_same _ _ _ rfl rfl
      · exact stepFrame_returned _ _ _ _
    · exact stepFrame_returned _ _ _ _

theorem countdown_returned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Returned m f (countdownPark interp m f targets resumeWith failFast).2.1 := by
  unfold countdownPark
  dsimp only
  split <;> exact returned_same _ _ _ rfl rfl

theorem withFiber_returned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : NAction) :
    Returned m f (evaluatePrim.withFiber interp m f yielding action).fiber := by
  cases action <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start,
      beginRace]
  all_goals repeat' first
    | exact returned_same _ _ _ rfl rfl
    | exact returned_start _ _ _ _ rfl rfl
    | exact countdown_returned _ _ _ _ _ _
    | split
  all_goals simp_all

theorem evaluatePrim_returned (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Returned m f (evaluatePrim interp m f yielding).fiber := by
  simp only [evaluatePrim, registerRace, RunFiber.park]
  repeat' first
    | exact stepFrame_returned _ _ _ _
    | exact finalizerOr_returned _ _ _ _ _
    | exact withFiber_returned _ _ _ _ _
    | exact returned_same _ _ _ rfl rfl
    | exact returned_yield _ _ _ _ _ rfl rfl rfl rfl
    | exact countdown_returned _ _ _ _ _ _
    | split
  all_goals simp_all

theorem exitScoped_returned (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) : Returned m f (exitScoped p m f yielding exit).fiber := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_returned _ _ _ _
    | exact returned_same _ _ _ rfl rfl
    | split

theorem evaluateNative_returned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Returned m f (evaluateNative p m f yielding table).fiber := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_returned _ _ _ _
    | exact exitScoped_returned _ _ _ _ _
    | exact returned_same _ _ _ rfl rfl
    | split

theorem returned_rebase {m n : NativeMachine} {f before g : NFiber}
    (h : Returned n before g) (observers : before.observers = f.observers)
    (dispatcher : before.dispatcher = f.dispatcher) (id : before.id = f.id)
    (token : n.nextToken = m.nextToken) : Returned m f g := by
  have keys : fiberKeys before = fiberKeys f := by simp only [fiberKeys, observers, dispatcher]
  refine ⟨?_, ?_, fun request hr => (h.external request hr).trans keys⟩
  · intro tasks
    exact h.tasks (by simpa only [TaskCodes, dispatcher] using tasks)
  · intro key hk
    rcases h.keys key hk with old | fresh
    · exact Or.inl (keys ▸ old)
    · exact Or.inr ⟨by simpa only [id, token] using fresh.1,
        by simpa only [token] using fresh.2⟩

theorem runloopTop_dispatch (f : NFiber) :
    (runloopTop f).observers = f.observers ∧ (runloopTop f).dispatcher = f.dispatcher := by
  unfold runloopTop
  split <;> exact ⟨rfl, rfl⟩

theorem injectYield_dispatch (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.observers = f.observers ∧ it.fiber.dispatcher = f.dispatcher ∧
      it.machine.nextToken = m.nextToken := by
  unfold injectYield at h
  split at h
  · injection h with he
    subst it
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem iteration_returned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    Returned m f (iteration (interpOf p table) m f yielding).fiber := by
  letI := evaluatorFor p table
  have base := runloopTop_dispatch f
  have id := Effect4.Program.Guard.Interruption.runloopTop_id f
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    have h := evaluateNative_returned p table m (countOp (runloopTop f)) yielding
    have rebased := returned_rebase (m := m) (f := f) h base.1 base.2 id rfl
    simpa only [iteration, hi] using rebased
  | some it =>
    have fields := injectYield_dispatch m (countOp (runloopTop f)) yielding it hi
    have childId := Effect4.Program.Guard.Interruption.injectYield_id m (countOp (runloopTop f)) yielding it hi
    have h := evaluateNative_returned p table it.machine it.fiber it.yielding
    have rebased := returned_rebase (m := m) (f := f) h (fields.1.trans base.1)
      (fields.2.1.trans base.2) (childId.trans id) fields.2.2
    simpa only [iteration, hi] using rebased

/-- Native returned tasks retain the caller's race-site condition. -/
theorem evaluateNative_taskRaceSites (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (tasks : TaskCodes f) :
    ∀ bucket ∈ (evaluateNative p m f yielding table).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = [] :=
  (evaluateNative_returned p table m f yielding).tasks tasks

/-- The exact allocation witness needed to bound every new returned key. -/
theorem evaluateNative_fiberKeys_refined (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (key : GuardKey)
    (hk : key ∈ fiberKeys (evaluateNative p m f yielding table).fiber) :
    key ∈ fiberKeys f ∨ (key = (f.id, m.nextToken) ∧
      (evaluateNative p m f yielding table).fiber.parked = .withGuard m.nextToken) :=
  (evaluateNative_returned p table m f yielding).keys key hk

theorem evaluateNative_fiberKeys_subset (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    fiberKeys (evaluateNative p m f yielding table).fiber ⊆ fiberKeys f ++ [(f.id, m.nextToken)] := by
  intro key hk
  rcases evaluateNative_fiberKeys_refined p table m f yielding key hk with old | fresh
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (List.mem_singleton.mpr fresh.1)

theorem evaluateNative_external_fiberKeys (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (request : NativeOp × Val)
    (external : externalRequest (evaluateNative p m f yielding table).fiber.frame.current = some request) :
    fiberKeys (evaluateNative p m f yielding table).fiber = fiberKeys f :=
  (evaluateNative_returned p table m f yielding).external request external

theorem iteration_taskRaceSites (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (tasks : TaskCodes f) :
    letI := evaluatorFor p table
    ∀ bucket ∈ (iteration (interpOf p table) m f yielding).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = [] :=
  (iteration_returned p table m f yielding).tasks tasks

theorem iteration_fiberKeys_refined (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (key : GuardKey) :
    letI := evaluatorFor p table
    key ∈ fiberKeys (iteration (interpOf p table) m f yielding).fiber →
      key ∈ fiberKeys f ∨ (key = (f.id, m.nextToken) ∧
        (iteration (interpOf p table) m f yielding).fiber.parked = .withGuard m.nextToken) := by
  letI := evaluatorFor p table
  exact (iteration_returned p table m f yielding).keys key

theorem iteration_fiberKeys_subset (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    fiberKeys (iteration (interpOf p table) m f yielding).fiber ⊆ fiberKeys f ++ [(f.id, m.nextToken)] := by
  letI := evaluatorFor p table
  intro key hk
  rcases iteration_fiberKeys_refined p table m f yielding key hk with old | fresh
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (List.mem_singleton.mpr fresh.1)

theorem iteration_external_fiberKeys (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (request : NativeOp × Val) :
    letI := evaluatorFor p table
    externalRequest (iteration (interpOf p table) m f yielding).fiber.frame.current = some request →
      fiberKeys (iteration (interpOf p table) m f yielding).fiber = fiberKeys f := by
  letI := evaluatorFor p table
  exact (iteration_returned p table m f yielding).external request

end Effect4.Program.Guard.ReturnTasks
