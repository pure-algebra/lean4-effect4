import Effect4.Laws.Program.Typed.Commands.Race
import Effect4.Laws.Program.Handles.Evaluation

/-!
# Laws.Program.Typed.Edits — the decision edits over `J` and `I` (`M6Edits`)

Wave 2's fifth group (seat D3): the edits a decision makes outside the command loop
(`Machine/Fibers.lean:2111-2140`, `Machine.Lift.DecisionLift`'s fields), over the split's `J`
(`MachineTyped`), `I` (`ConfigTyped`) and the fire snapshot (`SnapshotTyped`).

* `yield` (`yieldVerdict`'s modify): a quiet edit of the override flag no clause reads.
* `interrupt` (`Machine.Lift.interruptEdit`): the interrupt record (`configTyped_interruptRecord`).
* `drain` (a `fire`'s drain and disarm): the owner's dispatcher emptied; its tasks become the
  snapshot, typed by the dispatcher's column (`TaskOk`), their keys the machine's internal ones.
* `clockNone` (an `advance` step that fires nothing): the timer store's clock moves; nothing any
  clause reads changes, and the timers stay well formed (`TimerStore.clockStep_wf`).
* `answer` (`prepareAsyncAnswer` and the `resume` it queues): the reference interpreter prepares
  nothing (`RunInterp.prepareAnswer`'s default), and the admission types the answer at a parked
  fiber's token (`AnswerOk`), which is what `resume_step` reads.

`clockSome` (an `advance` step that fires a sleep) is not proved here; seat D3's receipt records
why: the fired sleeper's `resume` carries `void`, and nothing in `J` types a timer's sleeper token
at a type `void` fits.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-- `J` with the empty residue is `I`. -/
theorem configTyped_nil {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) : ConfigTyped root rootTy w m [] :=
  ⟨typed, fun _ _ _ ⟨_, r⟩ => r.elim (fun h => nomatch h) (fun h => nomatch h),
    queueOk_nil root w m⟩

/-- `J` with the due drain queued is `I`. -/
theorem configTyped_drainDue {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) :
    ConfigTyped root rootTy w m (.drainDue :: q) :=
  configTyped_cons_plain typed _ trivial trivial trivial (fun _ h => nomatch h) trivial rfl
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)

/-! ## `yield` -/

/-- The verdict a `yieldVerdict` decision stores: a field no clause reads. -/
theorem quiet_yield (v : Bool) : QuietEdit (fun f : RFiber => { f with yieldOverride := some v }) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun f => ⟨[], (List.append_nil f.observers).symm, fun _ h => nomatch h⟩⟩

/-- **`yield` keeps `J`**: the override flag is no clause's. -/
theorem edit_yield (root : ProgramSource) (rootTy : EffTy) : EditYield root rootTy := by
  intro w m id v typed
  exact (configTyped_modify_quiet (configTyped_nil typed) id (quiet_yield v)
    (fun _ _ o ho => Or.inl ho)).machine

/-! ## `interrupt` -/

/-- **`interrupt` keeps `J`**: the decision's interrupt is the command's record
(`configTyped_interruptRecord`), after the events it emits. -/
theorem edit_interrupt (root : ProgramSource) (rootTy : EffTy) : EditInterrupt root rootTy := by
  intro w m who extra target t typed ht
  have e1 := configTyped_emit (configTyped_nil typed) [RunEvent.interruptRecorded who target]
  unfold Machine.Lift.interruptEdit
  dsimp only
  split
  · have e2 := configTyped_emit e1 [RunEvent.interruptDeferred target]
    exact (configTyped_interruptRecord e2 ht who extra).machine
  · exact (configTyped_interruptRecord e1 ht who extra).machine

/-! ## `answer` -/

/-- The reference interpreter prepares an answer as its completion's code, at the same store. -/
theorem prepareAsyncAnswer_running (root : ProgramSource) (m : RState) (id : FiberId)
    (token : Nat) (answer : Completion Val Err Defect FiberId Ann) (stuck : m.stuck = none) :
    prepareAsyncAnswer (interpR root.program) m id token answer =
      (m.state, denoteCompletion answer) := by
  unfold prepareAsyncAnswer
  rw [stuck]
  rfl

/-- **`answer` keeps `J` and `I`** at the same world: a parked fiber's resume is typed by the
admission (`AnswerOk` and `denoteCompletion_typed`) and runs as the command (`resume_step`); an
inert one leaves the machine and the due drain. -/
theorem edit_answer (root : ProgramSource) (rootTy : EffTy) : EditAnswer root rootTy := by
  intro w m id token answer typed stuck admitted
  rw [prepareAsyncAnswer_running root m id token answer stuck]
  refine ⟨w, leHost_refl w, ?_⟩
  have rest : ConfigTyped root rootTy w { m with state := m.state } [Cmd.drainDue] :=
    configTyped_drainDue (configTyped_nil typed)
  have after := resume_step rest (id := id) (token := token) (answer := denoteCompletion answer)
    fun parked ty declared => by
      obtain ⟨ty', declared', strong⟩ := admitted parked
      rw [declared'] at declared
      cases declared
      exact denoteCompletion_typed root strong
  exact ⟨after.machine, fun _ => ⟨after, queueOk_nil root w _⟩⟩

/-! ## `drain` -/

/-- A fiber edit that keeps the fiber's park and current code keeps every request. -/
theorem requestOfR_update_flags {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (parked : g.parked = f.parked) (current : g.frame.current = f.frame.current)
    (fiber : FiberId) (token : Nat) : requestOfR (m.update g) fiber token = requestOfR m fiber token := by
  by_cases same : fiber = g.id
  · subst same
    have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf hid
    have hf' : m.fiber? g.id = some f := by rw [hid]; exact hf
    by_cases hp : g.parked = .withGuard token
    · rw [requestOfR_of_parked look hp, requestOfR_of_parked hf' (parked ▸ hp), current]
    · rw [requestOfR_of_not_parked look hp,
        requestOfR_of_not_parked hf' (fun h => hp (parked.trans h))]
  · exact requestOfR_congr (rfiber?_update_other same) token

/-- A command list whose every command has a trivial registration tail is a registration
queue. -/
theorem registrationQueue_of_tails {l : List RCmd}
    (h : ∀ c ∈ l, ∀ rest, Guard.RegistrationQueue.RegistrationTail c rest) :
    Guard.RegistrationQueue.RegistrationQueue l := by
  induction l with
  | nil => trivial
  | cons c rest ih =>
    exact ⟨h c List.mem_cons_self rest, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')⟩

/-- A drained task sits in one of the dispatcher's buckets. -/
theorem mem_drain {d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram}
    {task : RTask} (h : task ∈ d.drain.1) : ∃ b ∈ d.buckets, task ∈ b.tasks := by
  obtain ⟨tasks, hl, ht⟩ := List.mem_flatten.mp h
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hl
  exact ⟨b, hb, ht⟩

/-- **The snapshot a drain hands the fire is typed**: every task's command is typed by the
dispatcher's column (`TaskOk`: a resume's answer at its token), and its key is one of the
dispatcher's, below the token counter and requested by no park. -/
theorem snapshotTyped_drain {root : ProgramSource} {w : World} {m : RState}
    {d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram}
    (ok : DispatcherOk (preds root) w Expect.root d)
    (keysBelow : ∀ k ∈ Guard.bucketKeys d.buckets, k.2 < m.nextToken)
    (keysFree : ∀ fiber token r, requestOfR m fiber token = some r →
      (fiber, token) ∉ Guard.bucketKeys d.buckets) :
    SnapshotTyped root w m d.drain.1 := by
  have keysOf : ∀ key ∈ (d.drain.1.flatMap taskCmds).flatMap Guard.commandKeys,
      key ∈ Guard.bucketKeys d.buckets := by
    intro key hk
    obtain ⟨c, hc, hkc⟩ := List.mem_flatMap.mp hk
    obtain ⟨task, ht, hct⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, htb⟩ := mem_drain ht
    have inBucket : ∀ k ∈ Guard.taskKeys task, k ∈ Guard.bucketKeys d.buckets := fun k hk' =>
      List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨task, htb, hk'⟩⟩
    cases task with
    | start child =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl <;> cases hkc
    | resume target token code =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl
      · exact inBucket key hkc
      · cases hkc
    | wake list phase =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl <;> cases hkc
  refine
    { payload := fun c hc => ?_
      authority := fun c hc => ?_
      delivery := fun c hc => ?_
      owners := ?_
      registration := registrationQueue_of_tails fun c hc rest => taskCmd_tail hc rest
      keys := ⟨fun key hk => keysBelow key (keysOf key hk),
        fun fiber token r hr hk => keysFree fiber token r hr (keysOf _ hk)⟩
      observer := fun source exit observer h => ?_
      enroll := fun race child h => ?_
      noRaceAfterInterrupt := fun host yielding race h => ?_
      links := fun mode scope target interruptor extra h =>
        absurd rfl (taskCmd_not_link h mode scope target interruptor extra) }
  · obtain ⟨task, ht, hct⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, htb⟩ := mem_drain ht
    have taskOk := (ok.c0 b hb).c0 task htb
    cases task with
    | start child =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl <;> trivial
    | resume target token code =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl
      · exact taskOk
      · trivial
    | wake list phase =>
      simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hct
      rcases hct with rfl | rfl <;> trivial
  · rcases mem_taskCmds hc with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> trivial
  · rcases mem_taskCmds hc with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> trivial
  · rw [List.filterMap_eq_nil_iff.mpr fun _ member => taskCmd_owner m member]
    exact List.nodup_nil
  · rcases mem_taskCmds h with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ | h' <;> exact nomatch h'
  · rcases mem_taskCmds h with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ | h' <;> exact nomatch h'
  · rcases mem_taskCmds h with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ | h' <;> exact nomatch h'

/-- **`drain` keeps `J` and types the snapshot**: the owner's dispatcher is emptied (its column
holds over the empty bucket list) and disarmed; its tasks, typed by the column, are the snapshot. -/
theorem edit_drain (root : ProgramSource) (rootTy : EffTy) : EditDrain root rootTy := by
  intro w m owner f typed found
  have fid : f.id = owner := rfiber?_id found
  have hf : m.fiber? f.id = some f := by rw [fid]; exact found
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have wide := typed.wide
  have old := typed.fiber hmem
  let g : RFiber := { f with dispatcher := (f.dispatcher.drain).2 }
  have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w (m.update g) g :=
    { ok := ⟨moved.ok.c0, moved.ok.c1, moved.ok.c2, moved.ok.c3, ⟨fun _ h => nomatch h⟩,
        moved.ok.c5⟩
      delivery := moved.delivery
      below := moved.below
      pendingShape := moved.pendingShape
      parkedIdle := moved.parkedIdle
      parkedBelow := moved.parkedBelow
      exited := moved.exited
      deferredCause := moved.deferredCause
      pendingOwner := moved.pendingOwner
      observers := moved.observers
      registration := moved.registration
      code := moved.code
      tokens := moved.tokens }
  have bucketsIn : ∀ k ∈ Guard.bucketKeys f.dispatcher.buckets, k ∈ Guard.internalKeys m :=
    fun k hk => fiberKeys_internal hmem (List.mem_append_right _ hk)
  have keysG : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none) := by
    intro k hk
    rcases List.mem_append.mp hk with obs | buckets
    · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _ obs))
    · exact nomatch buckets
  have edited := configTyped_rupdate (g := g) (configTyped_nil typed) hf rfl (PendingWeaker.refl _)
    rfl rfl rfl rfl rfl (fun p => p) keysG fresh
  refine ⟨machineTyped_congr (m := m.update g) (m' := (m.update g).disarm owner) rfl rfl rfl rfl
    rfl rfl rfl edited.machine, ?_⟩
  refine snapshotTyped_drain old.ok.c4 (fun k hk => wide.keysBelow k (bucketsIn k hk)) ?_
  intro fiber token r hr hk
  have before : requestOfR m fiber token = some r := by
    have same := requestOfR_update_flags (m := m) (g := g) hf rfl rfl rfl fiber token
    rw [← same]
    exact hr
  exact wide.requestsOwned fiber token r before (bucketsIn _ hk)

/-! ## `clockNone` -/

/-- A store whose timers alone changed, to a well-formed timer store, is well-formed. -/
theorem wf_retime {t : Stores} (wf : t.WF) (timers : TimerStore) (htimers : timers.WF) :
    ({ t with timers := timers } : Stores).WF := by
  obtain ⟨hrefs, hscopes, hmemo, _⟩ := wf
  have le : t.le { t with timers := timers } := Stores.le_refl t
  refine ⟨fun v hv => Val.validIn_mono le v (hrefs v hv), fun e he => ?_, hmemo, htimers⟩
  have old := hscopes e he
  cases hc : e.scope.closingExit? with
  | none => rfl
  | some ex =>
    rw [hc] at old
    exact Val.validIn_mono le _ old

/-- **`clockNone` keeps `J`**, at the world over the advanced store: a clock step that fires no
sleep moves the clock alone (`TimerStore.clockStep_finish`), so the sleepers, every typed column
and every internal key are the old ones, and the timers stay well formed
(`TimerStore.clockStep_wf`). -/
theorem edit_clockNone (root : ProgramSource) (rootTy : EffTy) : EditClockNone root rootTy := by
  intro w m millis st typed _ step
  have wide := typed.wide
  have step' : (Option.map (Owed.mapCode denoteCompletion)
        (m.state.timers.clockStep millis
          (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).1,
      { m.state with timers := (m.state.timers.clockStep millis
          (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).2 }) =
      (none, st) := step
  rw [Prod.mk.injEq] at step'
  obtain ⟨fired, rfl⟩ := step'
  have noOwed : (m.state.timers.clockStep millis
      (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).1 = none :=
    Option.map_eq_none_iff.mp fired
  have wake : (m.state.timers.clockStep millis
      (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).2.wake =
      m.state.timers.wake := by
    cases h : TimerStore.dueMin (m.state.timers.target.getD (m.state.timers.now + millis))
        m.state.timers.wake.waiters with
    | none => rw [TimerStore.clockStep_finish _ millis _ h]
    | some x =>
      exfalso
      have owed := (TimerStore.fireNext_now m.state.timers _
        (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann) x h).1
      revert noOwed
      unfold TimerStore.clockStep
      dsimp only
      rcases hpair : m.state.timers.fireNext (m.state.timers.target.getD (m.state.timers.now + millis))
        (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)
        with ⟨fired', s'⟩
      rw [hpair] at owed
      cases fired' with
      | none => cases owed
      | some o =>
        dsimp only
        intro hnone
        cases hnone
  let T : TimerStore := (m.state.timers.clockStep millis
    (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).2
  have wf : ({ m.state with timers := T } : Stores).WF :=
    wf_retime wide.wf T (TimerStore.clockStep_wf wide.wf.2.2.2 millis
      (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann))
  have le : m.state.le { m.state with timers := T } := Stores.le_refl m.state
  have ord : w.leHost { w with state := { m.state with timers := T } } := by
    apply leHost_restate
    · rw [wide.state]
      exact le
    · rw [wide.state]
    · rw [wide.state]
    · rw [wide.state]
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
  have keys : Guard.internalKeys ({ m with state := { m.state with timers := T } } : RState) ⊆
      Guard.internalKeys m := by
    intro k hk
    rw [internalKeys_fibers] at hk ⊢
    have e : (({ m with state := { m.state with timers := T } } : RState).state.timers.wake) =
        m.state.timers.wake := wake
    rw [e] at hk
    exact hk
  obtain ⟨_, restated⟩ := configTyped_restate (s := { m.state with timers := T })
    (configTyped_nil typed) le rfl rfl rfl wf ⟨c0, c1, c2, c3, c4, c5⟩ keys wide.live.dueOwners
  exact ⟨_, ord, restated.machine⟩

/-! ## M6b from what remains

Five of the six edits are proved above. `DecisionKeeps` (`M6Ledger.decision_preserves`) follows
from the eighteen command facts and the sixth edit through the lift (`decisionKeeps_of_ledger`);
these two theorems state exactly that, so the goal closes by one line when its premises do. -/

/-- The six edits from the one this module does not prove. -/
theorem decisionEdits_of_clockSome (root : ProgramSource) (rootTy : EffTy)
    (clockSome : EditClockSome root rootTy) : DecisionEdits root rootTy :=
  { drain := edit_drain root rootTy
    yield := edit_yield root rootTy
    interrupt := edit_interrupt root rootTy
    clockNone := edit_clockNone root rootTy
    clockSome := clockSome
    answer := edit_answer root rootTy }

/-- **M6b from the eighteen command facts and the clock's firing edit**: the other five edits are
proved here, and the lift (`decisionKeeps_of_ledger`, `Machine.Lift.stepDecisionState_lift`) does
the rest. -/
theorem decisionKeeps_of_steps (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (steps : ∀ command, StepPreserves root rootTy command) (clockSome : EditClockSome root rootTy)
    (d : Api.Decision) : DecisionKeeps root rootTy fuel d :=
  decisionKeeps_of_ledger root rootTy fuel d steps (decisionEdits_of_clockSome root rootTy clockSome)

/-! ## M6c from what remains (step 6) -/

/-- **M6c from M5, the eighteen command facts and the clock's firing edit**: `reachable_of_ledger`
over `decisionKeeps_of_steps`, written as the proof it is, with the goals it consumes as
premises. -/
theorem typedState_reachable_of_steps (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadsTyped root rootTy fuel fuel) (steps : ∀ command, StepPreserves root rootTy command)
    (clockSome : EditClockSome root rootTy) (m : RState) : ReachableTyped root rootTy fuel m :=
  reachable_of_ledger root rootTy fuel load
    (fun d => decisionKeeps_of_steps root rootTy fuel steps clockSome d) m

/-! ## Exit handles from the native handle invariant (step 6, `M7.exitHandles_valid`)

The route the brief names second: the frame machine's handle invariant (`handles_minted`: every
collected handle exists) carried across `run_eq_ref`'s relation (`replay_rel`, `bookMeans_obs`:
the two replays record the same exits over the same stores). It reaches every handle `Val.keys`
collects, which are the frames whose kind byte is registered (`Val.keys_eq_handles`); `Val.validIn`
also refuses a frame with an unregistered byte, which no handle invariant of the tree speaks of.
So the goal follows from this route for exits whose frames are registered
(`exitHandles_valid_of_registered`), and the registered-byte fact is what remains. The route
through `J` reaches less: `Live`, the membership at `unknown`, checks no scope, memo or external
handle and no unregistered byte. -/

/-- Every handle frame of a value has a registered kind byte, so `Val.keys` sees every frame
`Val.validIn` checks. -/
def HandlesRegistered (v : Val) : Prop :=
  ∀ h ∈ Store.Val.handles v, (HandleKind.ofByte? h.1).isSome = true

/-- A value whose handle frames are registered and exist in a world is valid in the world's
store. -/
theorem validIn_of_ok {ids : List FiberId} {s : Stores} {v : Val} (registered : HandlesRegistered v)
    (ok : Machine.Ok ⟨ids, s⟩ v.keys) : v.validIn s = true := by
  rw [Val.validIn_eq_handles, List.all_eq_true]
  intro code hmem
  obtain ⟨kind, hkind⟩ := Option.isSome_iff_exists.mp (registered code hmem)
  have member : ∀ h, Handle.ofCode code = some h → h.existsIn ⟨ids, s⟩ = true := by
    intro h hh
    refine ok h ?_
    rw [Val.keys_eq_handles]
    exact List.mem_filterMap.mpr ⟨code, hmem, hh⟩
  unfold Stores.handleValid
  rw [hkind]
  cases kind with
  | fiber => rfl
  | cell =>
    have e := member (.cell ⟨code.2⟩) (by unfold Handle.ofCode; rw [hkind])
    exact e
  | promise =>
    have e := member (.promise ⟨code.2⟩) (by unfold Handle.ofCode; rw [hkind])
    exact e
  | scope =>
    have e := member (.scope code.2) (by unfold Handle.ofCode; rw [hkind])
    exact e
  | memoMap =>
    have e := member (.memoMap code.2) (by unfold Handle.ofCode; rw [hkind])
    exact e
  | external =>
    have e := member (.external code.2) (by unfold Handle.ofCode; rw [hkind])
    exact e

/-- A tape with no host answer meets the handle invariant's tape premise at every machine. -/
theorem answersValid_of_noHostAnswer (program : Api.Program) (fuel : Nat) :
    ∀ (tape : List Api.Decision), (∀ d ∈ tape, NoHostAnswer d) → ∀ m : Api.Machine,
      letI := evaluatorFor program
      AnswersValidAt (interpOf program) fuel tape m := by
  intro tape
  induction tape with
  | nil => intro _ m; rfl
  | cons d rest ih =>
    intro free m
    letI := evaluatorFor program
    show answersValid (interpOf program) fuel (d :: rest) m = true
    unfold answersValid
    cases hs : m.stuck with
    | some _ => rfl
    | none =>
      dsimp only
      have later := ih (fun d' hd' => free d' (List.mem_cons_of_mem _ hd'))
      cases d with
      | answerAsync _ _ _ => exact (free _ List.mem_cons_self).elim
      | _ =>
        dsimp only
        rw [Bool.true_and]
        split
        · exact later _
        · rfl

/-- **`M7.exitHandles_valid` for registered exits**: on the reference replay of an answer-free
tape, a recorded success's value whose handle frames are registered is valid in the stores, by
the frame machine's handle invariant (`handles_minted`) across `run_eq_ref`'s relation. -/
theorem exitHandles_valid_of_registered (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (m : RState)
    (registered : ∀ f ∈ m.fibers, ∀ v, f.exit = some (.success v) → HandlesRegistered v) :
    ExitHandlesValid root rootTy fuel m := by
  rintro _ _ _ ⟨tape, free, rfl⟩ f hf v hx
  have minted := handles_minted root.program fuel tape
    ⟨load_minted root.program fuel, answersValid_of_noHostAnswer root.program fuel tape free _⟩
  rw [replay_machine] at minted
  have rel := ReplayRel.machine (replay_rel root.program fuel fuel tape)
  have exits := bookMeans_exits rel
  have state := rel.state
  have member : (f.id, f.exit) ∈ (replayR root.program fuel tape).machine.fibers.map
      fun f => (f.id, f.exit) := List.mem_map_of_mem hf
  have member' : (f.id, f.exit) ∈ ((replayEval (evaluator := evaluatorFor root.program)
      (interpOf root.program) fuel tape (Api.load root.program fuel)).machine.fibers.map
        fun f => (f.id, f.exit)) := by
    rw [exits]
    exact member
  obtain ⟨g, hg, same⟩ := List.mem_map.mp member'
  obtain ⟨_, gx⟩ := Prod.mk.inj same
  rw [hx] at gx
  have ok : Machine.Ok (RunMachine.world (replayEval (evaluator := evaluatorFor root.program)
      (interpOf root.program) fuel tape (Api.load root.program fuel)).machine) v.keys := by
    intro h hh
    apply minted h
    unfold RunMachine.keys
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨g, hg, ?_⟩)))
    unfold RunFiber.keys
    rw [gx]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hh))))
  have valid := validIn_of_ok (registered f hf v hx) ok
  rw [state] at valid
  exact valid

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Edits.drain := @Effect4.Program.Typed.edit_drain
#obligation_proved Effect4.Program.Typed.M6Edits.yield := @Effect4.Program.Typed.edit_yield
#obligation_proved Effect4.Program.Typed.M6Edits.interrupt := @Effect4.Program.Typed.edit_interrupt
#obligation_proved Effect4.Program.Typed.M6Edits.clockNone := @Effect4.Program.Typed.edit_clockNone
#obligation_proved Effect4.Program.Typed.M6Edits.answer := @Effect4.Program.Typed.edit_answer
-- `M6Edits`' report moved here from `Assembly.lean`'s foot: this module sees the proofs.
#typed_state_obligations Effect4.Program.Typed.M6Edits ceiling 1
  using aesop (rule_sets := [Effect4.TypedState])
