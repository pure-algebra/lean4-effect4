import Effect4.Laws.Program.ReleaseCustody.CommandRaceDebit
import Effect4.Laws.Program.ReleaseCustody.ScopeTransfer
import Effect4.Laws.Machine.FiberSumMessages

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: actual scope-link, dispatcher and store command clauses of release custody.
These local bounds count existing scopes, stored task code and queued resumes.
They establish no history closure, source uniqueness or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.CommandDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control

/-- A store edit spends at most the foreign cleanup credit already held by its scopes. -/
theorem state (q : List Nat) (m : NativeMachine) (next : Stores) (commands : List Command)
    (held : Funded q m commands)
    (debit : ScopeTransfer.storedCredits q next.scopes ≤ ScopeTransfer.storedCredits q m.state.scopes) :
    Funded q {m with state := next} commands := by
  unfold Funded machineCredits at held ⊢
  unfold ScopeTransfer.storedCredits at debit
  dsimp only
  omega

/-- Addressed messages spend only stored fiber credit and emit zero-credit commands.
Consumer: actual scope-link command funding after its canonical plan. -/
theorem fiber_edits (q : List Nat) (m : NativeMachine)
    (edits : List (FiberEdit Err Defect FiberId Ann)) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup) (held : Funded q m rest) :
    Funded q (applyFiberEdits edits m).1 ((applyFiberEdits edits m).2 ++ rest) := by
  have bounded := (FiberSum.fiberEdits_le (fiberCredits q) (fun _ _ => rfl)
    (Evaluation.interrupt_fiber_le q) edits m unique).2
  have shape := RunMachine.applyFiberEdits_shape edits m
  have zero : ((applyFiberEdits edits m).2.map (commandCredits q)).sum = 0 := by
    have mapped : (applyFiberEdits edits m).2.map (commandCredits q) =
        List.replicate (applyFiberEdits edits m).2.length 0 := by
      apply List.map_eq_replicate_iff.mpr
      intro command member
      obtain ⟨id, rfl⟩ := shape.2 command member
      rfl
    rw [mapped, List.sum_replicate_nat, Nat.mul_zero]
  have trace := congrArg RunMachine.trace shape.1
  have stores := congrArg RunMachine.state shape.1
  have races := congrArg RunMachine.races shape.1
  unfold Funded machineCredits at held ⊢
  simp only [List.map_append, List.sum_append, zero, Nat.zero_add, trace, stores, races]
  unfold FiberSum.total at bounded
  omega

/-- Linking an existing fiber adds only administrative scope cleanup or interrupts that fiber. -/
theorem link_scope (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (held : Funded q m rest) :
    let out := linkScope (interpOf root table) m mode scope target who extra
    Funded q out.1 (out.2 ++ rest) := by
  let plan := linkScopeEdits (interpOf root table) m mode scope target who extra
  let Edge (before after : NativeMachine)
      (edit : Machine.Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode
        (FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
        (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) : Prop :=
    after = edit.apply before ∧ (Funded q before rest → Funded q after rest)
  have emitted (before : NativeMachine) (events)
      (release : events.countP (ReleaseTrace.releaseAt q) = 0)
      (registered : events.countP (ReleaseTrace.registeredAt q) = 0) :
      Edge before (before.emit events) (.emit events) :=
    ⟨rfl, fun funded => emit q before rest funded events release registered⟩
  have path := Edits.link_plan_path (Edge := Edge) (interpOf root table)
    mode scope target who m
    (fun next key result => ⟨rfl, fun funded => state q m next rest funded
      (Nat.le_of_eq (ScopeTransfer.link q mode scope target scopes fresh result))⟩)
    (fun before => emitted before [.scopeClosedOnLink scope target, .interruptRecorded who target] rfl rfl)
    (fun before key => emitted before [.scopeLinked mode scope key target] rfl rfl)
    (fun _ _ => ⟨rfl, fun funded => funded⟩) extra
  have funded : Funded q plan.1 rest := by
    rw [Edits.link_plan_word]
    exact Edits.run_preserves_at (fun _ _ _ edge => edge.1) (fun before => Funded q before rest)
      (fun _ _ _ edge => edge.2) path held
  have sameFibers : plan.1.fibers = m.fibers := by
    rw [Edits.link_plan_word]
    exact Edits.run_keeps _ _ (fun edit member => edit.keeps_fibers
      (Edits.link_misses _ m mode scope target who edit member)) m
  exact fiber_edits q plan.1 plan.2 rest (by rw [sameFibers]; exact fibers) funded

/-- Actual scope-link commands retain the same registration funding. -/
theorem link (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (held : Funded q m (.link mode scope target who extra :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.link mode scope target who extra) rest
    Funded q out.1 out.2 :=
  link_scope root table q m mode scope target who extra rest fibers scopes fresh (tail q m _ rest held)

/-- Inserting a zero-credit task retains the dispatcher's scalar credit. -/
theorem insert_zero (q : List Nat) (priority : Nat) (task : NTask) (zero : taskCredits q task = 0)
    (buckets : List (Bucket EffName EffThunk Val Err Defect FiberId Ann)) :
    ((Dispatcher.insert priority task buckets).map fun b => (b.tasks.map (taskCredits q)).sum).sum =
      (buckets.map fun b => (b.tasks.map (taskCredits q)).sum).sum := by
  induction buckets with
  | nil => simp only [Dispatcher.insert, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zero, Nat.add_zero]
  | cons bucket rest ih =>
    simp only [Dispatcher.insert]
    split
    · simp only [List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append,
        List.sum_nil, zero, Nat.add_zero]
    · split
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero, Nat.zero_add]
      · simp only [List.map_cons, List.sum_cons, ih]

/-- Posting an actual zero-credit task cannot increase machine credit. -/
theorem post_task (q : List Nat) (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) (zero : taskCredits q task = 0) (commands : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup) (held : Funded q m commands) :
    Funded q (m.postTask owner priority task) commands := by
  unfold RunMachine.postTask
  split
  · exact held
  · rename_i fiber found
    apply emit q _ _ _ _ rfl rfl
    change Funded q (m.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task}) commands
    apply update q m fiber {fiber with dispatcher := fiber.dispatcher.enqueue priority task}
      commands commands held unique (by simpa only [fiber_id_of_lookup found] using found) rfl
    simp only [fiberCredits, Dispatcher.enqueue, insert_zero q priority task zero]
    exact Nat.le_refl _

/-- Posting retains the stored identity list. -/
theorem post_task_ids (m : NativeMachine) (owner : FiberId) (priority : Nat) (task : NTask) :
    (m.postTask owner priority task).fibers.map RunFiber.id = m.fibers.map RunFiber.id := by
  unfold RunMachine.postTask
  split
  · rfl
  · exact RunMachine.update_keeps_ids _ _

/-- Draining native zero-credit replies transports them into commands or dispatcher tasks. -/
theorem drain_owed (q : List Nat) (m : NativeMachine) (due : List (Owed NCode))
    (rest : List Command) (unique : (m.fibers.map RunFiber.id).Nodup)
    (zero : ∀ owed ∈ due, currentCredits q owed.code = 0) (held : Funded q m rest) :
    Funded q (drainOwed m due).1 ((drainOwed m due).2 ++ rest) := by
  induction due generalizing m with
  | nil => exact held
  | cons owed due ih =>
    have head := zero owed (List.mem_cons_self ..)
    have tailZero : ∀ entry ∈ due, currentCredits q entry.code = 0 :=
      fun entry member => zero entry (List.mem_cons_of_mem _ member)
    cases mode : owed.mode with
    | now =>
      simpa only [drainOwed, mode, List.cons_append, Funded, List.map_cons, List.sum_cons,
        commandCredits, head, Nat.zero_add] using ih m unique tailZero held
    | scheduled owner priority =>
      simpa only [drainOwed, mode] using ih (m.postTask owner priority (.resume owed.waiter owed.token owed.code))
        (by rw [post_task_ids]; exact unique) tailZero
        (post_task q m owner priority (.resume owed.waiter owed.token owed.code) head rest unique held)

/-- The native due-resume drain creates only zero-credit completion code. -/
theorem drain_due (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (rest : List Command) (unique : (m.fibers.map RunFiber.id).Nodup)
    (held : Funded q m (.drainDue :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m .drainDue rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  refine drain_owed q _ _ rest unique ?_ ?_
  · intro owed member
    change owed ∈ m.state.deferreds.drainDue.1.map (Owed.mapCode (fun c => embed (completionPrim c))) at member
    obtain ⟨entry, _, equal⟩ := List.mem_map.mp member
    subst owed
    exact Execution.Outer.completion_zero q entry.code
  · exact state q m _ rest (tail q m _ rest held) (Nat.le_refl _)

/-- Waking a store waiter list changes none of the release-credit fields. -/
theorem wake (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (list : WakeKey) (phase : WakePhase) (rest : List Command)
    (held : Funded q m (.wake list phase :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.wake list phase) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  change Funded q {m with state := Stores.wakeList list phase m.state} rest
  unfold Stores.wakeList
  split <;> exact tail q m _ rest held

end Effect4.Program.ReleaseCustody.CommandDebit
