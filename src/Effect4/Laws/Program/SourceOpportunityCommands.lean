import Effect4.Laws.Program.SourceOpportunityExecution
import Effect4.Laws.Program.Size

/-!
Concept: scope-lifetime-finalization R11.
Consumer: admitted-history source-use bounds and original application registrations.
These actual command laws compose existing producer and keyed-row bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- An existing row edit spends at most its original frame reservation.
Consumer: administrative source opportunity command cases. -/
theorem update_total_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (old next : SourceFiber) (same : next.id = old.id)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : old ∈ m.fibers)
    (bound : frame root q next.frame ≤ frame root q old.frame) :
    recorded q (m.update next) + fibers root q (m.update next) ≤ recorded q m + fibers root q m := by
  have decreased := update_debit root q m old next same unique member 0
    (by simpa only [Nat.add_zero] using bound)
  change recorded q m + fibers root q (m.update next) ≤ recorded q m + fibers root q m
  simpa only [Nat.add_zero] using Nat.add_le_add_left decreased (recorded q m)

/-- A keyed administrative edit spends no extra stored source reservation.
Consumer: observers, tracking, dispatcher drains, and decision edits. -/
theorem modify_total_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (edit : SourceFiber → SourceFiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (same : ∀ fiber, (edit fiber).id = fiber.id)
    (bound : ∀ fiber, frame root q (edit fiber).frame ≤ frame root q fiber.frame) :
    recorded q (m.modify id edit) + fibers root q (m.modify id edit) ≤ recorded q m + fibers root q m := by
  unfold RunMachine.modify
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    exact update_total_le root q m fiber (edit fiber) (same fiber) unique
      (List.mem_of_find?_eq_some found) (bound fiber)

/-- Diagnostic trace events record no registration opportunity.
Consumer: administrative command emission. -/
theorem emit_total (root : NativeEff) (q : List Nat) (m : NativeMachine) (events)
    (zero : (events.map (runEvent q)).sum = 0) :
    recorded q (m.emit events) + fibers root q (m.emit events) = recorded q m + fibers root q m := by
  rw [recorded_emit, zero, Nat.add_zero]
  rfl

/-- Starting an existing fiber changes scheduler fields only.
Consumer: the complete source opportunity command contract. -/
theorem evaluate_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.evaluate id) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    split
    · exact Nat.le_refl _
    · have bound := update_total_le root q m fiber {fiber with running := true, currentOpCount := 0}
        rfl unique (List.mem_of_find?_eq_some found) (Nat.le_refl _)
      simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
      exact bound

/-- Interrupting a target discards only its active source reservation.
Consumer: command and outside-loop interruption. -/
theorem interrupt_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List SourceCommand) (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.interruptTarget target who extra) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    have bound := update_total_le root q m fiber (interruptRecord (interpOf root table) who extra fiber).1
      (Guard.interruptRecord_id root table who extra fiber) unique (List.mem_of_find?_eq_some found)
      (interrupt_record_le root q table [] who extra fiber)
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
    exact bound

/-- Native wait codes carry administrative source names only.
Consumer: after-interruption and parallel-await commands. -/
theorem await_code_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (kind : ParkKind) :
    current root q (awaitCode (interpOf root table) m kind) = 0 := by
  fun_cases awaitCode (interpOf root table) m kind
  case case1 target mode exit found => exact exit_answer_zero root q table m exit mode
  case case2 target mode missing => cases mode <;> rfl
  all_goals rfl

/-- Discarding a wait's answer adds no source opportunity.
Consumer: after-interruption command. -/
theorem await_void_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (kind : ParkKind) :
    current root q (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)) = 0 := by
  change current root q (awaitCode (interpOf root table) m kind) + 0 = 0
  rw [await_code_zero, Nat.add_zero]

/-- An administrative answered wait retains the saved source frames.
Consumer: command preservation at afterInterrupt. -/
theorem after_interrupt_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.afterInterrupt host yielding kind) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    have localDebit := replace_current_debit root q m fiber yielding
      (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)) .continue_
      (by rw [await_void_zero]; exact Nat.zero_le _)
    exact settle_debit root q m fiber _ rest unique (List.mem_of_find?_eq_some found) unique rfl localDebit

/-- Clearing an exited stack spends its saved source reservations.
Consumer: exitDone and the finish command. -/
theorem cleared_frame_le (root : NativeEff) (q : List Nat) (table : RowTable) (fiber : SourceFiber) :
    frame root q (fiber.cleared (interpOf root table)).frame ≤ frame root q fiber.frame := by
  change current root q fiber.frame.current + (List.map (saved root q) []).sum ≤ _
  simp only [List.map_nil, List.sum_nil, Nat.add_zero, frame]
  exact Nat.le_add_right _ _

/-- The exitDone command clears only spent frame reservations.
Consumer: complete command preservation. -/
theorem exit_done_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.exitDone id) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    exact update_total_le root q m fiber _ rfl unique (List.mem_of_find?_eq_some found)
      (cleared_frame_le root q table fiber)

/-- Metadata modification retains the distinct stored identity list.
Consumer: composing child tracking and dispatcher posting. -/
theorem modify_ids_same (m : NativeMachine) (id : FiberId) (edit : SourceFiber → SourceFiber) :
    (m.modify id edit).fibers.map (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id) := by
  unfold RunMachine.modify
  split
  · rfl
  · exact RunMachine.update_keeps_ids _ _

/-- Tracking a child edits only the parent and child's metadata.
Consumer: complete source opportunity command preservation. -/
theorem track_child_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.trackChild parent child) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · have parentBound := modify_total_le root q m parent
        (fun fiber => {fiber with children := fiber.children ++ [child]}) unique (fun _ => rfl)
        (fun _ => Nat.le_refl _)
      have firstUnique : ((m.modify parent fun fiber =>
          {fiber with children := fiber.children ++ [child]}).fibers.map (fun fiber => fiber.id)).Nodup := by
        rw [modify_ids_same m parent (fun fiber => {fiber with children := fiber.children ++ [child]})]
        exact unique
      have childBound := modify_total_le root q _ child
        (fun fiber => {fiber with observers := fiber.observers ++ [Observer.untrackChild parent]}) firstUnique
        (fun _ => rfl) (fun _ => Nat.le_refl _)
      exact Nat.le_trans childBound parentBound

/-- Native administrative await and iterator names contain no source opportunity.
Consumer: closeParAwait command preservation. -/
theorem close_parallel_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (children : List FiberId)
    (rest : List SourceCommand) (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.closeParAwait host yielding children) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    apply settle_debit root q m fiber _ rest unique (List.mem_of_find?_eq_some found) unique rfl
    unfold Debit
    change recorded q m + outside root q fiber.id m +
      (0 + (0 + (fiber.frame.stack.map (saved root q)).sum)) ≤ _
    simp only [Nat.zero_add, frame]
    omega

/-- Posting an actual resume task changes dispatcher metadata only.
Consumer: due-store draining and outside-loop clock replies. -/
theorem post_task_total_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (priority : Nat) (task : Task EffName EffThunk Val Err Defect FiberId Ann)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    recorded q (m.postTask owner priority task) + fibers root q (m.postTask owner priority task) ≤
      recorded q m + fibers root q m := by
  unfold RunMachine.postTask
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    have edited := update_total_le root q m fiber
      {fiber with dispatcher := fiber.dispatcher.enqueue priority task} rfl unique
      (List.mem_of_find?_eq_some found) (Nat.le_refl _)
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
    exact edited

/-- Posting a dispatcher task retains all stored fiber identities.
Consumer: repeated due-store draining. -/
theorem post_task_ids (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : Task EffName EffThunk Val Err Defect FiberId Ann) :
    (m.postTask owner priority task).fibers.map (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id) := by
  unfold RunMachine.postTask
  split
  · rfl
  · rename_i fiber found
    change (m.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task}).fibers.map
      (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id)
    exact RunMachine.update_keeps_ids _ _

/-- Draining actual owed replies preserves stored source opportunities.
Consumer: drainDue commands and clock decisions. -/
theorem drain_owed_total_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owed : List (Owed NCode)) (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    recorded q (drainOwed m owed).1 + fibers root q (drainOwed m owed).1 ≤
      recorded q m + fibers root q m := by
  induction owed generalizing m with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    cases mode : first.mode
    case now =>
      rw [drainOwed, mode]
      exact ih m unique
    case scheduled owner priority =>
      rw [drainOwed, mode]
      have nextUnique : ((m.postTask owner priority (.resume first.waiter first.token first.code)).fibers.map
          (fun fiber => fiber.id)).Nodup := by
        rw [post_task_ids]
        exact unique
      exact Nat.le_trans (ih _ nextUnique) (post_task_total_le root q m owner priority _ unique)

/-- The actual drainDue command spends no extra source opportunity.
Consumer: complete command preservation. -/
theorem drain_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m .drainDue rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m :=
  drain_owed_total_le root q {m with state := ((interpOf root table).dueResumes m.state).2}
    ((interpOf root table).dueResumes m.state).1 unique

/-- List interruption spends only off-owner active source reservations.
Consumer: countdown observer composition around its saved waiter row. -/
theorem interrupt_each_outside_le (root : NativeEff) (q : List Nat) (table : RowTable)
    (owner who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (acc : NativeMachine × List SourceCommand) (ledger : ForkLedger.Invariant.Ok acc.1) :
    recorded q (interruptEach (interpOf root table) who extra targets acc).1 +
        outside root q owner (interruptEach (interpOf root table) who extra targets acc).1 ≤
      recorded q acc.1 + outside root q owner acc.1 := by
  induction targets generalizing acc with
  | nil => exact Nat.le_refl _
  | cons target rest ih =>
    unfold interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc ledger
    · rename_i fiber found
      have off := outside_update_le root q acc.1 owner fiber
        (interruptRecord (interpOf root table) (some who) extra fiber).1
        (Guard.interruptRecord_id root table (some who) extra fiber)
        ledger.idsUnique (List.mem_of_find?_eq_some found)
        (interrupt_record_le root q table [] (some who) extra fiber)
      have nextLedger := ForkLedger.Invariant.emit_ok
        (ForkLedger.Invariant.update_ok ledger (interruptRecord (interpOf root table) (some who) extra fiber).1)
        [RunEvent.interruptRecorded (some who) target]
      apply Nat.le_trans (ih _ nextLedger)
      simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        runEvent, Nat.add_zero, outside_emit]
      exact Nat.add_le_add_left off (recorded q acc.1)

/-- Actual countdown bookkeeping never recreates the waiter's source reservation.
Consumer: observe command preservation. -/
theorem observer_total_le (root : NativeEff) (q : List Nat) (table : RowTable)
    (id : FiberId) (exit : ExitV) (acc : NativeMachine × List SourceCommand) (observer : Observer)
    (ledger : ForkLedger.Invariant.Ok acc.1) (raceFree : RaceFreeSource root)
    (source : ConfigurationAt root acc.1) :
    recorded q (fireObserver (interpOf root table) id exit acc observer).1 +
        fibers root q (fireObserver (interpOf root table) id exit acc observer).1 ≤
      recorded q acc.1 + fibers root q acc.1 := by
  let m := acc.1.emit [RunEvent.observerFired id observer]
  have base : ForkLedger.Invariant.Ok m := ledger
  have unchanged : recorded q m + fibers root q m = recorded q acc.1 + fibers root q acc.1 :=
    emit_total root q acc.1 _ rfl
  have offFailed (waiter : FiberId) (remaining : List FiberId) (failure : Bool)
      (next : NativeMachine) (nested : List SourceCommand)
      (found : (if failure then interruptEach (interpOf root table) waiter
        ((interpOf root table).stackAnnotations waiter) remaining (m, []) else (m, [])) = (next, nested)) :
      ForkLedger.Invariant.Ok next ∧ recorded q next + outside root q waiter next ≤
        recorded q m + outside root q waiter m := by
    split at found
    · have off := interrupt_each_outside_le root q table waiter waiter
        ((interpOf root table).stackAnnotations waiter) remaining (m, []) base
      have rows := ForkLedger.Invariant.Native.interruptEach_ok (interpOf root table) waiter
        ((interpOf root table).stackAnnotations waiter) remaining (m, []) base
      rw [found] at off rows
      exact ⟨rows, off⟩
    · cases found
      exact ⟨base, Nat.le_refl _⟩
  have pendingInstall (waiter : FiberId) (fiber changed : SourceFiber)
      (next : NativeMachine) (found : m.fiber? waiter = some fiber)
      (rows : ForkLedger.Invariant.Ok next)
      (off : recorded q next + outside root q waiter next ≤ recorded q m + outside root q waiter m)
      (key : changed.id = fiber.id) (sameFrame : changed.frame = fiber.frame) :
      recorded q (next.update changed) + fibers root q (next.update changed) ≤
        recorded q acc.1 + fibers root q acc.1 := by
    have same := RunMachine.id_of_fiber? found
    have installed := install_le root q next waiter changed (key.trans same) rows.idsUnique
    rw [sameFrame] at installed
    have partition := outside_split root q m fiber base.idsUnique (List.mem_of_find?_eq_some found)
    rw [same] at partition
    change recorded q next + fibers root q (next.update changed) ≤ _
    omega
  have noRaces : m.races = [] := races_nil root m raceFree ⟨source.fibers, source.races, source.scopes⟩
  fun_cases fireObserver (interpOf root table) id exit acc observer
  case case2 parent emitted =>
    rw [← unchanged]
    exact modify_total_le root q m parent _ base.idsUnique (fun _ => rfl) (fun _ => Nat.le_refl _)
  case case7 waiter token fiber p selected collected failure next nested exits walk changed emitted found counted =>
    have moved := offFailed waiter p.remaining failure next nested counted
    exact pendingInstall waiter fiber changed next found moved.1 moved.2 rfl rfl
  case case8 waiter token fiber p selected collected failure next nested exits target rest walk observing changed emitted found counted =>
    have moved := offFailed waiter p.remaining failure next nested counted
    have off := outside_modify_le root q next waiter target
      (fun fiber => {fiber with observers := fiber.observers ++ [Observer.countdown waiter token]})
      moved.1.idsUnique (fun _ => rfl) (fun _ => Nat.le_refl _)
    have rows := ForkLedger.Invariant.modify_ok moved.1 target
      (fun fiber => {fiber with observers := fiber.observers ++ [Observer.countdown waiter token]})
    have observationTrace : recorded q observing = recorded q next := by
      unfold observing RunMachine.modify
      split <;> rfl
    have observingOff : recorded q observing + outside root q waiter observing ≤
        recorded q m + outside root q waiter m := by
      rw [observationTrace]
      exact Nat.le_trans (Nat.add_le_add_left off _) moved.2
    exact pendingInstall waiter fiber changed observing found rows observingOff rfl rfl
  case case10 race previous changed state accepted unsettled selected emitted found updated settling finished =>
    have empty : m.race? race = none := by unfold RunMachine.race?; rw [noRaces]; rfl
    rw [empty] at found
    cases found
  case case11 race previous changed state stopped emitted found updated =>
    have empty : m.race? race = none := by unfold RunMachine.race?; rw [noRaces]; rfl
    rw [empty] at found
    cases found
  case case1 waiter token mode emitted =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case3 scope key emitted found =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case4 scope key state emitted found =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case5 waiter token emitted found =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case6 waiter token fiber selected emitted found =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case9 race emitted found =>
    rw [← unchanged]
    exact Nat.le_refl _
  case case12 key emitted =>
    rw [← unchanged, emit_total root q m [RunEvent.callback key exit] rfl]
    exact Nat.le_refl _

/-- Bounds for every omitted owner bound the total finite stored-row projection.
Consumer: the existing native scope-link debit. -/
theorem outside_bound_total (root : NativeEff) (q : List Nat) (before after : NativeMachine)
    (bound : ∀ owner, recorded q after + outside root q owner after ≤
      recorded q before + outside root q owner before) :
    recorded q after + fibers root q after ≤ recorded q before + fibers root q before := by
  let ids := (before.fibers ++ after.fibers).map (fun fiber => fiber.id.value)
  let owner : FiberId := ⟨ids.sum + 1⟩
  have absent (fiber : SourceFiber) (member : fiber ∈ before.fibers ++ after.fibers) : fiber.id ≠ owner := by
    intro equal
    have lower := le_sum_of_mem ids fiber.id.value (List.mem_map.mpr ⟨fiber, member, rfl⟩)
    have same := congrArg FiberId.value equal
    dsimp only [owner] at same
    omega
  have omitted (m : NativeMachine) (rows : ∀ fiber ∈ m.fibers, fiber ∈ before.fibers ++ after.fibers) :
      outside root q owner m = fibers root q m := by
    unfold outside fibers
    congr 1
    apply List.map_congr_left
    intro fiber member
    exact if_neg (absent fiber (rows fiber member))
  have first := omitted before (fun fiber member => List.mem_append_left _ member)
  have last := omitted after (fun fiber member => List.mem_append_right _ member)
  have debit := bound owner
  rw [first, last] at debit
  exact debit

/-- Actual scope-link bookkeeping spends only existing source opportunities.
Consumer: complete command preservation. -/
theorem link_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.link mode scope target who extra) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  apply outside_bound_total
  intro owner
  have link := link_debit root q table m owner target scope mode who extra unique
  change recorded q (linkScope (interpAt root m.completedExits table) m mode scope target who extra).1 +
    outside root q owner (linkScope (interpAt root m.completedExits table) m mode scope target who extra).1 ≤ _
  rw [link.2]
  exact Nat.add_le_add_left link.1 (recorded q m)

/-- The finish command installs only source-free middleware or retained frames.
Consumer: complete command preservation. -/
theorem finish_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.finish id exit) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    unfold exitFiber
    dsimp only
    split
    · simp only [exitFiber.exitInterruptChildren]
      let changed : SourceFiber := {fiber with
        running := false
        finalizing := some exit
        frame := {fiber.frame with
          deferredInterrupt := false
          current := .onSuccess ((interpOf root table).interruptAllCode fiber.children) (.restore exit)}}
      have bounded : frame root q changed.frame ≤ frame root q fiber.frame := by
        change 0 + (fiber.frame.stack.map (saved root q)).sum ≤ _
        simp only [Nat.zero_add, frame]
        omega
      have updated := update_total_le root q m fiber changed rfl unique (List.mem_of_find?_eq_some found) bounded
      simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
      exact updated
    · let published : SourceFiber := ({fiber with running := false} : SourceFiber).publish exit
      let middle := (m.update published).emit [RunEvent.exited fiber.id exit]
      have emitted := emit_total root q (m.update published) [RunEvent.exited fiber.id exit] rfl
      have updated := update_total_le root q m fiber published rfl unique
        (List.mem_of_find?_eq_some found) (Nat.le_refl _)
      have middleBound : recorded q middle + fibers root q middle ≤ recorded q m + fibers root q m := by
        rw [emitted]
        exact updated
      have middleUnique : (middle.fibers.map (fun fiber => fiber.id)).Nodup := by
        change ((m.update published).fibers.map (fun fiber => fiber.id)).Nodup
        have ids : (m.update published).fibers.map (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id) :=
          RunMachine.update_keeps_ids published m
        rw [ids]
        exact unique
      have own : m.fiber? fiber.id = some fiber := by
        rw [RunMachine.id_of_fiber? found]
        exact found
      have installed : middle.fiber? published.id = some published :=
        Guard.fiber_lookup_update_self own published rfl
      change let out : NativeMachine × List SourceCommand := match published.observers with
        | [] => (middle.update (published.cleared (interpOf root table)), [.drainDue])
        | observers => (middle, observers.map (.observe published.id exit) ++ [.exitDone published.id, .drainDue])
        recorded q out.1 + fibers root q out.1 ≤ _
      split
      · exact Nat.le_trans (update_total_le root q middle published _ rfl middleUnique
          (List.mem_of_find?_eq_some installed) (cleared_frame_le root q table published)) middleBound
      · exact middleBound

/-- Every actual source-owned command spends only the existing source budget.
Consumer: the admitted decision-history bound for Workers and Atomic.
No command constructor remains an additional preservation premise. -/
theorem command_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (command : SourceCommand) (rest : List SourceCommand)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m)
    (head : CommandAt root command) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m command rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  have unique := ledger.idsUnique
  have empty := races_nil root m raceFree owned
  have noRace (id : Nat) : m.race? id = none := by
    unfold RunMachine.race?
    rw [empty]
    rfl
  cases command
  case evaluate id => exact evaluate_command_debit root q table m id rest unique
  case loop id yielding =>
    exact loop_command_debit root q fragment clearFin clearLoop table m id yielding rest
      sequential raceFree owned ledger
  case deliver id yielding =>
    exact deliver_command_debit root q fragment clearFin clearLoop table m id yielding rest
      sequential raceFree owned ledger
  case resume id token answer => exact resume_command_debit root q table m id token answer rest unique head.2
  case launch race =>
    simp only [driveStep, noRace]
    exact Nat.le_refl _
  case enrollRace race child =>
    simp only [driveStep, noRace]
    exact Nat.le_refl _
  case registrationDone race yielding =>
    simp only [driveStep, noRace]
    exact Nat.le_refl _
  case interruptTarget target who extra => exact interrupt_command_debit root q table m target who extra rest unique
  case afterInterrupt host yielding kind => exact after_interrupt_debit root q table m host yielding kind rest unique
  case raceCancel race host yielding remaining visited =>
    cases remaining with
    | nil => exact Nat.le_refl _
    | cons target restTargets =>
      simp only [driveStep, noRace]
      exact Nat.le_refl _
  case trackChild parent child => exact track_child_debit root q table m parent child rest unique
  case observe id exit observer => exact observer_total_le root q table id exit (m, []) observer ledger raceFree owned
  case exitDone id => exact exit_done_debit root q table m id rest unique
  case closeParAwait host yielding children => exact close_parallel_debit root q table m host yielding children rest unique
  case link mode scope target who extra => exact link_command_debit root q table m mode scope target who extra rest unique
  case finish id exit => exact finish_command_debit root q table m id exit rest unique
  case drainDue => exact drain_command_debit root q table m rest unique
  case wake list phase => exact Nat.le_refl _

end Effect4.Program.SourceScope.Opportunities
