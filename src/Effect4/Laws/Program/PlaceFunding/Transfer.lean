import Effect4.Laws.Program.PlaceFunding.Control
import Effect4.Laws.Machine.EditObserverWords
import Effect4.Laws.Machine.Ledger

/-!
Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: shared place funding serves Atomic.Cleanup.log_debits and the existing stack ledger run claim.
Reach: actual machine rows, source permissions for imported code, and local evaluator debit.
The command instance assigns zero weight to races, pending commands, and detached tasks.
External step allowances remain explicit. The saved-stack instance uses zero allowance and unrestricted code.
These laws establish no instance evaluator debit, source admission, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

variable {L : Ledger} {Free : NCode → Prop}

theorem NoQueue.held_eq (quiet : NoQueue L) (m : NativeMachine)
    (pending : List Native.NCmd) (snapshot : List (Task EffName EffThunk Val Err Defect FiberId Ann)) :
    L.held m pending snapshot = L.state m.state + FiberSum.total L.fiber m := by
  simp only [PlaceLedger.held, funext quiet.races, funext quiet.commands, funext quiet.tasks,
    PlaceLedger.zero_sum, Nat.add_zero]

/-- Local accounting installs the actual returned owner once, independently of queued weight. -/
theorem NoQueue.install_debit {L : Ledger} (quiet : NoQueue L)
    (m : NativeMachine) (fiber : Guard.NFiber) (it : Moves.NIteration)
    (unique : (m.fibers.map (fun f => f.id)).Nodup) (member : fiber ∈ m.fibers)
    (afterUnique : (it.machine.fibers.map (fun f => f.id)).Nodup)
    (key : it.fiber.id = fiber.id) (debit : L.IterDebit m fiber it) :
    L.Balanced m [] [] (it.machine.update it.fiber) [] [] := by
  have installed := FiberSum.install_le L.fiber it.machine fiber.id it.fiber key afterUnique
  have kept := L.install_balanced m fiber it [] [] unique member installed debit
  simpa only [PlaceLedger.Balanced, quiet.held_eq] using kept


theorem NoQueue.balance_iff (quiet : NoQueue L) (m n : NativeMachine) :
    L.Balanced m [] [] n [] [] ↔
      L.spent n + (L.state n.state + FiberSum.total L.fiber n) + L.issued m ≤
        L.spent m + (L.state m.state + FiberSum.total L.fiber m) + L.issued n := by
  simp only [PlaceLedger.Balanced, quiet.held_eq]

theorem NoQueue.fields (quiet : NoQueue L) (m n : NativeMachine)
    (fibers : n.fibers = m.fibers) (state : n.state = m.state) (trace : n.trace = m.trace) :
    L.Balanced m [] [] n [] [] := by
  rw [quiet.balance_iff]
  simp only [PlaceLedger.spent, PlaceLedger.issued, FiberSum.total, fibers, state, trace, Nat.le_refl]

theorem Control.metadata_eq (control : Control L Free) (old next : NFiber)
    (id : next.id = old.id) (active : next.frame.current = old.frame.current)
    (saved : next.frame.stack = old.frame.stack) (count : next.currentOpCount = old.currentOpCount) :
    L.fiber next = L.fiber old := by
  exact Nat.le_antisymm (control.metadata old next id active saved (Nat.le_of_eq count))
    (control.metadata next old id.symm active.symm saved.symm (Nat.le_of_eq count.symm))

theorem Control.update (_control : Control L Free) (m : NativeMachine) (old next : NFiber)
    (ok : Ok m) (found : m.fiber? old.id = some old) (id : next.id = old.id)
    (bounded : L.fiber next ≤ L.fiber old) : L.Balanced m [] [] (m.update next) [] [] :=
  PlaceLedger.update_balance L m old next [] [] ok.idsUnique found id bounded

theorem Events.emit (events : Events L) (m : NativeMachine)
    (word : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) (allowed : ∀ event ∈ word, Moves.administrative event = true) :
    L.Balanced m [] [] (m.emit word) [] [] := by
  apply PlaceLedger.emit_balance
  induction word with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons]
    have one := events.administrative head (allowed head (.head _))
    have rest := ih (fun event member => allowed event (.tail _ member))
    omega



def Transfer (before after : NativeMachine) (edit : Machine.Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode (FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) : Prop :=
  after = edit.apply before ∧ (Ok before → Ok after ∧ L.Balanced before [] [] after [] [])

theorem transfer_path {before after : NativeMachine} {word}
    (path : Effect4.Contracts.Path (Transfer (L := L)) before after word) (ok : Ok before) :
    Ok after ∧ L.Balanced before [] [] after [] [] := by
  induction path with
  | nil held => exact ⟨ok, Nat.le_refl _⟩
  | cons edge rest ih =>
    have first := edge.2 ok
    have last := ih first.1
    exact ⟨last.1, first.2.trans L last.2⟩

theorem update_transfer (control : Control L Free) (m : NativeMachine) (old next : NFiber)
    (target : FiberId) (found : m.fiber? target = some old) (id : next.id = old.id)
    (bounded : L.fiber next ≤ L.fiber old) :
    Transfer (L := L) m (m.update next) (.update next) := by
  refine ⟨rfl, fun ok => ⟨update_ok ok next, ?_⟩⟩
  apply control.update m old next ok _ id bounded
  simpa only [RunMachine.id_of_fiber? found] using found

theorem metadata_transfer (control : Control L Free) (m : NativeMachine) (old next : NFiber)
    (target : FiberId) (found : m.fiber? target = some old) (id : next.id = old.id)
    (active : next.frame.current = old.frame.current) (saved : next.frame.stack = old.frame.stack)
    (count : next.currentOpCount ≤ old.currentOpCount) :
    Transfer (L := L) m (m.update next) (.update next) :=
  update_transfer control m old next target found id (control.metadata old next id active saved count)

theorem modify_transfer (control : Control L Free) (m : NativeMachine) (target : FiberId)
    (edit : NFiber → NFiber) (id : ∀ fiber, (edit fiber).id = fiber.id)
    (bounded : ∀ fiber, L.fiber (edit fiber) ≤ L.fiber fiber) :
    Ok m → Ok (m.modify target edit) ∧ L.Balanced m [] [] (m.modify target edit) [] [] := by
  intro ok
  unfold RunMachine.modify
  split
  · exact ⟨ok, Nat.le_refl _⟩
  · rename_i old found
    exact (update_transfer control m old (edit old) target found (id old) (bounded old)).2 ok

theorem observe_transfer (control : Control L Free) (m : NativeMachine)
    (target : FiberId) (observer : Observer) :
    Transfer (L := L) m (m.observe target observer) (.observe target observer) := by
  refine ⟨rfl, ?_⟩
  exact modify_transfer control m target (fun fiber => {fiber with observers := fiber.observers ++ [observer]})
    (fun _ => rfl) (fun fiber => control.metadata fiber _ rfl rfl rfl (Nat.le_refl _))

theorem emit_transfer (events : Events L) (m : NativeMachine)
    (word : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (allowed : ∀ event ∈ word, Moves.administrative event = true) :
    Transfer (L := L) m (m.emit word) (.emit word) :=
  ⟨rfl, fun ok => ⟨emit_ok ok word, events.emit m word allowed⟩⟩

theorem halt_transfer (quiet : NoQueue L) (m : NativeMachine) (why : Stuck) :
    Transfer (L := L) m (m.halt why) (.halt why) :=
  ⟨rfl, fun ok => ⟨halt_ok ok why, quiet.fields m _ rfl rfl rfl⟩⟩

theorem race_transfer (quiet : NoQueue L) (m : NativeMachine) (race : Race EffName EffThunk Val Err Defect FiberId Ann) :
    Transfer (L := L) m (m.updateRace race) (.updateRace race) :=
  ⟨rfl, fun ok => ⟨updateRace_ok ok race, quiet.fields m _ rfl rfl rfl⟩⟩

theorem state_transfer (m : NativeMachine) (state : Stores)
    (bounded : L.state state ≤ L.state m.state) :
    Transfer (L := L) m {m with state := state} (.setState state) :=
  ⟨rfl, fun ok => ⟨state_ok ok state, PlaceLedger.state_balance L m state [] [] bounded⟩⟩

theorem interrupt_transfer (control : Control L Free) (events : Events L)
    (interp : Native.NInterp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (target : FiberId) (acc : NativeMachine × List Native.NCmd) :
    Effect4.Contracts.Path (Transfer (L := L)) acc.1
      (interruptEach interp who extra [target] acc).1 (Edits.interruptWord interp who extra target acc.1) := by
  apply Edits.interrupt_path interp who extra
  · intro m target old found
    apply update_transfer control m old _ target found (StackLedger.interruptRecord_key interp (some who) extra old)
    exact control.interruption (interruptCause interp (some who) extra old.id) old
  · intro m target
    exact emit_transfer events m [.interruptRecorded (some who) target]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)

theorem observer_balance (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (interp : Native.NInterp) (stores : StoreHooks L interp)
    (id : FiberId) (exit : ExitV) (acc : NativeMachine × List Native.NCmd)
    (observer : Observer) (ok : Ok acc.1) :
    L.Balanced acc.1 [] [] (fireObserver interp id exit acc observer).1 [] [] := by
  apply (transfer_path (L := L) (word := Edits.observerWord interp id exit acc.1 observer) (ok := ok) ?_).2
  apply (Edits.observer_producer_path_accounting interp (fun _ => 0) (fun _ => True)
    id exit acc observer ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1
  · intro m target old next found id frame _ _ count _ _ _ _
    exact metadata_transfer control m old next target found id
      (congrArg FrameFiber.current frame) (congrArg FrameFiber.stack frame) (Nat.le_of_eq count)
  · intro m target observed _
    exact observe_transfer control m target observed
  · intro m id observer
    exact emit_transfer events m [.observerFired id observer]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  · intro m id exit
    exact emit_transfer events m [.raceSettled id exit]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  · intro m key exit
    exact emit_transfer events m [.callback key exit]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  · intro m scope key state _ found
    exact state_transfer m state (stores.drop scope key m.state state found)
  · intro m scope key _ _
    exact halt_transfer quiet m (.unknownScope scope)
  · intro m raceId race _
    exact race_transfer quiet m race
  · intro who extra targets held
    exact Edits.interrupts_path interp who extra (interrupt_transfer control events interp who extra) targets held
  · exact fun _ => ⟨rfl, True.intro⟩
  · exact fun _ _ _ _ => ⟨rfl, True.intro⟩
  · exact fun _ _ _ _ _ _ => ⟨rfl, True.intro⟩
  · exact fun _ _ _ _ _ _ _ _ _ => ⟨rfl, True.intro⟩



theorem post_path (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : Task EffName EffThunk Val Err Defect FiberId Ann) :
    Effect4.Contracts.Path (Transfer (L := L)) m (m.postTask owner priority task)
      (Edits.postTaskWord m owner priority task) := by
  apply Edits.postTask_path m owner priority task
  · intro old found
    exact metadata_transfer control m old _ owner found rfl rfl rfl (Nat.le_refl _)
  · intro held
    exact ⟨rfl, fun ok => ⟨arm_ok ok owner, quiet.fields held _ rfl rfl rfl⟩⟩
  · intro held
    exact emit_transfer events held [.scheduledTask owner priority task]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  · exact halt_transfer quiet m (.unknownFiber owner)

theorem drain_balance (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (m : NativeMachine) (owed : List (Owed NCode)) (ok : Ok m) :
    L.Balanced m [] [] (drainOwed m owed).1 [] [] :=
  (transfer_path (Edits.drain_path (post_path control quiet events) m owed) ok).2

theorem Control.fiberEdits_balance (control : Control L Free) (quiet : NoQueue L)
    (m : NativeMachine) (word : List (FiberEdit Err Defect FiberId Ann)) (ok : Ok m) :
    L.Balanced m [] [] (applyFiberEdits word m).1 [] [] := by
  have weighted := FiberSum.fiberEdits_le L.fiber
    (fun fiber entries => control.metadata_eq fiber _ rfl rfl rfl rfl)
    control.interruption word m ok.idsUnique
  have shape := (RunMachine.applyFiberEdits_shape word m).1
  have state := congrArg (fun held : NativeMachine => held.state) shape
  have trace := congrArg (fun held : NativeMachine => held.trace) shape
  rw [quiet.balance_iff]
  unfold PlaceLedger.spent PlaceLedger.issued
  rw [state, trace]
  dsimp only
  omega

theorem link_balance (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (interp : Native.NInterp) (stores : StoreHooks L interp)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (m : NativeMachine) (ok : Ok m) :
    L.Balanced m [] [] (linkScope interp m mode scope target who extra).1 [] [] := by
  have plan : Effect4.Contracts.Path (Transfer (L := L)) m
      (linkScopeEdits interp m mode scope target who extra).1 (Edits.linkWord interp m mode scope target who) := by
    apply Edits.link_plan_path interp mode scope target who m
    · intro state key found
      exact state_transfer m state (stores.link mode scope target m.state state key found)
    · intro held
      apply emit_transfer events
      intro event member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro held key
      apply emit_transfer events
      intro event member
      have same := List.mem_singleton.mp member
      subst event
      rfl
    · intro held why
      exact halt_transfer quiet held why
  have kept := transfer_path plan ok
  exact kept.2.trans L (control.fiberEdits_balance quiet _ _ kept.1)

theorem Control.replace_changed (control : Control L Free) (old next : NFiber)
    (key : next.id = old.id) (free : Free next.frame.current)
    (saved : next.frame.stack = old.frame.stack) (count : next.currentOpCount ≤ old.currentOpCount) :
    L.fiber next ≤ L.fiber old := by
  have metadata := control.metadata {old with frame.current := next.frame.current} next key rfl saved count
  exact Nat.le_trans metadata (control.replace old next.frame.current free)

theorem Control.clear_changed (control : Control L Free) (old next : NFiber)
    (key : next.id = old.id) (active : next.frame.current = old.frame.current)
    (saved : next.frame.stack = []) (count : next.currentOpCount ≤ old.currentOpCount) :
    L.fiber next ≤ L.fiber old := by
  have metadata := control.metadata {old with frame.stack := []} next key active saved count
  exact Nat.le_trans metadata (control.clear old)

theorem quiet_funded (quiet : NoQueue L) (cap : Nat) (m : NativeMachine)
    (pending : List Native.NCmd) (snapshot : List (Task EffName EffThunk Val Err Defect FiberId Ann)) :
    L.Funded cap m pending snapshot ↔ L.Funded cap m [] [] := by
  simp only [PlaceLedger.Funded, quiet.held_eq]

theorem settle_balance (control : Control L Free) (quiet : NoQueue L)
    (id : FiberId) (rest : List Native.NCmd) (it : Native.NIter) (ok : Ok it.machine) :
    L.Balanced (it.machine.update it.fiber) [] [] (settle id rest it).1 [] [] := by
  have settled := L.settle_balanced
    (fun fiber entries => control.metadata_eq fiber _ rfl rfl rfl rfl)
    control.interruption
    (fun fiber => control.metadata_eq fiber _ rfl rfl rfl rfl)
    (fun fiber => control.metadata_eq fiber _ rfl rfl rfl rfl)
    (fun id => quiet.commands (.evaluate id)) (fun id y => quiet.commands (.loop id y))
    (fun id y => quiet.commands (.deliver id y))
    (fun id exit => quiet.commands (.finish id exit)) id rest it [] ok.idsUnique
  simpa only [PlaceLedger.Balanced, quiet.held_eq] using settled



theorem settle_bookkeeping (control : Control L Free) (quiet : NoQueue L)
    (m : NativeMachine) (old : NFiber) (it : Native.NIter) (rest : List Native.NCmd)
    (ok : Ok it.machine) (found : m.fiber? old.id = some old)
    (rows : it.machine.fibers = m.fibers) (key : it.fiber.id = old.id)
    (weight : L.fiber it.fiber ≤ L.fiber old)
    (before : L.Balanced m [] [] it.machine [] []) :
    L.Balanced m [] [] (settle old.id rest it).1 [] [] := by
  have stored : it.machine.fiber? old.id = some old := by
    simp only [RunMachine.fiber?, rows]
    exact found
  have installed := control.update it.machine old it.fiber ok stored key weight
  exact (before.trans L installed).trans L (settle_balance control quiet old.id rest it ok)

theorem spawn_balance (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (interp : Native.NInterp) (m : NativeMachine) (parent : NFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) (free : Free program) :
    L.Balanced m [] [] (spawn interp m parent program options site).1 [] [] := by
  let flag := match options.maskMode with
    | .interruptible => true | .uninterruptible => false | .inherit => parent.frame.interruptible
  let child : NFiber := RunFiber.make ⟨m.nextId⟩ program flag (interp.budgetOf parent.context) parent.context
  let appended : NativeMachine := {m with fibers := m.fibers ++ [child]}
  let stamped : NativeMachine := {appended with
    nextId := m.nextId + 1
    forks := m.forks ++ [⟨⟨m.nextId⟩, parent.id, options.daemon, site⟩]}
  have weight : L.fiber child = 0 := control.entry _ program flag _ _ free
  have added := PlaceLedger.append_balance L m child [] [] weight
  have metadata := quiet.fields appended stamped rfl rfl rfl
  have emitted := events.emit stamped [.forked parent.id ⟨m.nextId⟩ options.daemon]
    (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  exact (added.trans L metadata).trans L emitted

end Effect4.Program.PlaceFunding
