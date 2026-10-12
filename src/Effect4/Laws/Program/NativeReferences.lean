import Effect4.Laws.Program.NativeHistory
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
Administrative native transitions retain the reference heap.
Only an owned synchronous writer needs the checked source-site premise.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program HeapSites

/-- A keyed fiber edit retains the machine's store. -/
theorem modify_state (m : NativeMachine) (id : FiberId) (edit : SourceFiber → SourceFiber) :
    (m.modify id edit).state = m.state := by
  unfold RunMachine.modify
  split <;> rfl

/-- The close snapshot changes only scope rows. -/
theorem snapshot_refs (scope : Nat) (exit : ExitV) (state next : Stores)
    (strategy : FinalizerStrategy) (order : List FinName)
    (found : scopeCloseSnapshot scope exit state = some (next, strategy, order)) : next.refs = state.refs := by
  unfold scopeCloseSnapshot at found
  cases h : state.scopes.entryAt scope with
  | none => rw [h] at found; cases found
  | some entry =>
    simp only [h, Option.pure_def] at found
    cases found; rfl

/-- Unsafe scope closure changes the scope store before constructing cleanup, retaining references. -/
theorem close_unsafe_refs (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores)
    (program : Option Program) (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    next.refs = state.refs := by
  unfold storesCloseScopeUnsafe scopeCloseSnapshot at found
  repeat' split at found
  all_goals aesop

/-- Public scope closure likewise retains the reference heap. -/
theorem close_refs (root : NativeEff) (completed) (table : RowTable) (scope : Nat) (exit : ExitV)
    (flag : Bool) (fiber : FiberId) (state next : Stores) (code : Option NCode)
    (found : (interpAt root completed table).closeScope scope exit flag fiber state = some (next, code)) :
    next.refs = state.refs := by
  change (storesCloseScope scope exit flag state).map (fun r => (r.1, r.2.map embed)) =
    some (next, code) at found
  obtain ⟨pair, closed, eq⟩ := Option.map_eq_some_iff.mp found
  cases eq
  unfold storesCloseScope at closed
  repeat' split at closed
  all_goals aesop (add safe forward [snapshot_refs])

/-- Registering a native scope link changes only scopes and allocation metadata. -/
theorem scope_link_refs (root : NativeEff) (table : RowTable) (mode : Supervision.ScopeMode)
    (scope : Nat) (fiber : FiberId) (state next : Stores) (key : Nat)
    (found : (interpOf root table).scopeLinkFiber mode scope fiber state = some (next, key)) :
    next.refs = state.refs := by
  simp only [interpOf] at found
  split at found
  · cases found
  · cases found; rfl

/-- The native scope-link plan retains references before its addressed edits.
Consumer: actual native actions and the eager link adapter. -/
theorem link_plan_refs (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    (linkScopeEdits (interpOf root table) m mode scope target who extra).1.state.refs = m.state.refs := by
  unfold linkScopeEdits
  dsimp only
  repeat' split
  all_goals aesop (add safe forward [(scope_link_refs root table)]) (add norm simp [RunMachine.emit])

/-- Linking an existing native fiber retains references in every scope status. -/
theorem link_refs (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    (linkScope (interpOf root table) m mode scope target who extra).1.state.refs = m.state.refs := by
  unfold linkScope
  rw [congrArg RunMachine.state (RunMachine.applyFiberEdits_shape _ _).1]
  exact link_plan_refs root table m mode scope target who extra

/-- Native registration changes only deferreds or timers. -/
theorem register_refs (root : NativeEff) (completed) (table : RowTable) (name : EffName)
    (fiber : FiberId) (token : Nat) (state : Stores) :
    ((interpAt root completed table).registerAsync name fiber token state).1.refs = state.refs := by
  cases name
  case store name => cases name <;> rfl
  all_goals rfl

/-- Countdown parking installs callbacks without changing references. -/
theorem countdown_refs (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    (countdownPark (interpAt root completed table) m fiber targets resume failFast).1.state.refs = m.state.refs := by
  exact congrArg Stores.refs (StatePreservation.countdown_state (interpAt root completed table)
    m fiber targets resume failFast)

/-- Spawning stores only a fiber and its provenance. -/
theorem spawn_refs (root : NativeEff) (table : RowTable) (m : NativeMachine) (host : SourceFiber)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    (spawn (interpOf root table) m host program options site).1.state.refs = m.state.refs := rfl

/-- Starting a newly stored fiber retains references. -/
theorem start_refs (m : NativeMachine) (fiber : SourceFiber) (child : FiberId) (immediate : Bool) :
    (start m fiber child immediate).1.state.refs = m.state.refs := by
  unfold start
  split <;> rfl

/-- Parallel finalizer spawning retains references until those programs run. -/
theorem fork_finalizer_refs (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (host : SourceFiber) (programs : List NCode) :
    (forkFinalizers (interpAt root completed table) m host programs).1.state.refs = m.state.refs := by
  induction programs generalizing m with
  | nil => rfl
  | cons program rest ih =>
    exact (ih _).trans (spawn_refs root table m host program ⟨true, true, .inherit⟩ [])

/-- Shared frame evaluation itself changes no store. -/
theorem step_frame_refs (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding).machine.state.refs = m.state.refs := by
  unfold evaluatePrim.stepFrame
  dsimp only
  unfold evaluatePrim.finishFrame
  dsimp only
  split <;> rfl

/-- Running a represented finalizer changes its frame, retaining references until the body runs. -/
theorem finalizer_refs (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding exit).machine.state.refs = m.state.refs := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  repeat' split
  all_goals aesop (add norm simp [step_frame_refs])

set_option maxHeartbeats 1000000 in
/-- Native fiber actions change scheduler or scope state, retaining the reference heap. -/
theorem action_refs (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber (interpAt root completed table) m fiber yielding action).machine.state.refs = m.state.refs := by
  have born (before after : NativeMachine) (parent returned : SourceFiber) (program : NCode)
      (options : Supervision.ForkOptions) (site : List Nat) (child : FiberId)
      (found : spawn (interpAt root completed table) before parent program options site = (after, returned, child)) :
      after.state.refs = before.state.refs := by
    have kept := spawn_refs root table before parent program options site
    change (spawn (interpAt root completed table) before parent program options site).1.state.refs = before.state.refs at kept
    rw [found] at kept
    exact kept
  have started (before after : NativeMachine) (parent returned : SourceFiber) (child : FiberId)
      (immediate : Bool) (nested : List SourceCommand) (found : start before parent child immediate = (after, returned, nested)) :
      after.state.refs = before.state.refs := by
    have kept := start_refs before parent child immediate
    rw [found] at kept
    exact kept
  fun_cases evaluatePrim.withFiber (interpAt root completed table) m fiber yielding action
  case case1 answer program options site prepared parent spawned returned child birth after final nested startEq =>
    have fromSpawn := born prepared spawned fiber returned program options site child birth
    have fromStart := started spawned after returned final child options.startImmediately nested startEq
    have preparedRefs : prepared.state.refs = m.state.refs := by dsimp only [prepared]; split <;> rfl
    exact fromStart.trans (fromSpawn.trans preparedRefs)
  case case2 answer program options scope site spawned returned child birth after final nested startEq =>
    exact (started spawned after returned final child options.startImmediately nested startEq).trans
      (born m spawned fiber returned program {options with daemon := true} site child birth)
  case case3 answer program options site scope ambient spawned returned child birth after final nested startEq =>
    exact (started spawned after returned final child options.startImmediately nested startEq).trans
      (born m spawned fiber returned program {options with daemon := true} site child birth)
  case case7 answer outcome target scope after nested found =>
    have kept := link_plan_refs root table m .fiberRunIn scope target (some target) ReasonAnnotations.empty
    change (linkScopeEdits (interpAt root completed table) m .fiberRunIn scope target (some target) ReasonAnnotations.empty).1.state.refs = m.state.refs at kept
    rw [found] at kept
    exact kept
  case case9 target who =>
    unfold evaluatePrim.interruptAs
    split <;> rfl
  case case13 outcome targets after returned parked edits found =>
    have kept := congrArg Stores.refs (StatePreservation.countdown_plan_state (interpAt root completed table) m fiber targets .exitsValue false)
    rw [found] at kept; exact kept
  case case14 outcome targets after returned parked edits found =>
    have kept := congrArg Stores.refs (StatePreservation.countdown_plan_state (interpAt root completed table) m fiber targets .exitsValue true)
    rw [found] at kept; exact kept
  case case16 outcome snapshot fresh after returned parked edits found =>
    have kept := congrArg Stores.refs (StatePreservation.countdown_plan_state (interpAt root completed table) m fiber fresh .void false)
    rw [found] at kept; exact kept
  case case17 entrants site => rfl
  case case18 entrants site => rfl
  case case25 scope exit state found => exact close_refs root completed table scope exit _ _ m.state state none found
  case case26 scope exit state program found =>
    exact close_refs root completed table scope exit _ _ m.state state (some program) found
  case case27 programs after children found =>
    have kept := fork_finalizer_refs root completed table m fiber programs
    rw [found] at kept; exact kept
  all_goals rfl

/-- Posting a task changes scheduler fields, retaining the store. -/
theorem post_refs (m : NativeMachine) (owner : FiberId) (priority : Nat) (task : SourceTask) :
    (m.postTask owner priority task).state.refs = m.state.refs := by
  unfold RunMachine.postTask
  split <;> rfl

/-- An owed-resume drain installs only tasks or commands. -/
theorem drain_refs (m : NativeMachine) (due : List (Owed NCode)) :
    (drainOwed m due).1.state.refs = m.state.refs := by
  induction due generalizing m with
  | nil => rfl
  | cons first rest ih =>
    simp only [drainOwed]
    cases first.mode with
    | now => exact ih m
    | scheduled owner priority => exact (ih _).trans (post_refs m owner priority _)

/-- Interrupting a target list edits only saved fiber state. -/
theorem interrupt_each_refs (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (acc : NativeMachine × List SourceCommand) :
    (interruptEach (interpOf root table) who extra targets acc).1.state.refs = acc.1.state.refs := by
  induction targets generalizing acc with
  | nil => rfl
  | cons target rest ih =>
    unfold interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc
    · exact ih _

/-- Removing a finalizer edits only the scope store. -/
theorem drop_refs (root : NativeEff) (table : RowTable) (scope key : Nat) (state next : Stores)
    (found : (interpOf root table).dropFinalizer scope key state = some next) : next.refs = state.refs := by
  simp only [interpOf] at found
  split at found
  · cases found
  · cases found; rfl

/-- Observer bookkeeping retains the reference heap before its returned programs run. -/
theorem observer_refs (root : NativeEff) (table : RowTable) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List SourceCommand) (observer : Observer) :
    (fireObserver (interpOf root table) id exit acc observer).1.state.refs = acc.1.state.refs := by
  cases observer with
  | resumeAwait => rfl
  | untrackChild => exact congrArg Stores.refs (modify_state _ _ _)
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split
    · rfl
    · rename_i state step
      exact drop_refs root table scope key _ state step
  | countdown waiter token =>
    simp only [fireObserver]
    repeat' split
    all_goals simp only [RunMachine.applyFiberEdit_state, RunMachine.update,
      StatePreservation.interruptEach_state, RunMachine.emit]
  | raceCallback =>
    simp only [fireObserver]
    split
    · rfl
    · split <;> rfl
  | callback => rfl

/-- Publishing an exit or installing middleware changes no reference cell. -/
theorem exit_fiber_refs (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : SourceFiber) (exit : ExitV) :
    (exitFiber (interpOf root table) m fiber exit).1.state.refs = m.state.refs := by
  unfold exitFiber
  split
  · rfl
  · unfold exitFiber.exitStore
    dsimp only
    split <;> rfl

/-- Settling saves the acting fiber and commands, retaining its already produced store. -/
theorem settle_refs (id : FiberId) (rest : List SourceCommand) (it : SourceIteration) :
    (settle id rest it).1.state.refs = it.machine.state.refs := by
  exact congrArg Stores.refs (StatePreservation.settle_state id rest it)

end Effect4.Program.SourceScope
