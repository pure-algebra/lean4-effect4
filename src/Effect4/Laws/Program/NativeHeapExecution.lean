import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.StoreExecution
import Effect4.Laws.Machine.RefFootprint

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The cell predicate follows actual evaluation using the checked source writer.
Administrative scheduler and scope transitions retain references.
The shared command transfer retains the actual looked-up owner and synchronous answer.
Source heap and Timeout numeric instances consume this one command classification.
The numeric instance still owes source permission and cleanup/count order.
-/
set_option autoImplicit false
namespace Effect4.Program.StoreExecution
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- The existing native transfer exposes its actual represented synchronous operation.
This eliminates native thunk wrappers once, without another evaluator census. -/
theorem RefTransfer.native_row (root : NativeEff) (completed) (table : RowTable)
    {input : NCode} {before after : Stores}
    (step : RefTransfer (interpAt root completed table) input before after) :
    after.refs = before.refs ∨ ∃ op value,
      (input = .sync (.op op) ∨ input = .sync (.store (.op op))) ∧
      syncOpStep op before = some (after, value) := by
  cases step with
  | same _ refs => exact .inl refs
  | sync thunk next value current unparked answer =>
    cases thunk
    case op op => exact .inr ⟨op, value, .inl current, answer⟩
    case store stored =>
      cases stored
      case op op => exact .inr ⟨op, value, .inr current, answer⟩
      all_goals cases answer
    all_goals cases answer

/-- Every native reference transfer keeps a lookup outside its actual operation footprint.
The source premise names the represented operation and its actual answer. -/
theorem RefTransfer.refPeek_other (root : NativeEff) (completed) (table : RowTable)
    {input : NCode} {before after : Stores}
    (step : RefTransfer (interpAt root completed table) input before after) (cell : RefKey)
    (outside : ∀ op value,
      (input = .sync (.op op) ∨ input = .sync (.store (.op op))) →
      syncOpStep op before = some (after, value) → op.refFootprint value ≠ some cell) :
    refPeek after.refs cell = refPeek before.refs cell := by
  rcases step.native_row root completed table with same | ⟨op, value, current, actual⟩
  · exact same ▸ rfl
  · exact syncOpStep_refPeek_other actual cell (outside op value current actual)

/-- The generated primitive eliminator exposes the actual store action once.
The existing administrative projections supply all non-synchronous reference effects. -/
theorem primitive_refTransfer (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    RefTransfer (interpAt root completed table) fiber.frame.current m.state
      (evaluatePrim (interpAt root completed table) m fiber yielding).machine.state := by
  fun_cases evaluatePrim (interpAt root completed table) m fiber yielding
  case case2 register signal cancel current token state grown code registered =>
    apply RefTransfer.same
    have kept := SourceScope.register_refs root completed table register fiber.id m.nextToken m.state
    rw [registered] at kept
    exact kept
  case case3 register signal cancel current token state grown before parked registered =>
    apply RefTransfer.same
    have kept := SourceScope.register_refs root completed table register fiber.id m.nextToken m.state
    rw [registered] at kept
    exact kept
  case case5 race parked noYield noAsync =>
    unfold registerRace
    split <;> exact .same _ rfl
  case case6 targets parked next returned waiting edits counted noYield noAsync =>
    apply RefTransfer.same
    have kept := congrArg Stores.refs (StatePreservation.countdown_plan_state
      (interpAt root completed table) m fiber targets .exitsValue false)
    rw [counted] at kept
    exact kept
  case case10 noPark thunk current action found noYield noAsync =>
    exact .same _ (SourceScope.action_refs root completed table m fiber yielding action)
  case case11 noPark thunk current missing noYield noAsync =>
    exact .same _ (SourceScope.step_frame_refs root completed table m fiber yielding)
  case case12 noPark thunk current state value synced noYield noAsync =>
    exact .sync thunk state value current noPark synced
  case case14 noPark value current noYield noAsync =>
    exact .same _ (SourceScope.finalizer_refs root completed table m fiber yielding (.success value))
  case case15 noPark cause current noYield noAsync =>
    exact .same _ (SourceScope.finalizer_refs root completed table m fiber yielding (.failure cause))
  case case16 noPark noWithFiber noSync noSuccess noFailure noYield noAsync =>
    exact .same _ (SourceScope.step_frame_refs root completed table m fiber yielding)
  all_goals exact .same _ rfl

/-- The native evaluator keeps a cell outside its actual synchronous operation footprint.
Consumer: the reference lookup component of Atomic, Workers, and Timeout accounting.
This exposes source permission; it does not assume a separate per-scenario evaluator census. -/
theorem primitive_refPeek_other (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (cell : RefKey)
    (outside : ∀ op value,
      (fiber.frame.current = .sync (.op op) ∨ fiber.frame.current = .sync (.store (.op op))) →
      syncOpStep op m.state = some ((evaluatePrim (interpAt root completed table) m fiber yielding).machine.state, value) →
      op.refFootprint value ≠ some cell) :
    refPeek (evaluatePrim (interpAt root completed table) m fiber yielding).machine.state.refs cell =
      refPeek m.state.refs cell :=
  (primitive_refTransfer root completed table m fiber yielding).refPeek_other root completed table cell outside


theorem RefTransfer.table (root : NativeEff) (view : List (FiberId × ExitV)) (left right : RowTable)
    {input : NCode} {before after : Stores}
    (held : RefTransfer (interpAt root view left) input before after) :
    RefTransfer (interpAt root view right) input before after := by
  cases held with
  | same next refs => exact .same _ refs
  | sync thunk next value current unparked answer =>
    exact .sync thunk _ value current unparked answer

theorem exitScoped_refTransfer (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (exit : ExitV) :
    RefTransfer (interpAt root m.completedExits) fiber.frame.current m.state
      (exitScoped root m fiber yielding exit).machine.state := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact .same _ rfl
    · rename_i state program closed
      have kept := close_unsafe_refs _ _ _ m.state state program closed
      cases program <;> exact .same _ kept
  · exact primitive_refTransfer root m.completedExits [] m fiber yielding

theorem native_refTransfer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) :
    RefTransfer (interpAt root m.completedExits table) fiber.frame.current m.state
      (evaluateNative root m fiber yielding table).machine.state := by
  unfold evaluateNative
  split
  · split
    · exact .same _ rfl
    · exact primitive_refTransfer root m.completedExits table m fiber yielding
  · exact RefTransfer.table root m.completedExits [] table (exitScoped_refTransfer root m fiber yielding _)
  · exact RefTransfer.table root m.completedExits [] table (exitScoped_refTransfer root m fiber yielding _)
  · exact primitive_refTransfer root m.completedExits table m fiber yielding

/-- Runloop interruption can replace code only with failure, which writes no references. -/
theorem runloopTop_refTransfer (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (fiber : SourceFiber) {before after : Stores}
    (held : RefTransfer (interpAt root view table) (runloopTop fiber).frame.current before after) :
    RefTransfer (interpAt root view table) fiber.frame.current before after := by
  unfold runloopTop at held
  split at held
  · cases held with
    | same next refs => exact .same _ refs
    | sync thunk next value current unparked answer => cases current
  · exact held

/-- A charged iteration executes only the original synchronous head or leaves references alone. -/
theorem iteration_refTransfer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) :
    RefTransfer (interpAt root m.completedExits table) fiber.frame.current m.state
      (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding).machine.state := by
  unfold iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      have step := native_refTransfer root table
        (m.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}} true
      cases step with
      | same next refs => exact .same _ refs
      | sync thunk next value current unparked answer => cases current
    · cases injected
  · exact runloopTop_refTransfer root m.completedExits table fiber
      (native_refTransfer root table m (countOp (runloopTop fiber)) yielding)

/-- An actual command either retains references or executes the synchronous head of its looked-up owner. -/
inductive CommandRefTransfer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) : Stores → Prop
  | same (after : Stores) (refs : after.refs = m.state.refs) :
      CommandRefTransfer root table m command after
  | sync (id : FiberId) (yielding : Bool) (fiber : SourceFiber) (thunk : EffThunk)
      (after : Stores) (value : Val) (found : m.fiber? id = some fiber)
      (runs : command = .loop id yielding ∨ command = .deliver id yielding)
      (current : fiber.frame.current = .sync thunk)
      (unparked : (interpAt root m.completedExits table).parkOf fiber.frame.current = none)
      (answer : (interpAt root m.completedExits table).syncState thunk m.state = some (after, value)) :
      CommandRefTransfer root table m command after

theorem CommandRefTransfer.of_transfer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) (id : FiberId) (yielding : Bool) (fiber : SourceFiber) {after : Stores}
    (found : m.fiber? id = some fiber)
    (runs : command = .loop id yielding ∨ command = .deliver id yielding)
    (step : RefTransfer (interpAt root m.completedExits table) fiber.frame.current m.state after) :
    CommandRefTransfer root table m command after := by
  cases step with
  | same next refs => exact .same _ refs
  | sync thunk next value current unparked answer =>
    exact .sync id yielding fiber thunk _ value found runs current unparked answer

/-- A command's reference predicate consumes only its actual looked-up synchronous writer. -/
theorem CommandRefTransfer.preserves {root : NativeEff} {table : RowTable} {m : NativeMachine}
    {command : SourceCommand} {after : Stores}
    (step : CommandRefTransfer root table m command after) (P : RefHeap → Prop)
    (held : P m.state.refs)
    (sync : ∀ id yielding fiber thunk next value, m.fiber? id = some fiber →
      (command = .loop id yielding ∨ command = .deliver id yielding) →
      fiber.frame.current = .sync thunk →
      (interpAt root m.completedExits table).parkOf fiber.frame.current = none →
      (interpAt root m.completedExits table).syncState thunk m.state = some (next, value) →
      P next.refs) : P after.refs := by
  cases step with
  | same next refs => exact refs ▸ held
  | sync id yielding fiber thunk next value found runs current unparked answer =>
    exact sync id yielding fiber thunk _ value found runs current unparked answer

/-- The existing generated command eliminator exposes its actual reference effect once. -/
theorem command_refTransfer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) (rest : List SourceCommand) :
    CommandRefTransfer root table m command
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1.state := by
  fun_cases driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest
  case case5 id yielding fiber found =>
    rw [StatePreservation.settle_state]
    exact CommandRefTransfer.of_transfer root table m _ id yielding fiber found (.inl rfl)
      (iteration_refTransfer root table m fiber yielding)
  case case7 id yielding fiber found =>
    rw [StatePreservation.settle_state]
    exact CommandRefTransfer.of_transfer root table m _ id yielding fiber found (.inr rfl)
      (native_refTransfer root table m fiber yielding)
  case case16 id race raceFound program more programs blocked host hostFound spawned child spawnedEq updated =>
    apply CommandRefTransfer.same
    have kept := spawn_refs root table m host program ⟨true, true, .interruptible⟩ (race.nextSite.getD [])
    change (launchEntrant (interpOf root table) id m host program (race.nextSite.getD [])).1.state.refs = m.state.refs at kept
    rw [spawnedEq] at kept
    exact kept
  case case17 id child race fiber fiberFound raceFound updated exit exited changed nested observed =>
    apply CommandRefTransfer.same
    have kept := observer_refs root table child exit (updated, []) (.raceCallback id)
    rw [observed] at kept
    exact kept
  case case22 id yielding race raceFound updated fiber found exit accepted code changed =>
    exact .same _ (settle_refs _ _ _)
  case case23 id yielding race raceFound updated fiber found missing name before parked =>
    exact .same _ (settle_refs _ _ _)
  case case27 host yielding kind fiber found changed =>
    exact .same _ (settle_refs _ _ _)
  case case35 id exit observer changed nested observed =>
    apply CommandRefTransfer.same
    have kept := observer_refs root table id exit (m, []) observer
    rw [observed] at kept
    exact kept
  case case39 host yielding children fiber found frame changed =>
    exact .same _ (settle_refs _ _ _)
  case case40 mode scope target who extra changed nested linked =>
    apply CommandRefTransfer.same
    have kept := link_refs root table m mode scope target who extra
    rw [linked] at kept
    exact kept
  case case42 id exit fiber found changed nested finished =>
    apply CommandRefTransfer.same
    have kept := exit_fiber_refs root table m {fiber with running := false} exit
    rw [finished] at kept
    exact kept
  case case43 completions state found drainedPair =>
    apply CommandRefTransfer.same
    have kept := drain_refs {m with state} completions
    have stateRefs : state.refs = m.state.refs := by
      have h : ((interpOf root table).dueResumes m.state).2.refs = m.state.refs := rfl
      rw [found] at h
      exact h
    rw [kept, stateRefs]
  case case44 list phase =>
    apply CommandRefTransfer.same
    change (Stores.wakeList list phase m.state).refs = m.state.refs
    unfold Stores.wakeList
    split <;> rfl
  all_goals apply CommandRefTransfer.same
  all_goals simp only [RunMachine.emit, RunMachine.update, modify_state]
  all_goals rfl


end Effect4.Program.StoreExecution

namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program HeapSites

/-- Actual primitive evaluation uses the site's operation law at every reference writer. -/
theorem primitive_heap (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (held : FiberAt root fiber)
    (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (evaluatePrim (interpAt root completed table) m fiber yielding).machine.state.refs := by
  apply (StoreExecution.primitive_refTransfer root completed table m fiber yielding).preserves (HeapOk P) heap
  intro thunk state value current unparked synced
  have source := held.frame.1
  rw [current] at source
  exact sync_heap_at root completed table thunk m.state state value P sites heap source synced

/-- Scoped exit changes only scope state before running its represented cleanup. -/
theorem exit_scoped_heap (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (exit : ExitV) (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P)
    (heap : HeapOk P m.state.refs) : HeapOk P (exitScoped root m fiber yielding exit).machine.state.refs := by
  apply (StoreExecution.exitScoped_refTransfer root m fiber yielding exit).preserves (HeapOk P) heap
  intro thunk state value current unparked synced
  have source := held.frame.1
  rw [current] at source
  exact sync_heap_at root m.completedExits [] thunk m.state state value P sites heap source synced

/-- Actual native evaluation keeps the cell predicate from its source-site laws. -/
theorem native_heap (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P)
    (heap : HeapOk P m.state.refs) : HeapOk P (evaluateNative root m fiber yielding table).machine.state.refs := by
  apply (StoreExecution.native_refTransfer root table m fiber yielding).preserves (HeapOk P) heap
  intro thunk state value current unparked synced
  have source := held.frame.1
  rw [current] at source
  exact sync_heap_at root m.completedExits table thunk m.state state value P sites heap source synced

/-- A charged or forced-yield native iteration retains the source premise for its writer. -/
theorem iteration_heap (root : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (owned : ConfigurationAt root m)
    (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding).machine.state.refs := by
  have _ := owned
  apply (StoreExecution.iteration_refTransfer root table m fiber yielding).preserves (HeapOk P) heap
  intro thunk state value current unparked synced
  have source := held.frame.1
  rw [current] at source
  exact sync_heap_at root m.completedExits table thunk m.state state value P sites heap source synced

/-- Every actual command keeps the cell predicate while its current writer has source ownership. -/
theorem command_heap (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) (rest : List SourceCommand) (owned : ConfigurationAt root m)
    (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1.state.refs := by
  apply (StoreExecution.command_refTransfer root table m command rest).preserves (HeapOk P) heap
  intro id yielding fiber thunk state value found runs current unparked synced
  have source := (configuration_fiber root m id fiber owned found).frame.1
  rw [current] at source
  exact sync_heap_at root m.completedExits table thunk m.state state value P sites heap source synced

end Effect4.Program.SourceScope
