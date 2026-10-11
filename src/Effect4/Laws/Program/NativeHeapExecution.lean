import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.StoreExecution

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The cell predicate follows actual evaluation using the checked source writer.
Administrative scheduler and scope transitions retain references.
-/
set_option autoImplicit false
namespace Effect4.Program.StoreExecution
open Effect4 Effect4.Machine Effect4.Program

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


end Effect4.Program.StoreExecution

namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program HeapSites

/-- Actual primitive evaluation uses the site's operation law at every reference writer. -/
theorem primitive_heap (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (held : FiberAt root fiber)
    (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (evaluatePrim (interpAt root completed table) m fiber yielding).machine.state.refs := by
  apply (StoreExecution.primitive_refTransfer root completed table m fiber yielding).preserves
    (HeapOk P) heap
  intro thunk state value current unparked synced
  have source := held.frame.1
  rw [current] at source
  exact sync_heap_at root completed table thunk m.state state value P sites heap source synced

/-- Scoped exit changes only scope state before running its represented cleanup. -/
theorem exit_scoped_heap (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (exit : ExitV) (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P)
    (heap : HeapOk P m.state.refs) : HeapOk P (exitScoped root m fiber yielding exit).machine.state.refs := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact heap
    · rename_i state program closed
      have kept := close_unsafe_refs _ _ _ m.state state program closed
      cases program <;> exact kept ▸ heap
  · exact primitive_heap root m.completedExits [] m fiber yielding held P sites heap

/-- Actual native evaluation keeps the cell predicate from its source-site laws. -/
theorem native_heap (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P)
    (heap : HeapOk P m.state.refs) : HeapOk P (evaluateNative root m fiber yielding table).machine.state.refs := by
  unfold evaluateNative
  split
  · split
    · exact heap
    · exact primitive_heap root m.completedExits table m fiber yielding held P sites heap
  · exact exit_scoped_heap root m fiber yielding _ held P sites heap
  · exact exit_scoped_heap root m fiber yielding _ held P sites heap
  · exact primitive_heap root m.completedExits table m fiber yielding held P sites heap

/-- A charged or forced-yield native iteration retains the source premise for its writer. -/
theorem iteration_heap (root : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (owned : ConfigurationAt root m)
    (held : FiberAt root fiber) (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding).machine.state.refs := by
  have charged := count_at root _ (loop_top_at root fiber held)
  unfold iteration
  dsimp only
  split
  · rename_i it found
    have retained := yield_at root m _ yielding it owned charged found
    have heapNext : HeapOk P it.machine.state.refs := by
      unfold injectYield at found
      split at found
      · cases found; exact heap
      · cases found
    exact native_heap root table it.machine it.fiber it.yielding retained.fiber P sites heapNext
  · exact native_heap root table m _ yielding charged P sites heap

/-- Every actual command keeps the cell predicate while its current writer has source ownership. -/
theorem command_heap (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) (rest : List SourceCommand) (owned : ConfigurationAt root m)
    (P : Val → Prop) (sites : SitesKeep root P) (heap : HeapOk P m.state.refs) :
    HeapOk P (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1.state.refs := by
  have looked (id : FiberId) (fiber : SourceFiber) (found : m.fiber? id = some fiber) : FiberAt root fiber :=
    configuration_fiber root m id fiber owned found
  fun_cases driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest
  case case5 id yielding fiber found =>
    rw [settle_refs]
    exact iteration_heap root table m fiber yielding owned (looked id fiber found) P sites heap
  case case7 id yielding fiber found =>
    rw [settle_refs]
    exact native_heap root table m fiber yielding (looked id fiber found) P sites heap
  case case16 id race raceFound program more programs blocked host hostFound spawned child spawnedEq updated =>
    have kept := spawn_refs root table m host program ⟨true, true, .interruptible⟩ (race.nextSite.getD [])
    change (launchEntrant (interpOf root table) id m host program (race.nextSite.getD [])).1.state.refs = m.state.refs at kept
    rw [spawnedEq] at kept
    exact kept ▸ heap
  case case17 id child race fiber fiberFound raceFound updated exit exited changed nested observed =>
    have kept := observer_refs root table child exit (updated, []) (.raceCallback id)
    rw [observed] at kept
    exact kept ▸ heap
  case case22 id yielding race raceFound updated fiber found exit accepted code changed =>
    rw [settle_refs]; exact heap
  case case23 id yielding race raceFound updated fiber found missing name before parked =>
    rw [settle_refs]; exact heap
  case case27 host yielding kind fiber found changed =>
    rw [settle_refs]; exact heap
  case case35 id exit observer changed nested observed =>
    have kept := observer_refs root table id exit (m, []) observer
    rw [observed] at kept; exact kept ▸ heap
  case case39 host yielding children fiber found frame changed =>
    rw [settle_refs]; exact heap
  case case40 mode scope target who extra changed nested linked =>
    have kept := link_refs root table m mode scope target who extra
    rw [linked] at kept; exact kept ▸ heap
  case case42 id exit fiber found changed nested finished =>
    have kept := exit_fiber_refs root table m {fiber with running := false} exit
    rw [finished] at kept; exact kept ▸ heap
  case case43 completions state found drainedPair =>
    have kept := drain_refs {m with state} completions
    have stateRefs : state.refs = m.state.refs := by
      have h : ((interpOf root table).dueResumes m.state).2.refs = m.state.refs := rfl
      rw [found] at h; exact h
    rw [kept, stateRefs]; exact heap
  case case44 list phase =>
    change HeapOk P (Stores.wakeList list phase m.state).refs
    unfold Stores.wakeList
    split <;> exact heap
  all_goals simp only [RunMachine.emit, RunMachine.update, modify_state]
  all_goals exact heap

end Effect4.Program.SourceScope
