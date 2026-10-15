import Effect4.Laws.Program.AnswerSlots.InitializedQueueSettlement
import Effect4.Laws.Program.AnswerSlots.InitializedDriver
import Effect4.Laws.Program.Guard.NativeQueueAssembly

/-!
Concept: store-typing R4 and reactive-scheduling R12.
Question: the actual loop and delivery cuts retain the initialized pending-command word.
Reach: actual guarded lookup, complete native/charged production and real settlement.
Limit: fixed administrative cuts and outside decisions are the coordinator's shared driver.
Consumer: command_guarded and both crew log-history endpoints.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Native delivery joins its actual source commands with the reserved old queue tail. -/
theorem QueueAt.native_settled (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (rest : List Guard.NCmd)
    (state : Guard.GuardState machine) (lookup : machine.fiber? fiber.id = some fiber)
    (running : fiber.running = true) (held : QueueAt spec machine rest)
    (guard : Guard.GuardQueue spec.root spec.table machine rest)
    (fresh : fiber.id ∉ rest.filterMap (Guard.commandOwner machine))
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    QueueAt spec (Machine.settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).1
      (Machine.settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).2 := by
  have footprint := Moves.evaluateNative_footprint spec.root spec.table machine fiber yielding
  have growth := native_growth spec machine fiber yielding
  obtain ⟨old, found, edits⟩ := (Moves.evaluateNative_interference spec.root spec.table machine fiber yielding).lookup fiber.id fiber lookup
  exact QueueAt.settle spec machine fiber.id rest _ held guard
    (by rw [footprint.id]; exact fresh)
    (Guard.NativeState.evaluateNative_state spec.root spec.table state fiber yielding ⟨fiber, lookup⟩)
    (Guard.NativeStateLinks.evaluateNative_links spec.root spec.table machine fiber yielding)
    growth.1 growth.2 (native_returned spec fragment machine fiber yielding acting scopes) old
    (by rw [footprint.id]; exact found) (footprint.running.trans running) footprint.id
    (native_finished_stack spec machine fiber yielding)

/-- Charged loop evaluation joins its actual source commands with the reserved old queue tail. -/
theorem QueueAt.iteration_settled (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (rest : List Guard.NCmd)
    (state : Guard.GuardState machine) (lookup : machine.fiber? fiber.id = some fiber)
    (running : fiber.running = true) (held : QueueAt spec machine rest)
    (guard : Guard.GuardQueue spec.root spec.table machine rest)
    (fresh : fiber.id ∉ rest.filterMap (Guard.commandOwner machine))
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    QueueAt spec (Machine.settle fiber.id rest
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding)).1
      (Machine.settle fiber.id rest
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding)).2 := by
  have footprint := Moves.iteration_footprint spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding
  have growth := iteration_growth spec machine fiber yielding
  obtain ⟨old, found, edits⟩ := (Moves.iteration_interference spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding).lookup fiber.id fiber lookup
  exact QueueAt.settle spec machine fiber.id rest _ held guard
    (by rw [footprint.id]; exact fresh)
    (Guard.NativeState.iteration_state spec.root spec.table state fiber yielding ⟨fiber, lookup⟩)
    (Guard.NativeStateLinks.iteration_links spec.root spec.table machine fiber yielding)
    growth.1 growth.2 (iteration_returned spec fragment machine fiber yielding acting scopes) old
    (by rw [footprint.id]; exact found) (footprint.running.trans running) footprint.id
    (iteration_finished_stack spec machine fiber yielding)

/-- The actual native deliver command retains its full pending initialized demand. -/
theorem QueueAt.command_deliver (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List Guard.NCmd)
    (configuration : Configuration spec machine) (state : Guard.GuardState machine)
    (guard : Guard.GuardQueue spec.root spec.table machine (.deliver target yielding :: rest))
    (held : QueueAt spec machine (.deliver target yielding :: rest)) :
    letI := evaluatorFor spec.root spec.table
    QueueAt spec (driveStep (interpOf spec.root spec.table) machine (.deliver target yielding) rest).1
      (driveStep (interpOf spec.root spec.table) machine (.deliver target yielding) rest).2 := by
  letI := evaluatorFor spec.root spec.table
  obtain ⟨fiber, found, running, parked⟩ := guard.authority (.deliver target yielding) (List.mem_cons_self ..)
  have key := Guard.fiber_id_of_lookup found
  have lookup : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
  have owners := guard.owners
  simp only [List.filterMap_cons, Guard.commandOwner] at owners
  have fresh : fiber.id ∉ rest.filterMap (Guard.commandOwner machine) := key ▸ (List.nodup_cons.mp owners).1
  have after := QueueAt.native_settled spec fragment machine fiber yielding rest state lookup running held.tail
    (Guard.guardQueue_tail spec.root spec.table guard) fresh
    (configuration.frames fiber (List.mem_of_find?_eq_some found)) configuration.scopes
  simpa only [driveStep, found, key] using after

/-- The actual charged loop command retains its full pending initialized demand. -/
theorem QueueAt.command_loop (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List Guard.NCmd)
    (configuration : Configuration spec machine) (state : Guard.GuardState machine)
    (guard : Guard.GuardQueue spec.root spec.table machine (.loop target yielding :: rest))
    (held : QueueAt spec machine (.loop target yielding :: rest)) :
    letI := evaluatorFor spec.root spec.table
    QueueAt spec (driveStep (interpOf spec.root spec.table) machine (.loop target yielding) rest).1
      (driveStep (interpOf spec.root spec.table) machine (.loop target yielding) rest).2 := by
  letI := evaluatorFor spec.root spec.table
  obtain ⟨fiber, found, running, parked⟩ := guard.authority (.loop target yielding) (List.mem_cons_self ..)
  have key := Guard.fiber_id_of_lookup found
  have lookup : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
  have owners := guard.owners
  simp only [List.filterMap_cons, Guard.commandOwner] at owners
  have fresh : fiber.id ∉ rest.filterMap (Guard.commandOwner machine) := key ▸ (List.nodup_cons.mp owners).1
  have after := QueueAt.iteration_settled spec fragment machine fiber yielding rest state lookup running held.tail
    (Guard.guardQueue_tail spec.root spec.table guard) fresh
    (configuration.frames fiber (List.mem_of_find?_eq_some found)) configuration.scopes
  simpa only [driveStep, found, key] using after
end Effect4.Program.AnswerSlots.Initialized
