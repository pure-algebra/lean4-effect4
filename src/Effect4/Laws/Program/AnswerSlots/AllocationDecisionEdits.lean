import Effect4.Laws.Program.AnswerSlots.AllocationTasks
import Effect4.Laws.Program.AnswerSlots.AllocationQueue
import Effect4.Laws.Program.NativeHeapReplies
import Effect4.Laws.Program.Guard.AnswerDecision

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared bare-prefix coupled decision/history producer.
Actual reply preparation and scheduler edits retain the exact pending configuration.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- External reply preparation retains exact initialization contents and allocation counts. -/
theorem PendingConfiguration.prepare (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    PendingConfiguration spec fragment {machine with
      state := (prepareAsyncAnswer (interpOf spec.root spec.table) machine id token answer).1} := by
  apply PendingConfiguration.store_fields spec fragment machine _ before
  · exact SourceScope.prepare_reply_refs spec.root spec.table machine id token answer
  · exact congrArg (fun store : DeferredStore => store.cells.length)
      (Guard.AnswerDecision.prepareAsyncAnswer_shape spec.root spec.table machine id token answer).2.1

/-- The real clock hook writes timers without changing the initialized references or deferred count. -/
theorem PendingConfiguration.clock (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine) (millis : ClockMillis) :
    PendingConfiguration spec fragment {machine with state := ((interpOf spec.root spec.table).clockStep millis machine.state).2} := by
  apply PendingConfiguration.store_fields spec fragment machine _ before
  · rfl
  · rfl

/-- Recording the next yield decision retains the actual pending row observation. -/
theorem PendingConfiguration.yield (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine) (id : FiberId) (verdict : Bool) :
    PendingConfiguration spec fragment (machine.modify id fun fiber => {fiber with yieldOverride := some verdict}) := by
  unfold RunMachine.modify
  split
  · exact before
  · rename_i fiber found
    have member := RunMachine.mem_of_fiber? found
    exact PendingConfiguration.update spec fragment machine before _ (before.frames fiber member)
      (before.waits fiber member) (before.childless fiber member) (before.unobserved fiber member) (before.replies fiber member)

/-- The actual outside interruption uses the same checked pending row update. -/
theorem PendingConfiguration.interruptEdit (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) (fiber : SourceScope.SourceFiber)
    (found : machine.fiber? target = some fiber) :
    PendingConfiguration spec fragment (Lift.interruptEdit (interpOf spec.root spec.table) machine who extra target fiber) := by
  have changed := PendingConfiguration.interruption spec fragment machine before fiber
    (RunMachine.mem_of_fiber? found) (interruptCause (interpOf spec.root spec.table) who extra fiber.id)
  apply PendingConfiguration.fields spec fragment _ _ changed
  all_goals unfold Lift.interruptEdit
  all_goals dsimp only
  all_goals split <;> rfl
end Effect4.Program.AnswerSlots.AllocationAdapter
