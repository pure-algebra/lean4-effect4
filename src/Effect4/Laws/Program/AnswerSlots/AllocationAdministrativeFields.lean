import Effect4.Laws.Program.AnswerSlots.AllocationFields

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the common pending allocation administrative and outside-decision assembly.
Dispatcher scheduling preserves the actual pending root projection and its saved reply demand.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Posting a task changes the actual dispatcher but retains the pending row observation. -/
theorem PendingConfiguration.postTask (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (owner : FiberId) (priority : Nat) (task : Task EffName EffThunk Val Err Defect FiberId Ann) (ready : ReplyTask task) :
    PendingConfiguration spec fragment (machine.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact PendingConfiguration.fields spec fragment _ _ before rfl rfl rfl
  · rename_i fiber found
    have member := RunMachine.mem_of_fiber? found
    have updated := PendingConfiguration.update spec fragment machine before
      {fiber with dispatcher := fiber.dispatcher.enqueue priority task}
      (before.frames fiber member) (before.waits fiber member)
      (before.childless fiber member) (before.unobserved fiber member)
      (DispatcherPredicate.enqueue ReplyTask fiber.dispatcher priority task (before.replies fiber member) ready)
    exact PendingConfiguration.fields spec fragment _ _ updated rfl rfl rfl

/-- Delivering owed tasks preserves the whole pending configuration. -/
theorem PendingConfiguration.drainOwed (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (due : List (Owed NCode)) (before : PendingConfiguration spec fragment machine)
    (ready : ∀ owed ∈ due, ReplyTask (.resume owed.waiter owed.token owed.code)) :
    PendingConfiguration spec fragment (drainOwed machine due).1 := by
  induction due generalizing machine with
  | nil => exact before
  | cons owed rest ih =>
    have first := ready owed (.head _)
    have tail : ∀ other ∈ rest, ReplyTask (.resume other.waiter other.token other.code) :=
      fun other member => ready other (.tail _ member)
    cases mode : owed.mode with
    | now => simpa only [Machine.drainOwed, mode] using ih machine before tail
    | scheduled owner priority =>
      simpa only [Machine.drainOwed, mode] using ih _ (PendingConfiguration.postTask spec fragment machine before
        owner priority (.resume owed.waiter owed.token owed.code) first) tail

/-- Draining one actual dispatcher retains pending rows and the allocation heap. -/
theorem PendingConfiguration.drain (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (owner : FiberId) (fiber : SourceScope.SourceFiber) (found : machine.fiber? owner = some fiber) :
    PendingConfiguration spec fragment ((machine.update {fiber with dispatcher := fiber.dispatcher.drain.2}).disarm owner) := by
  have member := RunMachine.mem_of_fiber? found
  have updated := PendingConfiguration.update spec fragment machine before
    {fiber with dispatcher := fiber.dispatcher.drain.2}
    (before.frames fiber member) (before.waits fiber member)
    (before.childless fiber member) (before.unobserved fiber member)
    (DispatcherPredicate.drain ReplyTask fiber.dispatcher (before.replies fiber member)).2
  exact PendingConfiguration.fields spec fragment _ _ updated rfl rfl rfl
/-- Starting the actual pending owner changes only administrative execution fields. -/
theorem PendingConfiguration.start (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) :
    PendingConfiguration spec fragment (machine.update {fiber with running := true, currentOpCount := 0}) :=
  PendingConfiguration.update spec fragment machine before _ (before.frames fiber member)
    (before.waits fiber member) (before.childless fiber member) (before.unobserved fiber member) (before.replies fiber member)

/-- A real matching pending resume reads the parked demand before replacing the current code. -/
theorem PendingConfiguration.resume (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (token : Nat) (code : NCode)
    (parked : fiber.parked = .withGuard token) (terminal : SourceScope.TerminalReply code)
    (ordinary : NoRaceReply code) :
    PendingConfiguration spec fragment (machine.update
      {fiber with
        parked := .notParked
        pending := fiber.pending.filter (fun p => p.token ≠ token)
        frame := {fiber.frame with current := code}}) := by
  obtain ⟨output, input, current, saved⟩ := PendingWaits.resume spec fragment _ fiber code
    (before.waits fiber member) (by rw [parked]; intro impossible; cases impossible) terminal ordinary
  exact PendingConfiguration.update spec fragment machine before _ ⟨input, output, current, saved⟩
    (fun impossible => (impossible rfl).elim) (before.childless fiber member) (before.unobserved fiber member) (before.replies fiber member)

/-- A pending childless, unobserved owner publishes and clears without a source callback. -/
theorem PendingConfiguration.finish (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (exit : ExitV) :
    PendingConfiguration spec fragment
      (exitFiber (interpOf spec.root spec.table) machine {fiber with running := false} exit).1 := by
  have children := before.childless fiber member
  have observers := before.unobserved fiber member
  simp only [exitFiber, children, List.isEmpty_nil, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, exitFiber.exitStore, RunFiber.publish, observers]
  have published : PendingConfiguration spec fragment (machine.update ({fiber with running := false}.publish exit)) := by
    apply PendingConfiguration.update spec fragment machine before
    · exact FrameAt.fields spec fragment _ _ _ (before.frames fiber member) rfl rfl
    · exact fun impossible => (impossible rfl).elim
    · exact children
    · exact observers
    · exact before.replies fiber member
  have emitted := PendingConfiguration.fields spec fragment _
    ((machine.update ({fiber with running := false}.publish exit)).emit [.exited fiber.id exit]) published rfl rfl rfl
  have cleared : PendingConfiguration spec fragment
      (((machine.update ({fiber with running := false}.publish exit)).emit [.exited fiber.id exit]).update
        (({fiber with running := false}.publish exit).cleared (interpOf spec.root spec.table))) := by
    refine PendingConfiguration.update spec fragment ((machine.update ({fiber with running := false}.publish exit)).emit [.exited fiber.id exit]) emitted (({fiber with running := false}.publish exit).cleared (interpOf spec.root spec.table)) ?_ ?_ rfl rfl (before.replies fiber member)
    · exact FrameAt.cleared spec fragment _ _ (FrameAt.fields spec fragment _ _ _ (before.frames fiber member) rfl rfl)
    · exact fun impossible => (impossible rfl).elim
  simpa only [RunFiber.publish, RunFiber.cleared, observers, children] using cleared

end Effect4.Program.AnswerSlots.AllocationAdapter
