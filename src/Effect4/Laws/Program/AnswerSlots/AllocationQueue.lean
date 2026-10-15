import Effect4.Laws.Program.AnswerSlots.AllocationFixed

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Consumer: the shared pending allocation coupled command/history producer.
The command profile retains actual administration while source ownership supplies reply admission.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- No application-only operation occurs before the actual source entry. -/
def PendingCommand : SourceScope.SourceCommand → Prop
  | .evaluate _ | .loop _ _ | .deliver _ _ | .interruptTarget _ _ _
    | .finish _ _ | .drainDue => True
  | .resume id token code => ReplyTask (.resume id token code)
  | _ => False

/-- Pending command shape has no store or ghost dependency. -/
def PendingQueue (commands : List SourceScope.SourceCommand) : Prop :=
  ∀ command ∈ commands, PendingCommand command

theorem PendingQueue.append (first last : List SourceScope.SourceCommand)
    (left : PendingQueue first) (right : PendingQueue last) : PendingQueue (first ++ last) := by
  intro command member
  rcases List.mem_append.mp member with member | member
  · exact left command member
  · exact right command member

theorem PendingQueue.cons (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (allowed : PendingCommand command) (held : PendingQueue rest) : PendingQueue (command :: rest) := by
  intro next member
  rcases List.mem_cons.mp member with same | member
  · rw [same]; exact allowed
  · exact held next member

theorem pending_queue_nil : PendingQueue [] := fun _ member => (List.not_mem_nil member).elim

/-- Actual nonaction native settlement emits only its disposition and due drain before the old queue. -/
theorem PendingNativeCut.queue (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration)
    (cut : PendingNativeCut spec fragment machine fiber result) (id : FiberId)
    (rest : List SourceScope.SourceCommand) (held : PendingQueue rest) :
    PendingQueue (settle id rest result).2 := by
  have nested : PendingQueue result.nested := by
    intro command member
    rw [cut.effects.2 command member]
    trivial
  simp only [settle, cut.effects.1]
  cases outcome : result.outcome with
  | continue_ =>
    simp only [settleOutcome, outcome, List.append_assoc, List.singleton_append]
    exact PendingQueue.append _ _ nested (PendingQueue.cons _ _ trivial held)
  | answered =>
    simp only [settleOutcome, outcome, List.append_assoc, List.singleton_append]
    exact PendingQueue.append _ _ nested (PendingQueue.cons _ _ trivial held)
  | parked =>
    simp only [settleOutcome, outcome, List.append_assoc, List.singleton_append]
    split
    · exact PendingQueue.append _ _ nested (PendingQueue.cons _ _ trivial held)
    · exact PendingQueue.append _ _ nested held
  | commands =>
    simp only [settleOutcome, outcome]
    exact PendingQueue.append _ _ nested held
  | finished exit =>
    simp only [settleOutcome, outcome, List.append_assoc, List.singleton_append]
    exact PendingQueue.append _ _ nested (PendingQueue.cons _ _ trivial held)
  | stuck why =>
    simp only [settleOutcome, outcome]
    exact pending_queue_nil

/-- Draining owed entries emits only pending resumes. -/
theorem pending_drain_queue (machine : NativeMachine) (due : List (Owed NCode))
    (ready : ∀ owed ∈ due, ReplyTask (.resume owed.waiter owed.token owed.code)) :
    PendingQueue (drainOwed machine due).2 := by
  induction due generalizing machine with
  | nil => exact pending_queue_nil
  | cons owed rest ih =>
    have first := ready owed (.head _)
    have tail : ∀ other ∈ rest, ReplyTask (.resume other.waiter other.token other.code) :=
      fun other member => ready other (.tail _ member)
    cases mode : owed.mode with
    | now => simpa only [drainOwed, mode] using PendingQueue.cons (.resume owed.waiter owed.token owed.code) _ first (ih machine tail)
    | scheduled owner priority => simpa only [drainOwed, mode] using ih (machine.postTask owner priority (.resume owed.waiter owed.token owed.code)) tail

/-- Fixed pending commands emit only pending administration before the retained old queue. -/
theorem pending_fixed_queue (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (before : PendingConfiguration spec fragment machine) (allowed : FixedAllowed command) (held : PendingQueue rest) :
    letI := evaluatorFor spec.root spec.table
    PendingQueue (driveStep (interpOf spec.root spec.table) machine command rest).2 := by
  letI := evaluatorFor spec.root spec.table
  cases command <;> simp only [FixedAllowed] at allowed
  case evaluate id =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · exact PendingQueue.cons _ _ trivial held
  case resume id token code =>
    simp only [driveStep]
    split
    · exact held
    · split
      · split
        · exact PendingQueue.cons _ _ trivial held
        · exact held
      · exact held
  case interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact PendingQueue.cons _ _ trivial held
      · exact held
  case finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have children := before.childless fiber (RunMachine.mem_of_fiber? found)
      have observers := before.unobserved fiber (RunMachine.mem_of_fiber? found)
      simp only [exitFiber, children, List.isEmpty_nil, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, exitFiber.exitStore, RunFiber.publish, observers]
      exact PendingQueue.cons _ _ trivial held
  case drainDue => exact PendingQueue.append _ _ (pending_drain_queue _ _ (due_replies spec.root spec.table machine.state)) held
  case wake => exact held

/-- Source ownership supplies the actual pending resume admission in race-free applications. -/
theorem pending_reply_noRace (root : NativeEff) (raceFree : SourceScope.RaceFreeSource root)
    (code : NCode) (source : SourceScope.CodeAt root code) : NoRaceReply code := by
  intro race exit same
  rw [same] at source
  exact raceFree.not_race source.1

/-- The fixed subprofile reads reply admission at the actual command consumption. -/
theorem PendingCommand.fixed (command : SourceScope.SourceCommand) (allowed : PendingCommand command)
    (fixed : AnswerFlow.ghostAdvancing command = false) :
    FixedAllowed command := by
  cases command <;> simp only [PendingCommand] at allowed
  case evaluate => trivial
  case loop => cases fixed
  case deliver => cases fixed
  case resume id token code => exact allowed
  case interruptTarget => trivial
  case finish => trivial
  case drainDue => trivial
/-- Detached pending tasks retain their exact ordinary reply admission. -/
abbrev PendingSnapshot (tasks : List SourceScope.SourceTask) : Prop := DispatcherPredicate.Tasks ReplyTask tasks

/-- Each actual admitted task emits only pending commands. -/
theorem pending_task_queue (task : SourceScope.SourceTask) (ready : ReplyTask task) : PendingQueue (taskCmds task) := by
  cases task with
  | start child => exact PendingQueue.cons _ _ trivial (PendingQueue.cons _ _ trivial pending_queue_nil)
  | resume owner token code => exact PendingQueue.cons _ _ ready (PendingQueue.cons _ _ trivial pending_queue_nil)
  | wake list phase => exact False.elim ready

end Effect4.Program.AnswerSlots.AllocationAdapter
