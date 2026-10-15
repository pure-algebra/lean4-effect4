import Effect4.Laws.Program.AnswerSlots.AllocationDecisionEdits
import Effect4.Laws.Machine.LiftCoupledFact

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: Atomic, Queue and Timeout initialization-to-application histories.
The existing coupled scheduler carries the actual pending configuration until application entry.
The command producer chooses one world for machine, commands and detached tasks together.
Application command and entry producers remain explicit; this adapter adds no scheduler recursion.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program
universe u v

/-- Pending allocation and active application facts share the same actual machine. -/
def AttachedState {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (P : V → NativeMachine → Prop) : Option V → NativeMachine → Prop
  | none, machine => PendingConfiguration spec fragment machine
  | some world, machine => P world machine

/-- The command profile changes only at actual application entry. -/
def AttachedQueue {V : Type u} (Q : V → NativeMachine → List Guard.NCmd → Prop) :
    Option V → NativeMachine → List Guard.NCmd → Prop
  | none, _, commands => PendingQueue commands
  | some world, machine, commands => Q world machine commands

/-- Detached tasks use the same chosen application world as the machine and command queue. -/
def AttachedTasks {V : Type u} (R : V → NativeMachine → List Guard.NTask → Prop) :
    Option V → NativeMachine → List Guard.NTask → Prop
  | none, _, tasks => PendingSnapshot tasks
  | some world, machine, tasks => R world machine tasks

/-- World transitions carry no extra order restriction; local postconditions carry the application facts. -/
def attachmentOrder (V : Type u) : Effect4.Laws.Effects.WorldOrder (Option V) where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial

/-- One shared outside-decision adapter consumes actual pending commands and the existing active driver. -/
theorem coupled_decision {W : Type v} {V : Type u} (spec : Spec)
    (fragment : SourceScope.Fragment spec.root) (p : Effect4.Laws.Effects.WorldOrder V)
    (J : W → NativeMachine → Prop)
    (I : W → NativeMachine → List Guard.NCmd → Prop)
    (O : W → NativeMachine → List Guard.NTask → Prop)
    (A : W → NativeMachine → RunDecision EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (P : V → NativeMachine → Prop) (Q : V → NativeMachine → List Guard.NCmd → Prop)
    (R : V → NativeMachine → List Guard.NTask → Prop)
    (active : letI := evaluatorFor spec.root spec.table
      Lift.CoupledDecision (p := p) (interp := interpOf spec.root spec.table)
        (J := J) (I := I) (O := O) (A := A) (P := P) (Q := Q) (R := R))
    (pending_step : letI := evaluatorFor spec.root spec.table
      ∀ tasks world machine command rest, machine.stuck = none →
        Lift.Guarded J I O tasks world machine (command :: rest) →
        Lift.Guarded (AttachedState spec fragment P) (AttachedQueue Q) (AttachedTasks R)
          tasks none machine (command :: rest) →
        ∃ next, Lift.Guarded (AttachedState spec fragment P) (AttachedQueue Q) (AttachedTasks R)
          tasks next (driveStep (interpOf spec.root spec.table) machine command rest).1
          (driveStep (interpOf spec.root spec.table) machine command rest).2) :
    letI := evaluatorFor spec.root spec.table
    Lift.CoupledDecision (p := attachmentOrder V) (interp := interpOf spec.root spec.table)
      (J := J) (I := I) (O := O) (A := A)
      (P := AttachedState spec fragment P) (Q := AttachedQueue Q) (R := AttachedTasks R) := by
  letI := evaluatorFor spec.root spec.table
  refine {
    step := ?_, nil := ?_, drain := ?_, ran := ?_, task := ?_, skip := ?_,
    clockNone := ?_, clockSome := ?_, evaluate := ?_, yield := ?_, interrupt := ?_, middleware := ?_, answer := ?_ }
  · intro tasks world extra machine command rest running base held
    cases extra with
    | none =>
      obtain ⟨next, post⟩ := pending_step tasks world machine command rest running base held
      exact ⟨next, trivial, post⟩
    | some current =>
      obtain ⟨next, moved, post⟩ := active.step tasks world current machine command rest running base held
      exact ⟨some next, trivial, post⟩
  · intro extra machine
    cases extra with
    | none => exact fun task member => (List.not_mem_nil member).elim
    | some current => exact active.nil current machine
  · intro world extra machine owner fiber base held found
    cases extra with
    | none => exact ⟨held.drain spec fragment machine owner fiber found,
        (DispatcherPredicate.drain ReplyTask fiber.dispatcher (held.replies fiber (RunMachine.mem_of_fiber? found))).1⟩
    | some current => exact active.drain world current machine owner fiber base held found
  · intro world extra machine owner task base held
    cases extra with
    | none => exact held.fields spec fragment _ _ rfl rfl rfl
    | some current => exact active.ran world current machine owner task base held
  · intro world extra machine owner task tasks base held running reserved snapshot
    cases extra with
    | none => exact ⟨pending_task_queue task (snapshot task (.head _)),
        fun other member => snapshot other (.tail _ member)⟩
    | some current => exact active.task world current machine owner task tasks base held running reserved snapshot
  · intro extra machine task tasks snapshot
    cases extra with
    | none => exact fun other member => snapshot other (.tail _ member)
    | some current => exact active.skip current machine task tasks snapshot
  · intro world extra machine millis state base held running clock
    cases extra with
    | none =>
      have post := held.clock spec fragment machine millis
      rw [clock] at post
      exact ⟨none, trivial, post⟩
    | some current =>
      obtain ⟨next, moved, post⟩ := active.clockNone world current machine millis state base held running clock
      exact ⟨some next, trivial, post⟩
  · intro world extra machine millis owed state base held running clock
    cases extra with
    | none =>
      have post := held.clock spec fragment machine millis
      rw [clock] at post
      have ready := clock_replies spec.root spec.table machine.state millis owed (congrArg Prod.fst clock)
      have admitted : ∀ actual ∈ [owed], ReplyTask (.resume actual.waiter actual.token actual.code) := by
        intro actual member
        rw [List.mem_singleton.mp member]
        exact ready
      exact ⟨none, trivial, post.drainOwed spec fragment _ [owed] admitted,
        fun _ => PendingQueue.append _ _ (pending_drain_queue _ [owed] admitted)
          (PendingQueue.cons _ _ trivial pending_queue_nil)⟩
    | some current =>
      obtain ⟨next, moved, post, queued⟩ := active.clockSome world current machine millis owed state base held running clock
      exact ⟨some next, trivial, post, queued⟩
  · intro world extra machine id base held running
    cases extra with
    | none => exact pending_task_queue (.start id) trivial
    | some current => exact active.evaluate world current machine id base held running
  · intro world extra machine id verdict base held
    cases extra with
    | none => exact held.yield spec fragment machine id verdict
    | some current => exact active.yield world current machine id verdict base held
  · intro world extra machine who reason target fiber base held found
    cases extra with
    | none => exact held.interruptEdit spec fragment machine who reason target fiber found
    | some current => exact active.interrupt world current machine who reason target fiber base held found
  · intro world extra machine base held
    cases extra with
    | none => exact held.fields spec fragment _ _ rfl rfl rfl
    | some current => exact active.middleware world current machine base held
  · intro world extra machine id token answer base held running admitted
    cases extra with
    | none =>
      have prepared := held.prepare spec fragment machine id token answer
      have ready := prepared_reply_task spec.root spec.table machine id token answer
      have queue : PendingQueue [.drainDue] := PendingQueue.cons _ _ trivial pending_queue_nil
      exact ⟨none, trivial, prepared.fixed spec fragment _ (.resume id token _) [.drainDue] ready,
        fun _ => ⟨pending_fixed_queue spec fragment _ (.resume id token _) [.drainDue] prepared ready queue,
          fun task member => (List.not_mem_nil member).elim⟩⟩
    | some current =>
      obtain ⟨next, moved, post⟩ := active.answer world current machine id token answer base held running admitted
      exact ⟨some next, trivial, post⟩
end Effect4.Program.AnswerSlots.AllocationAdapter
