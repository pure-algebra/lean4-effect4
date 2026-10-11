import Effect4.Laws.Program.ReleaseCustody.NativeParkDebit
import Effect4.Laws.Program.Guard.ReturnCommands
import Effect4.Laws.Program.ReleaseCustody.NativeMachineShape

/-!
Concept: scope-lifetime-finalization R11.
Question: saved-frame and queued-owner sequencing serves Execution.history and Workers.releases_step.
Reach: actual native command shapes, existing Guard ownership and returned saved frames.
Limit: structural transports alone establish neither custody funding nor admitted-history closure.
Unlock: evaluator installation protects pending overwrite commands without another source grammar.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CommandSequencing
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.Sequencing Effect4.Program.ReleaseCustody.CommandStacks

/-- Installing a fiber with checked saved frames retains the other stored fibers.
Consumer: command settlement and matching resume updates. -/
theorem configuration_update (m : NativeMachine) (fiber : Control.Fiber)
    (held : ConfigurationKept m) (next : FiberKept fiber) : ConfigurationKept (m.update fiber) := by
  intro other member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq]
  split
  · exact next
  · exact held old present

/-- Metadata changes retain a fiber's current, saved frames and parked reply condition.
Consumer: native command updates and evaluator settlement. -/
theorem fiber_fields (fiber next : Control.Fiber) (held : FiberKept fiber)
    (current : next.frame.current = fiber.frame.current) (stack : next.frame.stack = fiber.frame.stack)
    (park : next.parked = fiber.parked) : FiberKept next := by
  refine ⟨?_, ?_⟩
  · rw [current, stack]
    exact held.sequence
  · intro parked
    rw [stack]
    exact held.parked (park ▸ parked)

/-- The native nested-command census requires only the returned owner's saved frames.
Consumer: nested_queue, followed by actual evaluator settlement. -/
theorem nested_frames (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it) :
    ∀ command ∈ it.nested, CommandFrames command it.fiber.frame.stack := by
  have simple (command : NCmd) (held : ReturnCommands.Simple command) :
      CommandFrames command it.fiber.frame.stack := by
    cases command <;> cases held <;> trivial
  cases nested with
  | simple commands => exact fun command member => simple command (commands command member)
  | owned outcome front last commands basic isLocal =>
    intro command member
    rw [commands] at member
    rcases List.mem_append.mp member with before | after
    · exact simple command (basic command before)
    · have same := List.mem_singleton.mp after
      subst command
      have noAdd := returned.commands outcome
      cases last <;> dsimp only [ReturnCommands.Local] at isLocal
      all_goals aesop (add safe apply [noAdd])
  | registration outcome rid race found host park commands =>
    intro command member
    rw [commands] at member
    have noAdd := returned.commands outcome
    rcases List.mem_cons.mp member with first | later
    · rw [first]; trivial
    · rw [List.mem_singleton.mp later]
      exact noAdd

/-- All owned nested commands name the returned fiber; simple commands have no owner.
Consumer: nested_queue at the actual keyed installation. -/
theorem nested_owner_at (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (machine : NativeMachine) (races : machine.races = it.machine.races)
    (next : Control.Fiber) (key : next.id = it.fiber.id)
    (nested : ReturnCommands.Nested root table it) (command : NCmd) (member : command ∈ it.nested)
    (owner : FiberId) (owns : commandOwner machine command = some owner) :
    owner = next.id := by
  have simple (command : NCmd) (held : ReturnCommands.Simple command)
      (wrong : commandOwner machine command = some owner) : False := by
    cases command <;> cases held <;> cases wrong
  cases nested with
  | simple commands => exact False.elim (simple command (commands command member) owns)
  | owned outcome front last commands basic isLocal =>
    rw [commands] at member
    rcases List.mem_append.mp member with before | after
    · exact False.elim (simple command (basic command before) owns)
    · have same := List.mem_singleton.mp after
      subst command
      cases last <;> dsimp only [ReturnCommands.Local] at isLocal
      all_goals aesop (add norm simp [commandOwner])
  | registration outcome rid race found host park commands =>
    rw [commands] at member
    rcases List.mem_cons.mp member with first | later
    · rw [first] at owns
      cases owns
    · rw [List.mem_singleton.mp later] at owns
      change (machine.race? rid).map Race.host = some owner at owns
      have sameRaces : machine.race? rid = it.machine.race? rid := by
        simp only [RunMachine.race?, races]
      rw [sameRaces] at owns
      rw [found, Option.map_some] at owns
      exact (Option.some.inj owns).symm.trans (host.trans key.symm)

/-- The installation instance retains the original owner statement. -/
theorem nested_owner (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (next : Control.Fiber) (key : next.id = it.fiber.id)
    (nested : ReturnCommands.Nested root table it) (command : NCmd) (member : command ∈ it.nested)
    (owner : FiberId) (owns : commandOwner (it.machine.update next) command = some owner) :
    owner = next.id :=
  nested_owner_at root table it _ rfl next key nested command member owner owns

/-- The actual selected row supplies the returned stack after message application.
Consumer: outcome queue closure after the actual owner is read again. -/
theorem nested_queue_at (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (machine : NativeMachine) (races : machine.races = it.machine.races)
    (next : Control.Fiber) (key : next.id = it.fiber.id)
    (stack : next.frame.stack = it.fiber.frame.stack)
    (found : machine.fiber? next.id = some next)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it) :
    QueueStable machine it.nested := by
  intro command member owner owns fiber seen
  have same := nested_owner_at root table it machine races next key nested command member owner owns
  subst owner
  have eq := Option.some.inj (seen.symm.trans found)
  subst fiber
  rw [stack]
  exact nested_frames root table it nested returned command member

/-- Installing the returned owner gives every emitted command its checked saved stack.
Consumer: settle_queue, then loop and delivery command sequencing. -/
theorem nested_queue (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (next old : Control.Fiber) (key : next.id = it.fiber.id)
    (stack : next.frame.stack = it.fiber.frame.stack)
    (found : it.machine.fiber? next.id = some old)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it) :
    QueueStable (it.machine.update next) it.nested := by
  exact nested_queue_at root table it _ rfl next key stack
    (fiber_lookup_update_self found next rfl) nested returned

/-- Outcome disposition changes only the stopped and parked metadata.
Consumer: settlement configuration closure after the shared message transfer. -/
theorem settleOutcome_configuration (id : FiberId) (rest : List NCmd) (it : RuntimeShape.Iteration)
    (held : ConfigurationKept it.machine) (returned : FiberKept it.fiber) :
    ConfigurationKept (settleOutcome id rest it).1 := by
  have next : FiberKept (Settle.settledFiber it) := by
    cases outcome : it.outcome with
    | parked =>
      simp only [Settle.settledFiber, outcome]
      split
      · exact ⟨returned.sequence, fun wrong => False.elim (wrong rfl)⟩
      · exact fiber_fields it.fiber _ returned rfl rfl rfl
    | stuck why =>
      simp only [Settle.settledFiber, outcome]
      exact fiber_fields it.fiber _ returned rfl rfl rfl
    | _ => simpa only [Settle.settledFiber, outcome] using returned
  have installed := configuration_update it.machine _ held next
  rw [Settle.settleOutcome_machine]
  cases it.outcome with
  | stuck why => exact installed
  | _ => exact installed

/-- Settling installs the checked returned frames in every outcome.
Consumer: loop and delivery command sequencing. -/
theorem settle_configuration (id : FiberId) (rest : List NCmd) (it : RuntimeShape.Iteration)
    (held : ConfigurationKept it.machine) (returned : Returned it) :
    ConfigurationKept (settle id rest it).1 := by
  cases messages : it.edits with
  | nil =>
    simpa only [settle, messages] using settleOutcome_configuration id rest it held returned.fiber
  | cons message tail =>
    have installed := configuration_update it.machine it.fiber held returned.fiber
    have changed := NativeMachineShape.interferes
      (Moves.InterferesWithLookup.fiberEdits (message :: tail) (it.machine.update it.fiber)).backward installed
    simp only [settle, messages]
    split
    · exact changed
    · rename_i owner found
      exact settleOutcome_configuration id rest _ changed
        (changed owner (List.mem_of_find?_eq_some found))

/-- Outcome disposition adds administrative commands or a finish on an empty stack.
Consumer: settlement queue closure before and after addressed messages. -/
theorem settleOutcome_queue (id : FiberId) (rest : List NCmd)
    (it : RuntimeShape.Iteration) (old : Control.Fiber) (key : it.fiber.id = id)
    (found : it.machine.fiber? id = some old)
    (front : ∀ next : Control.Fiber, next.id = it.fiber.id →
      next.frame.stack = it.fiber.frame.stack → QueueStable (it.machine.update next) it.nested)
    (finished : ∀ exit, it.outcome = .finished exit → it.fiber.frame.stack = [])
    (tail : QueueStable (settleOutcome id rest it).1 rest) :
    QueueStable (settleOutcome id rest it).1 (settleOutcome id rest it).2 := by
  have lookup : it.machine.fiber? it.fiber.id = some old := by rw [key]; exact found
  have frontQueue := front it.fiber rfl rfl
  have stopped := front {it.fiber with running := false} rfl rfl
  have cleared := front {it.fiber with parked := .notParked, pending := []} rfl rfl
  have admin (machine : NativeMachine) (command : NCmd)
      (free : ∀ frames, CommandFrames command frames) : QueueStable machine [command] := by
    intro c member owner owns fiber seen
    rw [List.mem_singleton.mp member]
    exact free fiber.frame.stack
  cases outcome : it.outcome
  case continue_ =>
    simp only [settleOutcome, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue (admin _ (.loop id it.yielding) (fun _ => trivial))) tail
  case answered =>
    simp only [settleOutcome, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue (admin _ (.deliver id it.yielding) (fun _ => trivial))) tail
  case parked =>
    simp only [settleOutcome, outcome] at tail ⊢
    split
    · rename_i deferred
      simp only [deferred, if_true] at tail
      exact queue_append (queue_append cleared (admin _ (.loop id it.yielding) (fun _ => trivial))) tail
    · rename_i deferred
      simp only [deferred] at tail
      exact queue_append stopped tail
  case commands =>
    simp only [settleOutcome, outcome] at tail ⊢
    exact queue_append frontQueue tail
  case finished exit =>
    have empty := finished exit outcome
    have finish : QueueStable (it.machine.update it.fiber) [.finish id exit] := by
      intro c member owner owns fiber seen
      rw [List.mem_singleton.mp member] at owns ⊢
      have same : id = owner := Option.some.inj owns
      subst owner
      have final := fiber_lookup_update_self lookup it.fiber rfl
      rw [key] at final
      have eq := Option.some.inj (seen.symm.trans final)
      subst fiber
      exact empty
    simp only [settleOutcome, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue finish) tail
  case stuck why =>
    simp only [settleOutcome, outcome]
    exact queue_nil _


/-- Settlement's new command prefix consumes exactly its returned owner's stack.
Consumer: full native command queue sequencing after old-tail transport. -/
theorem settle_queue (root : NativeEff) (table : RowTable) (id : FiberId) (rest : List NCmd)
    (it : RuntimeShape.Iteration) (old : Control.Fiber) (key : it.fiber.id = id)
    (found : it.machine.fiber? id = some old)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it)
    (tail : QueueStable (settle id rest it).1 rest) :
    QueueStable (settle id rest it).1 (settle id rest it).2 := by
  have lookup : it.machine.fiber? it.fiber.id = some old := by rw [key]; exact found
  cases messages : it.edits with
  | nil =>
    simp only [settle, messages] at tail ⊢
    exact settleOutcome_queue id rest it old key found
      (fun next same stack => nested_queue root table it next old same stack
        (by rw [same]; exact lookup) nested returned) returned.finished tail
  | cons message messagesTail =>
    let changed := applyFiberEdits (message :: messagesTail) (it.machine.update it.fiber)
    have installed := fiber_lookup_update_self lookup it.fiber rfl
    obtain ⟨owner, ownerFound, word⟩ :=
      (Moves.InterferesWithLookup.fiberEdits (message :: messagesTail) (it.machine.update it.fiber)).lookup
        it.fiber.id it.fiber installed
    have same := word.id
    have stack := StackRegion.other_edits_stack word
    let next : RuntimeShape.Iteration := {it with
      machine := changed.1
      fiber := owner
      nested := changed.2 ++ it.nested
      edits := []}
    have front : ∀ fresh : Control.Fiber, fresh.id = next.fiber.id →
        fresh.frame.stack = next.fiber.frame.stack → QueueStable (next.machine.update fresh) next.nested := by
      intro fresh freshId freshStack
      apply queue_append
      · intro command member owner owns fiber seen
        obtain ⟨target, eq⟩ := (RunMachine.applyFiberEdits_shape
          (message :: messagesTail) (it.machine.update it.fiber)).2 command member
        subst command
        trivial
      · have races := congrArg RunMachine.races (RunMachine.applyFiberEdits_shape
          (message :: messagesTail) (it.machine.update it.fiber)).1
        apply nested_queue_at root table it (next.machine.update fresh) races fresh
          (freshId.trans same) (freshStack.trans stack) _ nested returned
        rw [freshId, same]
        exact fiber_lookup_update_self ownerFound fresh (freshId.trans same)
    have finished : ∀ exit, next.outcome = .finished exit → next.fiber.frame.stack = [] := by
      intro exit result
      exact stack.trans (returned.finished exit result)
    have selected : next.machine.fiber? id = some owner := by
      rw [← key]
      exact ownerFound
    simp only [settle, messages, ownerFound] at tail ⊢
    exact settleOutcome_queue id rest next owner (same.trans key) selected front finished tail

end Effect4.Program.ReleaseCustody.CommandSequencing
