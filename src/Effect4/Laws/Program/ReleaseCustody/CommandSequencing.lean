import Effect4.Laws.Program.ReleaseCustody.NativeParkDebit
import Effect4.Laws.Program.Guard.ReturnCommands

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
theorem nested_owner (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (next : Control.Fiber) (key : next.id = it.fiber.id)
    (nested : ReturnCommands.Nested root table it) (command : NCmd) (member : command ∈ it.nested)
    (owner : FiberId) (owns : commandOwner (it.machine.update next) command = some owner) :
    owner = next.id := by
  have simple (command : NCmd) (held : ReturnCommands.Simple command)
      (wrong : commandOwner (it.machine.update next) command = some owner) : False := by
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
      change (it.machine.race? rid).map Race.host = some owner at owns
      rw [found, Option.map_some] at owns
      exact (Option.some.inj owns).symm.trans (host.trans key.symm)

/-- Installing the returned owner gives every emitted command its checked saved stack.
Consumer: settle_queue, then loop and delivery command sequencing. -/
theorem nested_queue (root : NativeEff) (table : RowTable) (it : RuntimeShape.Iteration)
    (next old : Control.Fiber) (key : next.id = it.fiber.id)
    (stack : next.frame.stack = it.fiber.frame.stack)
    (found : it.machine.fiber? next.id = some old)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it) :
    QueueStable (it.machine.update next) it.nested := by
  intro command member owner owns fiber seen
  have same := nested_owner root table it next key nested command member owner owns
  subst owner
  have lookup := fiber_lookup_update_self found next rfl
  have eq := Option.some.inj (seen.symm.trans lookup)
  subst fiber
  rw [stack]
  exact nested_frames root table it nested returned command member

/-- Settling installs the checked returned frames in every outcome.
Consumer: loop and delivery command sequencing. -/
theorem settle_configuration (id : FiberId) (rest : List NCmd) (it : RuntimeShape.Iteration)
    (held : ConfigurationKept it.machine) (returned : Returned it) :
    ConfigurationKept (settle id rest it).1 := by
  have installed := configuration_update it.machine it.fiber held returned.fiber
  have stopped := configuration_update it.machine {it.fiber with running := false} held
    (fiber_fields it.fiber _ returned.fiber rfl rfl rfl)
  have cleared := configuration_update it.machine {it.fiber with parked := .notParked, pending := []} held
    ⟨returned.fiber.sequence, by intro wrong; exact False.elim (wrong rfl)⟩
  unfold settle
  split
  · exact installed
  · exact installed
  · split
    · exact cleared
    · exact stopped
  · exact installed
  · exact installed
  · exact stopped

/-- Settlement's new command prefix consumes exactly its returned owner's stack.
Consumer: full native command queue sequencing after old-tail transport. -/
theorem settle_queue (root : NativeEff) (table : RowTable) (id : FiberId) (rest : List NCmd)
    (it : RuntimeShape.Iteration) (old : Control.Fiber) (key : it.fiber.id = id)
    (found : it.machine.fiber? id = some old)
    (nested : ReturnCommands.Nested root table it) (returned : Returned it)
    (tail : QueueStable (settle id rest it).1 rest) :
    QueueStable (settle id rest it).1 (settle id rest it).2 := by
  have lookup : it.machine.fiber? it.fiber.id = some old := by rw [key]; exact found
  have frontQueue := nested_queue root table it it.fiber old rfl rfl lookup nested returned
  have stopped := nested_queue root table it {it.fiber with running := false} old rfl rfl lookup nested returned
  have cleared := nested_queue root table it {it.fiber with parked := .notParked, pending := []}
    old rfl rfl lookup nested returned
  have admin (machine : NativeMachine) (command : NCmd)
      (free : ∀ frames, CommandFrames command frames) : QueueStable machine [command] := by
    intro c member owner owns fiber seen
    rw [List.mem_singleton.mp member]
    exact free fiber.frame.stack
  cases outcome : it.outcome
  case continue_ =>
    simp only [settle, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue (admin _ (.loop id it.yielding) (fun _ => trivial))) tail
  case answered =>
    simp only [settle, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue (admin _ (.deliver id it.yielding) (fun _ => trivial))) tail
  case parked =>
    simp only [settle, outcome] at tail ⊢
    split
    · rename_i deferred
      simp only [deferred, if_true] at tail
      exact queue_append (queue_append cleared (admin _ (.loop id it.yielding) (fun _ => trivial))) tail
    · rename_i deferred
      simp only [deferred] at tail
      exact queue_append stopped tail
  case commands =>
    simp only [settle, outcome] at tail ⊢
    exact queue_append frontQueue tail
  case finished exit =>
    have empty := returned.finished exit outcome
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
    simp only [settle, outcome] at tail ⊢
    exact queue_append (queue_append frontQueue finish) tail
  case stuck why =>
    simp only [settle, outcome]
    exact queue_nil _

end Effect4.Program.ReleaseCustody.CommandSequencing
