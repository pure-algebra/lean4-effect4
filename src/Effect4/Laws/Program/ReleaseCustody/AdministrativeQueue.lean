import Effect4.Laws.Program.ReleaseCustody.AdministrativeKept
import Effect4.Laws.Program.Guard.Command

/-!
Concept: scope-lifetime-finalization R11.
Question: pending-command stack closure serves Execution.history and Workers.releases_step.
Reach: actual native command lists and the existing Guard owner relation.
Limit: queue closure establishes neither release funding nor progress.
Unlock: the complete command induction combines this condition with stored-frame sequencing.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Effect4.Program.ReleaseCustody.AdministrativeQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.Sequencing Effect4.Program.ReleaseCustody.CommandStacks

/-- These commands place no constraint on an owner's saved stack.
Consumer: the concrete emitted-command census and queue assembly. -/
def Free (command : NCmd) : Prop := ∀ frames, CommandFrames command frames

/-- Every newly emitted command accepts any saved stack.
Consumer: observer and administrative queue transport. -/
def AddsFree (before after : List NCmd) : Prop := ∀ command ∈ after, command ∈ before ∨ Free command

theorem AddsFree.refl (commands : List NCmd) : AddsFree commands commands :=
  fun _ member => Or.inl member

theorem AddsFree.trans {a b c : List NCmd} (first : AddsFree a b) (last : AddsFree b c) : AddsFree a c := by
  intro command member
  rcases last command member with prior | free
  · exact first command prior
  · exact Or.inr free

theorem AddsFree.append (before left right : List NCmd) (a : AddsFree before left) (b : AddsFree before right) :
    AddsFree before (left ++ right) := by
  intro command member
  rcases List.mem_append.mp member with first | last
  · exact a command first
  · exact b command last

/-- Free emitted commands can be appended to a retained pending queue.
Consumer: the non-evaluator command census below. -/
theorem assemble {m : NativeMachine} {before after : List NCmd}
    (held : QueueStable m before) (added : AddsFree before after) : QueueStable m after := by
  intro command member owner owns fiber found
  rcases added command member with old | free
  · exact held command old owner owns fiber found
  · exact free fiber.frame.stack

/-- Nested interrupts add only evaluate commands.
Consumer: countdown observer command census. -/
theorem interrupt_each (interp : Moves.NInterp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (targets : List FiberId) (m : NativeMachine) (commands : List NCmd) :
    AddsFree commands (interruptEach interp who extra targets (m, commands)).2 := by
  induction targets generalizing m commands with
  | nil => exact .refl commands
  | cons target rest ih =>
    simp only [interruptEach, List.foldl_cons]
    split
    · exact ih m commands
    · apply AddsFree.trans (last := ih _ _)
      split
      · intro command member
        rcases List.mem_append.mp member with old | new
        · exact Or.inl old
        · rw [List.mem_singleton.mp new]
          exact Or.inr (fun _ => trivial)
      · simpa only [List.append_nil] using AddsFree.refl commands

/-- Countdown observers add only interrupt evaluations and one optional resume.
Consumer: fire_observer below. -/
theorem countdown_observer (interp : Moves.NInterp) (m : NativeMachine) (id : FiberId) (exit : ExitV)
    (commands : List NCmd) (waiter : FiberId) (token : Nat) :
    AddsFree commands (fireObserver interp id exit (m, commands) (.countdown waiter token)).2 := by
  simp only [fireObserver]
  split
  · exact .refl commands
  · split
    · exact .refl commands
    · rename_i fiber found pending present
      let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
      let firstFailure := pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess
      generalize result : (if firstFailure then
          interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining (base, [])
          else (base, [])) = out
      have nested : AddsFree [] out.2 := by
        rw [← result]
        split
        · exact interrupt_each interp waiter _ pending.remaining base []
        · exact .refl []
      obtain ⟨nextMachine, nextCommands⟩ := out
      dsimp only at nested ⊢
      split
      · apply AddsFree.append
        · apply AddsFree.append commands commands nextCommands (.refl commands)
          intro command member
          rcases nested command member with impossible | free
          · cases impossible
          · exact Or.inr free
        · intro command member
          rw [List.mem_singleton.mp member]
          exact Or.inr (fun _ => trivial)
      · apply AddsFree.append commands commands nextCommands (.refl commands)
        intro command member
        rcases nested command member with impossible | free
        · cases impossible
        · exact Or.inr free

/-- An observer's emitted commands place no new saved-stack constraint.
Consumer: observe command pending-stack closure. -/
theorem fire_observer (interp : Moves.NInterp) (m : NativeMachine) (id : FiberId) (exit : ExitV)
    (commands : List NCmd) (observer : Observer) :
    AddsFree commands (fireObserver interp id exit (m, commands) observer).2 := by
  cases observer with
  | countdown waiter token => exact countdown_observer interp m id exit commands waiter token
  | resumeAwait =>
    intro command member
    rcases List.mem_append.mp member with old | new
    · exact Or.inl old
    · rw [List.mem_singleton.mp new]; exact Or.inr (fun _ => trivial)
  | untrackChild => exact .refl commands
  | callback => exact .refl commands
  | dropScopeFinalizer => simp only [fireObserver]; split <;> exact .refl commands
  | raceCallback =>
    simp only [fireObserver]
    repeat' split
    all_goals aesop (add norm simp [AddsFree, Free, CommandFrames, List.mem_append, List.mem_cons, List.not_mem_nil])

/-- Draining owed resumes adds only token-matched resume commands.
Consumer: the drainDue command census. -/
theorem drain_owed (m : NativeMachine) (owed : List (Owed NCode)) : AddsFree [] (drainOwed m owed).2 := by
  induction owed generalizing m with
  | nil => exact .refl []
  | cons due rest ih =>
    simp only [drainOwed]
    split
    · intro command member
      rcases List.mem_cons.mp member with new | old
      · rw [new]; exact Or.inr (fun _ => trivial)
      · exact ih m command old
    · exact ih _

/-- Exit publication emits only evaluations, observer commands and drains.
Consumer: the actual finish command's emitted prefix. -/
theorem exit_fiber (interp : Moves.NInterp) (m : NativeMachine) (fiber : Control.Fiber) (exit : ExitV) :
    AddsFree [] (exitFiber interp m fiber exit).2 := by
  unfold exitFiber
  split
  · intro command member
    rw [List.mem_singleton.mp member]; exact Or.inr (fun _ => trivial)
  · unfold exitFiber.exitStore
    dsimp only
    split
    · intro command member
      rw [List.mem_singleton.mp member]; exact Or.inr (fun _ => trivial)
    · intro command member
      rcases List.mem_append.mp member with observed | after
      · obtain ⟨observer, _, same⟩ := List.mem_map.mp observed
        rw [← same]; exact Or.inr (fun _ => trivial)
      · rcases List.mem_cons.mp after with done | later
        · rw [done]; exact Or.inr (fun _ => trivial)
        · rw [List.mem_singleton.mp later]; exact Or.inr (fun _ => trivial)

/-- The non-evaluator commands introduce only free stack constraints, except the existing race-cancel owner.
Consumer: full administrative queue closure below. -/
theorem emitted (root : NativeEff) (table : RowTable) (m : NativeMachine) (command : NCmd)
    (rest : List NCmd) (notLoop : ∀ id yielding, command ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, command ≠ .deliver id yielding)
    (notCancel : ∀ race id yielding remaining visited, command ≠ .raceCancel race id yielding remaining visited) :
    letI := evaluatorFor root table
    AddsFree rest (driveStep (interpOf root table) m command rest).2 := by
  letI := evaluatorFor root table
  cases command with
  | loop id yielding => exact False.elim (notLoop id yielding rfl)
  | deliver id yielding => exact False.elim (notDeliver id yielding rfl)
  | raceCancel race id yielding remaining visited => exact False.elim (notCancel race id yielding remaining visited rfl)
  | evaluate | resume | launch | registrationDone | interruptTarget | afterInterrupt | trackChild | exitDone | closeParAwait | wake =>
    simp only [driveStep]
    repeat' split
    all_goals aesop (add norm simp [AddsFree, Free, CommandFrames, settle,
      List.mem_append, List.mem_cons, List.not_mem_nil])
  | enrollRace race child =>
    simp only [driveStep]
    split
    · rename_i entry fiber raceFound fiberFound
      split
      · rename_i exit exited
        have added := fire_observer (interpOf root table)
          (m.updateRace {entry with state := {entry.state with live := entry.state.live ++ [child]}})
          child exit [] (.raceCallback race)
        apply AddsFree.append
        · intro command member
          rcases added command member with impossible | free
          · cases impossible
          · exact Or.inr free
        · exact .refl rest
      · exact .refl rest
    · exact .refl rest
  | observe id exit observer =>
    apply AddsFree.append
    · intro command member
      rcases fire_observer (interpOf root table) m id exit [] observer command member with impossible | free
      · cases impossible
      · exact Or.inr free
    · exact .refl rest
  | link mode scope target who extra =>
    apply AddsFree.append
    · intro command member
      have simple := ReturnCommands.allSimple_linkScope (interpOf root table) m mode scope target who extra command member
      cases command <;> cases simple <;> exact Or.inr (fun _ => trivial)
    · exact .refl rest
  | finish id exit =>
    simp only [driveStep]
    split
    · exact .refl rest
    · apply AddsFree.append
      · intro command member
        rcases exit_fiber (interpOf root table) m _ exit command member with impossible | free
        · cases impossible
        · exact Or.inr free
      · exact .refl rest
  | drainDue =>
    apply AddsFree.append
    · intro command member
      rcases drain_owed _ _ command member with impossible | free
      · cases impossible
      · exact Or.inr free
    · exact .refl rest

/-- A race-free table trivially preserves each previous race owner.
Consumer: pending-owner stack transport at every administrative command. -/
theorem race_hosts (m n : NativeMachine) (empty : m.races = []) : RaceHostsPreserved m n := by
  intro id race found
  simp only [RunMachine.race?, empty, List.find?_nil] at found
  cases found

theorem away_owner {m n : NativeMachine} {owner target : FiberId}
    (same : owner = target) (held : StackLinksAway owner m n) : StackLinksAway target m n := same ▸ held

theorem away_fibers {m n o : NativeMachine} {owner : FiberId}
    (held : StackLinksAway owner m n) (same : o.fibers = n.fibers) : StackLinksAway owner m o := by
  intro id fiber different found
  obtain ⟨next, seen, stack⟩ := held id fiber different found
  exact ⟨next, by simpa only [RunMachine.fiber?, same] using seen, stack⟩

/-- An exit changes only its selected owner's stack.
Consumer: finish command tail transport. -/
theorem exit_away (interp : Moves.NInterp) (m : NativeMachine) (fiber : Control.Fiber) (exit : ExitV) :
    StackLinksAway fiber.id m (exitFiber interp m {fiber with running := false} exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    let next : Control.Fiber := {fiber with
      finalizing := some exit
      running := false
      frame := {fiber.frame with
        deferredInterrupt := false
        current := .onSuccess (interp.interruptAllCode fiber.children) (interp.restoreName exit)}}
    exact away_fibers (update_away m next) rfl
  · unfold exitFiber.exitStore
    dsimp only
    let next := ({fiber with running := false}.publish exit)
    let emitted := (m.update next).emit [.exited next.id exit]
    have first : StackLinksAway fiber.id m emitted := away_fibers (update_away m next) rfl
    split
    · exact first.trans (update_away emitted (next.cleared interp))
    · exact first

/-- A command without an active owner retains every pending owner's saved stack.
Consumer: the administrative command census below. -/
theorem unowned_tail (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : NCmd) (rest : List NCmd) (guard : GuardQueue root table m (command :: rest))
    (held : QueueStable m (command :: rest)) (empty : m.races = [])
    (unowned : commandOwner m command = none) (notExit : ∀ id, command ≠ .exitDone id) :
    letI := evaluatorFor root table
    QueueStable (driveStep (interpOf root table) m command rest).1 rest := by
  letI := evaluatorFor root table
  exact queue_transport root table (guardQueue_tail root table guard) (queue_tail held)
    (race_hosts m _ empty) (unowned_command_links root table m command rest unowned notExit)

/-- Administrative overwrites change only their owner; clearing changes only an exited row.
Consumer: complete administrative QueueStable assembly. -/
theorem tail (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : NCmd) (rest : List NCmd) (state : GuardState m)
    (guard : GuardQueue root table m (command :: rest)) (held : QueueStable m (command :: rest))
    (empty : m.races = []) (notLoop : ∀ id yielding, command ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, command ≠ .deliver id yielding) :
    letI := evaluatorFor root table
    QueueStable (driveStep (interpOf root table) m command rest).1 rest := by
  letI := evaluatorFor root table
  have authority := guard.authority command (List.mem_cons_self ..)
  cases command with
  | loop id yielding => exact False.elim (notLoop id yielding rfl)
  | deliver id yielding => exact False.elim (notDeliver id yielding rfl)
  | evaluate | resume | launch | enrollRace | interruptTarget | trackChild | observe | link | drainDue | wake =>
    apply unowned_tail root table m _ rest guard held empty rfl
    intro id wrong; cases wrong
  | registrationDone race yielding =>
    exact unowned_tail root table m _ rest guard held empty
      (by simp only [commandOwner, RunMachine.race?, empty, List.find?_nil, Option.map_none])
      (by intro id wrong; cases wrong)
  | afterInterrupt id yielding kind =>
    obtain ⟨fiber, found, _, _⟩ := authority
    simp only [driveStep, found]
    apply queue_tail_transport root table (.afterInterrupt id yielding kind) rest guard (queue_tail held) id rfl
    · exact race_hosts m _ empty
    · simp only [settle]
      apply away_owner (fiber_id_of_lookup found)
      exact update_away m {fiber with frame := {fiber.frame with
        current := asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)}}
  | closeParAwait id yielding targets =>
    obtain ⟨fiber, found, _, _⟩ := authority
    simp only [driveStep, found]
    apply queue_tail_transport root table (.closeParAwait id yielding targets) rest guard (queue_tail held) id rfl
    · exact race_hosts m _ empty
    · simp only [settle]
      apply away_owner (fiber_id_of_lookup found)
      exact update_away m {fiber with frame := {fiber.frame with
        stack := .iterator ((interpOf root table).closeDoneName) ((interpOf root table).voidValue) :: fiber.frame.stack
        current := (interpOf root table).parkCode (.awaitAll targets)}}
  | finish id exit =>
    obtain ⟨fiber, found, _, _⟩ := authority
    simp only [driveStep, found]
    apply queue_tail_transport root table (.finish id exit) rest guard (queue_tail held) id rfl
    · exact race_hosts m _ empty
    · exact away_owner (fiber_id_of_lookup found) (exit_away (interpOf root table) m fiber exit)
  | exitDone id =>
    obtain ⟨fiber, found, exited⟩ := authority
    simp only [driveStep, found]
    exact queue_cleared root table m state rest (guardQueue_tail root table guard) (queue_tail held) fiber
      (by simpa only [fiber_id_of_lookup found] using found) exited
  | raceCancel race id yielding remaining visited =>
    simp only [driveStep]
    split
    · exact queue_tail held
    · have noRace : m.race? race = none := by simp only [RunMachine.race?, empty, List.find?_nil]
      simp only [noRace]
      exact queue_tail held

/-- Every administrative command retains the actual pending-owner stack condition.
Consumer: full command closure and the original admitted Workers history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem non_evaluator (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : NCmd) (rest : List NCmd) (state : GuardState m)
    (guard : GuardQueue root table m (command :: rest)) (held : QueueStable m (command :: rest))
    (empty : m.races = []) (notLoop : ∀ id yielding, command ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, command ≠ .deliver id yielding) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m command rest
    QueueStable out.1 out.2 := by
  letI := evaluatorFor root table
  have kept := tail root table m command rest state guard held empty notLoop notDeliver
  cases command with
  | raceCancel race id yielding remaining visited =>
    have selected := held (.raceCancel race id yielding remaining visited) (List.mem_cons_self ..) id rfl
    have next : QueueStable m [.afterInterrupt id yielding (.awaitAll visited)] := by
      intro command member owner owns fiber found
      rw [List.mem_singleton.mp member] at owns ⊢
      have same := Option.some.inj owns
      subst owner
      exact selected fiber found
    dsimp only
    simp only [driveStep]
    split
    · exact queue_append next (queue_tail held)
    · have noRace : m.race? race = none := by simp only [RunMachine.race?, empty, List.find?_nil]
      simp only [noRace]
      exact queue_append next (queue_tail held)
  | evaluate | loop | deliver | resume | launch | enrollRace | registrationDone | interruptTarget
    | afterInterrupt | trackChild | observe | exitDone | closeParAwait | link | finish | drainDue | wake =>
    apply assemble kept
    apply emitted root table m _ rest notLoop notDeliver
    intro race id yielding remaining visited same
    cases same

end Effect4.Program.ReleaseCustody.AdministrativeQueue
