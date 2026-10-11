import Effect4.Laws.Program.ReleaseCustody.LoopCommand
import Effect4.Laws.Program.ReleaseCustody.CommandFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: administrative frame closure serves Execution.history and Workers.releases_step.
Reach: actual native command edits, source-owned terminal replies and queued overwrite stacks.
Limit: this frame assertion establishes neither funding nor store allocation nor progress alone.
Unlock: the command induction joins these frames with the existing scalar census and Guard ownership.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.AdministrativeKept
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.Sequencing Effect4.Program.ReleaseCustody.CommandStacks

/-- Edits outside the stored fiber list retain the frame assertion.
Consumer: native administrative command closure. -/
theorem same_fibers {m n : NativeMachine} (held : ConfigurationKept m) (same : n.fibers = m.fibers) :
    ConfigurationKept n := fun f member => held f (same ▸ member)

/-- A keyed metadata edit retains the old row's sequencing.
Consumer: dispatcher and observer edits below. -/
theorem modify (m : NativeMachine) (id : FiberId) (edit : Control.Fiber → Control.Fiber)
    (held : ConfigurationKept m) (current : ∀ f, (edit f).frame.current = f.frame.current)
    (stack : ∀ f, (edit f).frame.stack = f.frame.stack) (park : ∀ f, (edit f).parked = f.parked) :
    ConfigurationKept (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i f found
    exact CommandSequencing.configuration_update m (edit f) held
      (CommandSequencing.fiber_fields f (edit f) (held f (List.mem_of_find?_eq_some found))
        (current f) (stack f) (park f))

/-- An interrupt retains the saved registration sequence.
Consumer: interruptEach and the interrupt command. -/
theorem interrupt (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (found : m.fiber? fiber.id = some fiber)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (held : ConfigurationKept m) :
    ConfigurationKept (m.update (interruptRecord (interpOf root table) who extra fiber).1) :=
  CommandSequencing.configuration_update m _ held
    (NativeMachineShape.edit (.interrupted (interpOf root table) fiber who extra)
      (held fiber (List.mem_of_find?_eq_some found)))

/-- Nested interrupts retain every stored row's frame assertion.
Consumer: countdown observers and link edits. -/
theorem interrupt_each (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (m : NativeMachine) (commands : List NCmd)
    (held : ConfigurationKept m) :
    ConfigurationKept (interruptEach (interpOf root table) who extra targets (m, commands)).1 := by
  induction targets generalizing m commands with
  | nil => exact held
  | cons target rest ih =>
    simp only [interruptEach, List.foldl_cons]
    split
    · exact ih m commands held
    · rename_i fiber found
      apply ih
      exact same_fibers (interrupt root table m fiber
        (by simpa only [fiber_id_of_lookup found] using found) (some who) extra held) rfl

/-- Posting a dispatcher task changes no current or saved frame.
Consumer: drain_owed and due-resume commands. -/
theorem post_task (m : NativeMachine) (owner : FiberId) (priority : Nat) (task : NTask)
    (held : ConfigurationKept m) : ConfigurationKept (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact same_fibers held rfl
  · rename_i fiber found
    exact same_fibers
      (CommandSequencing.configuration_update m {fiber with dispatcher := fiber.dispatcher.enqueue priority task} held
        (CommandSequencing.fiber_fields fiber _ (held fiber (List.mem_of_find?_eq_some found)) rfl rfl rfl)) rfl

/-- Draining owed resumes only posts tasks before their commands execute.
Consumer: administrative drain closure. -/
theorem drain_owed (m : NativeMachine) (due : List (Owed NCode)) (held : ConfigurationKept m) :
    ConfigurationKept (drainOwed m due).1 := by
  induction due generalizing m with
  | nil => exact held
  | cons owed rest ih =>
    cases mode : owed.mode with
    | now => simpa only [drainOwed, mode] using ih m held
    | scheduled owner priority =>
      simpa only [drainOwed, mode] using ih _ (post_task m owner priority (.resume owed.waiter owed.token owed.code) held)

/-- A stale waiter record retains its original frame after the observer's nested interrupts.
Consumer: fire_observer below. -/
theorem countdown_observer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (commands : List NCmd) (waiter : FiberId) (token : Nat)
    (held : ConfigurationKept m) :
    ConfigurationKept (fireObserver (interpOf root table) id exit (m, commands) (.countdown waiter token)).1 := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have emitted : ConfigurationKept base := held
  simp only [fireObserver, show m.emit _ = base from rfl]
  cases found : base.fiber? waiter with
  | none => exact emitted
  | some fiber =>
    have original := emitted fiber (List.mem_of_find?_eq_some found)
    simp only []
    cases pending : fiber.pending.find? (fun p => p.token = token) with
    | none => exact emitted
    | some park =>
      simp only []
      let collected := park.collected ++ [exit]
      let firstFailure := park.failFast && !exit.isSuccess && park.collected.all Exit.isSuccess
      generalize result : (if firstFailure then
          interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter)
            park.remaining (base, []) else (base, [])) = out
      have middle : ConfigurationKept out.1 := by
        rw [← result]
        split
        · exact interrupt_each root table waiter _ park.remaining base [] emitted
        · exact emitted
      obtain ⟨outMachine, nested⟩ := out
      dsimp only at middle ⊢
      cases walked : countdownWalk outMachine park.remaining collected with
      | mk exits next =>
        cases next with
        | none =>
          exact CommandSequencing.configuration_update outMachine _ middle
            (CommandSequencing.fiber_fields fiber _ original rfl rfl rfl)
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          exact CommandSequencing.configuration_update _ _
            (modify outMachine next (fun f => {f with observers := f.observers ++ [.countdown waiter token]})
              middle (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
            (CommandSequencing.fiber_fields fiber _ original rfl rfl rfl)

/-- Every actual observer retains stored frames, including the saved waiter after nested interruption.
Consumer: observe and finish command closure. -/
theorem fire_observer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (commands : List NCmd) (observer : Observer)
    (held : ConfigurationKept m) :
    ConfigurationKept (fireObserver (interpOf root table) id exit (m, commands) observer).1 := by
  cases observer with
  | countdown waiter token => exact countdown_observer root table m id exit commands waiter token held
  | resumeAwait => exact same_fibers held rfl
  | callback => exact same_fibers held rfl
  | untrackChild parent =>
    exact modify _ parent _ held (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split <;> exact same_fibers held rfl
  | raceCallback race =>
    simp only [fireObserver]
    split
    · exact same_fibers held rfl
    · split <;> exact same_fibers held rfl

/-- A clean stack accepts every administrative current code and parked status.
Consumer: finish, afterInterrupt and closeParAwait. -/
theorem clean (fiber : Control.Fiber) (held : NoAdd fiber.frame.stack) : FiberKept fiber :=
  ⟨.clean _ _ held, fun _ => .clean _ held⟩

/-- Exit publication and child interruption retain a consumed stack.
Consumer: the actual finish command. -/
theorem exit_fiber (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (exit : ExitV) (held : ConfigurationKept m)
    (empty : fiber.frame.stack = []) :
    ConfigurationKept (exitFiber (interpOf root table) m {fiber with running := false} exit).1 := by
  have missing : NoAdd fiber.frame.stack := empty ▸ noAdd_empty
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    let next : Control.Fiber := {fiber with
      finalizing := some exit
      running := false
      frame := {fiber.frame with
        deferredInterrupt := false
        current := .onSuccess ((interpOf root table).interruptAllCode fiber.children) ((interpOf root table).restoreName exit)}}
    exact same_fibers (CommandSequencing.configuration_update m next held (clean next missing)) rfl
  · unfold exitFiber.exitStore
    dsimp only
    have published := CommandSequencing.configuration_update m
      ({fiber with running := false}.publish exit) held (clean _ missing)
    split
    · exact CommandSequencing.configuration_update _ _ published (clean _ noAdd_empty)
    · exact published

/-- Every command outside evaluator entry retains saved-frame sequencing.
Consumer: the whole native command assertion and original Workers history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem non_evaluator (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : NCmd) (rest : List NCmd) (held : ConfigurationKept m)
    (queue : QueueStable m (command :: rest)) (owned : SourceScope.CommandAt root command)
    (raceFree : SourceScope.RaceFreeSource root) (races : m.races = [])
    (notLoop : ∀ id yielding, command ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, command ≠ .deliver id yielding) :
    letI := evaluatorFor root table
    ConfigurationKept (driveStep (interpOf root table) m command rest).1 := by
  letI := evaluatorFor root table
  have selected := queue command (List.mem_cons_self ..)
  have noRace (id : Nat) : m.race? id = none := by simp only [RunMachine.race?, races, List.find?_nil]
  cases command with
  | loop id yielding => exact False.elim (notLoop id yielding rfl)
  | deliver id yielding => exact False.elim (notDeliver id yielding rfl)
  | evaluate id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · exact held
      · exact same_fibers (CommandSequencing.configuration_update m {fiber with running := true, currentOpCount := 0} held
          (CommandSequencing.fiber_fields fiber _ (held fiber (List.mem_of_find?_eq_some found)) rfl rfl rfl)) rfl
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · rename_i actual parked
        split
        · rename_i matched
          have original := held fiber (List.mem_of_find?_eq_some found)
          have stable := original.parked (by rw [parked]; intro wrong; cases wrong)
          exact same_fibers (CommandSequencing.configuration_update m _ held
            ⟨ReplySequencing.terminal root raceFree answer owned.1 owned.2 _ stable,
              fun wrong => False.elim (wrong rfl)⟩) rfl
        · exact held
      · exact held
  | launch race => simp only [driveStep, noRace]; exact held
  | enrollRace race child => simp only [driveStep, noRace]; exact held
  | registrationDone race yielding => simp only [driveStep, noRace]; exact held
  | interruptTarget id who extra =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact same_fibers (interrupt root table m fiber
        (by simpa only [fiber_id_of_lookup found] using found) who extra held) rfl
  | afterInterrupt id yielding kind =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have missing : NoAdd fiber.frame.stack := selected id rfl fiber found
      exact CommandSequencing.settle_configuration fiber.id rest _ held
        ⟨clean _ missing, (by intro wrong; cases wrong), (by intro _ wrong; cases wrong)⟩
  | raceCancel race id yielding remaining visited =>
    simp only [driveStep]
    split
    · exact held
    · simp only [noRace]; exact held
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · exact modify _ child _ (modify m parent _ held (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | observe id exit observer => exact fire_observer root table m id exit [] observer held
  | exitDone id =>
    simp only [driveStep]
    split
    · exact held
    · exact CommandSequencing.configuration_update m _ held (clean _ noAdd_empty)
  | closeParAwait id yielding targets =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have missing : NoAdd fiber.frame.stack := selected id rfl fiber found
      have pushed : NoAdd (.iterator (.store .closeParDone) ((interpOf root table).voidValue) :: fiber.frame.stack) :=
        PopSequencing.noAdd_cons _ (by intro _ _ _ wrong; cases wrong) missing
      exact CommandSequencing.settle_configuration fiber.id rest _ held
        ⟨clean _ pushed, (by intro wrong; cases wrong), (by intro _ wrong; cases wrong)⟩
  | link mode scope target who extra =>
    exact NativeMachineShape.interferes (Moves.Interferes.linkScope (interpOf root table) m mode scope target who extra) held
  | finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact exit_fiber root table m fiber exit held (selected id rfl fiber found)
  | drainDue =>
    exact drain_owed _ _ (same_fibers held rfl)
  | wake => exact same_fibers held rfl

end Effect4.Program.ReleaseCustody.AdministrativeKept
