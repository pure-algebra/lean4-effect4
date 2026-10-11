import Effect4.Laws.Program.StackRegion
import Effect4.Laws.Machine.EditObserverWords

/-!
Concept: scope-lifetime-finalization, R11, the saved-mask region bracket.
Question: actual command transport supplies compiled_region_bracket's entry-stack premise.
Reach: the watched live identity, actual detached evaluation boundary tests, and guarded exit clearing.
Limit: no unconditional claim crosses a detached exit; no progress or outside-runtime agreement follows.
Consumer: the command-prefix region lift and then the existing region bracket.
-/
set_option autoImplicit false
namespace Effect4.Program.StackRegion
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

/-- A changed current code or metadata retains a known saved suffix. -/
theorem fiber_fields {below : List NCode} {first last : NFiber} (held : Inside below first)
    (stack : last.frame.stack = first.frame.stack) : Inside below last := by
  obtain ⟨above, shape⟩ := held
  exact ⟨above, stack.trans shape⟩

/-- Pushing one administrative frame places it above the same entry stack. -/
theorem push_inside {below : List NCode} {fiber : NFiber} (held : Inside below fiber) (code : NCode) :
    Inside below {fiber with frame := {fiber.frame with stack := code :: fiber.frame.stack}} := by
  obtain ⟨above, shape⟩ := held
  exact ⟨code :: above, congrArg (code :: ·) shape⟩

/-- Replacing a looked-up row transfers its region condition through the supplied local edit. -/
theorem update_from {id : FiberId} {below : List NCode} {machine : NativeMachine}
    (first last : NFiber) (member : first ∈ machine.fibers) (held : Held id below machine)
    (key : last.id = first.id) (exit : last.exit = first.exit)
    (kept : Inside below first → Inside below last) : Held id below (machine.update last) := by
  apply update last held
  intro selected live
  exact kept (held.frames first member (key.symm.trans selected) (exit.symm.trans live))

/-- Metadata edits keep the selected region independently of source code. -/
theorem modify {id : FiberId} {below : List NCode} (machine : NativeMachine)
    (target : FiberId) (edit : NFiber → NFiber) (held : Held id below machine)
    (key : ∀ fiber, (edit fiber).id = fiber.id)
    (exit : ∀ fiber, (edit fiber).exit = fiber.exit)
    (stack : ∀ fiber, (edit fiber).frame.stack = fiber.frame.stack) :
    Held id below (machine.modify target edit) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    exact update_from fiber (edit fiber) (List.mem_of_find?_eq_some found) held
      (key fiber) (exit fiber) (fun inside => fiber_fields inside (stack fiber))

/-- An actual recorded interrupt does not pop the watched entry stack. -/
theorem interrupt {id : FiberId} {below : List NCode} (interp : NInterp)
    (machine : NativeMachine) (fiber : NFiber) (member : fiber ∈ machine.fibers)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (held : Held id below machine) :
    Held id below (machine.update (interruptRecord interp who extra fiber).1) :=
  update_from fiber _ member held (OtherEdit.id (.interrupted interp fiber who extra))
    (OtherEdit.exit (.interrupted interp fiber who extra))
    (fun inside => fiber_fields inside (other_edit_stack (.interrupted interp fiber who extra)))

/-- Nested observer interrupts retain the region before their evaluation commands execute. -/
theorem interrupt_each {id : FiberId} {below : List NCode} (interp : NInterp) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (machine : NativeMachine)
    (commands : List NCommand) (held : Held id below machine) :
    Held id below (interruptEach interp who extra targets (machine, commands)).1 := by
  induction targets generalizing machine commands with
  | nil => exact held
  | cons target rest ih =>
    simp only [interruptEach, List.foldl_cons]
    split
    · exact ih machine commands held
    · rename_i fiber found
      apply ih
      exact fields (interrupt interp machine fiber (List.mem_of_find?_eq_some found) (some who) extra held)
        rfl (Nat.le_refl _)

/-- Posting a task changes no saved frame of its dispatcher owner. -/
theorem post_task {id : FiberId} {below : List NCode} (machine : NativeMachine)
    (owner : FiberId) (priority : Nat) (task : Task EffName EffThunk Val Err Defect FiberId Ann) (held : Held id below machine) :
    Held id below (machine.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact held
  · rename_i fiber found
    exact update_from fiber _ (List.mem_of_find?_eq_some found) held rfl rfl (fun inside => inside)

/-- Owed resumes only post tasks before their actual resume commands execute. -/
theorem drain_owed {id : FiberId} {below : List NCode} (machine : NativeMachine)
    (owed : List (Owed NCode)) (held : Held id below machine) :
    Held id below (drainOwed machine owed).1 := by
  induction owed generalizing machine with
  | nil => exact held
  | cons next rest ih =>
    simp only [drainOwed]
    split
    · exact ih machine held
    · exact ih _ (post_task machine _ _ _ held)

/-- Actual observer updates retain saved stacks, including a waiter snapshot after nested interrupts. -/
theorem observer {id : FiberId} {below : List NCode} (interp : NInterp)
    (machine : NativeMachine) (owner : FiberId) (exit : ExitV) (commands : List NCommand)
    (held : Held id below machine) (callback : Observer) :
    Held id below (fireObserver interp owner exit (machine, commands) callback).1 := by
  rw [Edits.observer_word]
  simp only [Edits.observerWord, Edits.run_append, Edits.run_cons, Edits.run_nil, Edit.apply]
  have fired : Held id below (machine.emit [.observerFired owner callback]) :=
    fields held rfl (Nat.le_refl _)
  generalize machine.emit [.observerFired owner callback] = current at fired ⊢
  cases callback with
  | resumeAwait waiter token resumeWith => exact fired
  | untrackChild parent =>
    simp only [Edits.observerTailWord]
    split
    · exact fired
    · rename_i fiber found
      simp only [Edits.run_cons, Edits.run_nil, Edit.apply]
      exact update_from fiber _ (List.mem_of_find?_eq_some found) fired rfl rfl
        (fun inside => inside)
  | dropScopeFinalizer scope key =>
    simp only [Edits.observerTailWord]
    split <;> exact fired
  | countdown waiter token =>
    simp only [Edits.observerTailWord]
    split
    · exact fired
    · rename_i fiber found
      split
      · exact fired
      · rename_i pending pendingFound
        rw [Edits.run_append, Edits.interrupt_choice_word]
        have interrupted : Held id below
            (if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
              interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining (current, [])
            else (current, [])).1 := by
          split
          · exact interrupt_each interp _ _ _ _ _ fired
          · exact fired
        generalize (if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
            interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining (current, [])
          else (current, [])) = changed at interrupted ⊢
        split
        · exact interrupted
        · rename_i latest latestFound
          split
          · exact interrupted
          · split
            · simp only [Edits.run_cons, Edits.run_nil, Edit.apply]
              exact update_from latest _ (List.mem_of_find?_eq_some latestFound) interrupted
                rfl rfl (fun inside => inside)
            · simp only [Edits.run_cons, Edits.run_nil, Edit.apply]
              exact modify _ _ _
                (update_from latest _ (List.mem_of_find?_eq_some latestFound) interrupted
                  rfl rfl (fun inside => inside))
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | raceCallback raceId =>
    simp only [Edits.observerTailWord]
    split
    · exact fired
    · simp only [Edits.run_append, Edits.run_cons, Edits.run_nil, Edit.apply]
      split <;> exact fired
  | callback key => exact fired

/-- Exit publication removes the live obligation before clearing the stack. -/
theorem finish {id : FiberId} {below : List NCode} (interp : NInterp)
    (machine : NativeMachine) (fiber : NFiber) (member : fiber ∈ machine.fibers)
    (exit : ExitV) (held : Held id below machine) :
    Held id below (exitFiber interp machine {fiber with running := false} exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    exact update_from fiber _ member held rfl rfl (fun inside => inside)
  · unfold exitFiber.exitStore
    dsimp only
    have published := update ({fiber with running := false}.publish exit) held
      (fun _ live => by cases live)
    split
    · exact update _ published (fun _ live => by cases live)
    · exact published

/-- Only loop and delivery can reach the detached region boundary in one command.
The premise is tested on the actual selected row; it states no resulting stack shape. -/
def Continues (root : NativeEff) (table : RowTable) (interp : NInterp)
    (id : FiberId) (below : List NCode) (machine : NativeMachine) : NCommand → Prop
  | .loop owner yielding => ∀ fiber, machine.fiber? owner = some fiber →
      fiber.id = id → fiber.exit = none → GoesOn
        (iteration (evaluator := evaluatorFor root table) interp machine (detach below fiber) yielding)
  | .deliver owner yielding => ∀ fiber, machine.fiber? owner = some fiber →
      fiber.id = id → fiber.exit = none →
      GoesOn (evaluateNative root machine (detach below fiber) yielding table)
  | _ => True

/-- Every actual command keeps the entry suffix before the detached evaluation exits.
The clear premise is supplied by the existing compiled command authority. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem command (root : NativeEff) (table : RowTable) (interp : NInterp)
    (machine : NativeMachine) (head : NCommand) (rest : List NCommand)
    (id : FiberId) (below : List NCode) (held : Held id below machine)
    (going : Continues root table interp id below machine head)
    (clear : ∀ target, head = .exitDone target → ∀ fiber,
      machine.fiber? target = some fiber → fiber.exit ≠ none) :
    Held id below (driveStep (evaluator := evaluatorFor root table) interp machine head rest).1 := by
  cases head with
  | loop owner yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact loop_held root table interp machine fiber (List.mem_of_find?_eq_some found)
        owner yielding rest id below held (going fiber found)
  | deliver owner yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact deliver_held root table machine fiber (List.mem_of_find?_eq_some found)
        owner yielding rest id below held (going fiber found)
  | evaluate owner =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · exact held
      · exact update_from fiber _ (List.mem_of_find?_eq_some found) held rfl rfl (fun inside => inside)
  | finish owner exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact finish interp machine fiber (List.mem_of_find?_eq_some found) exit held
  | resume owner token answer =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · split
        · exact update_from fiber _ (List.mem_of_find?_eq_some found) held rfl rfl (fun inside => inside)
        · exact held
      · exact held
  | launch raceId =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split
        · exact held
        · split
          · exact held
          · exact fields (interferes (Interferes.launchEntrant interp raceId machine _ _ []) held) rfl (Nat.le_refl _)
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · split
      · apply observer interp
        exact held
      · exact modify _ _ _ held (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    · exact held
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · rename_i fiber found
        split
        · exact settle_held _ rest _ held (held.frames fiber (List.mem_of_find?_eq_some found))
        · apply settle_held _ rest _ held
          intro selected live
          exact push_inside (held.frames fiber (List.mem_of_find?_eq_some found) selected live) _
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact interrupt interp machine fiber (List.mem_of_find?_eq_some found) who extra held
  | afterInterrupt owner yielding kind =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact settle_held _ rest _ held (held.frames fiber (List.mem_of_find?_eq_some found))
  | raceCancel raceId owner yielding remaining visited =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split <;> exact held
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · exact modify _ _ _ (modify _ _ _ held (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | observe owner exit callback =>
    simp only [driveStep]
    exact observer interp machine owner exit [] held callback
  | exitDone owner =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact update _ held (fun _ live => False.elim (clear owner rfl fiber found live))
  | closeParAwait owner yielding fibers =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      apply settle_held _ rest _ held
      intro selected live
      exact push_inside (held.frames fiber (List.mem_of_find?_eq_some found) selected live) _
  | link mode scope target interruptor extra =>
    simp only [driveStep]
    exact interferes (Interferes.linkScope _ _ _ _ _ _ _) held
  | drainDue =>
    simp only [driveStep]
    exact drain_owed _ _ held
  | wake list phase => exact held

end Effect4.Program.StackRegion
