import Test.Dogfood.Scenario.Atomic.StageReplies
import Test.Dogfood.Scenario.Atomic.StageTasks

/-!
Concept: reactive-scheduling R11.
Consumer: Atomic's actual native settled task assertion and source-entry handoff.
The existing dispatcher producer carries old matching admissions and actual new static tasks together.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program

/-- Stored tasks owe reply permission only when their actual parked token matches. -/
def AdmittedTasks (machine : NativeMachine) : Prop :=
  ∀ fiber ∈ machine.fibers, DispatcherPredicate.All (TaskPermission machine) fiber.dispatcher

/-- Actor installation retains admitted dispatchers through the same actual reply transport. -/
theorem AdmittedTasks.update (machine : NativeMachine) (actor : SourceScope.SourceFiber)
    (held : AdmittedTasks machine) (owned : DispatcherPredicate.All (TaskPermission machine) actor.dispatcher)
    (reply : ∀ id token code, ReplyPermission machine id token code →
      ReplyPermission (machine.update actor) id token code) : AdmittedTasks (machine.update actor) := by
  intro row member bucket inside task present
  obtain ⟨old, oldIn, same⟩ := List.mem_map.mp member
  have typed : DispatcherPredicate.All (TaskPermission machine) row.dispatcher := by
    rw [← same]
    change DispatcherPredicate.All (TaskPermission machine) (if old.id = actor.id then actor else old).dispatcher
    split
    · exact owned
    · exact held old oldIn
  exact (typed bucket inside task present).transport machine (machine.update actor) task reply

/-- An actual addressed interruption retains stored tasks and their matching-token admission. -/
theorem AdmittedTasks.interruption (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (member : fiber ∈ machine.fibers) (cause : CauseV) (held : AdmittedTasks machine) :
    AdmittedTasks (machine.update (interruptWithCause cause fiber).1) := by
  apply held.update machine (interruptWithCause cause fiber).1
  · rw [interruption_dispatcher fiber cause]
    exact held fiber member
  · intro id token code reply
    exact reply.interruption machine fiber member cause id token code

/-- The common pending dispatcher profile seeds matching-root admission at actual entry. -/
theorem AdmittedTasks.of_pending (machine : NativeMachine)
    (roots : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩)
    (pending : AnswerSlots.AllocationAdapter.ReplyRows machine) : AdmittedTasks machine := by
  intro fiber member bucket inside task present
  have reply := pending fiber member bucket inside task present
  cases task with
  | start id => exact .start id
  | resume id token code =>
    exact .resume id token code (ReplyPermission.root_only machine roots id token code reply.1 reply.2)
  | wake list phase => exact False.elim reply

/-- The source guard bounds every actual stored resume token. -/
theorem stored_task_below (machine : NativeMachine) (guard : Guard.GuardState machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers)
    (bucket : Guard.NBucket) (inside : bucket ∈ fiber.dispatcher.buckets)
    (id : FiberId) (token : Nat) (code : NCode) (present : .resume id token code ∈ bucket.tasks) :
    token < machine.nextToken := by
  apply guard.keysBelow (id, token)
  apply Guard.internalKeys_fiber member
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨bucket, inside,
    List.mem_flatMap.mpr ⟨.resume id token code, present, List.mem_singleton_self _⟩⟩

/-- One actual native result retains matching admission for every stored task after installation. -/
theorem native_admitted_tasks (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (source : SourceScope.FrameAt built.program fiber.frame)
    (guard : Guard.GuardState machine) (member : fiber ∈ machine.fibers)
    (active : fiber.parked = .notParked) (held : AdmittedTasks machine) :
    let result := evaluateNative built.program machine fiber yielding built.table
    AdmittedTasks (result.machine.update result.fiber) := by
  let P : Guard.NTask → Prop := fun task => TaskAt task ∨
    (TaskPermission machine task ∧ ∀ key ∈ Guard.taskKeys task, key.2 < machine.nextToken)
  have old : ∀ row ∈ machine.fibers, DispatcherPredicate.All P row.dispatcher := by
    intro row inside bucket bucketIn task taskIn
    refine .inr ⟨held row inside bucket bucketIn task taskIn, ?_⟩
    intro key keyIn
    cases task with
    | start id => cases keyIn
    | wake list phase => cases keyIn
    | resume id token code =>
      have same := List.mem_singleton.mp keyIn
      subst key
      exact stored_task_below machine guard row inside bucket bucketIn id token code taskIn
  have kept := native_tasks_on built accepted fragment world machine fiber yielding role metadata source P
    (fun id token => .inl (.resume id token (.success .unit) .unit))
    (fun id => .inl (.start id)) old (old fiber member)
  have fresh := Guard.ReturnFields.evaluateNative_freshPark built.program built.table machine fiber yielding active
  have others := Moves.evaluateNative_interferes built.program built.table machine fiber yielding
  dsimp only [AdmittedTasks]
  intro row inside bucket bucketIn task taskIn
  obtain ⟨prior, priorIn, same⟩ := List.mem_map.mp inside
  have typed : DispatcherPredicate.All P row.dispatcher := by
    rw [← same]
    change DispatcherPredicate.All P (if prior.id = (evaluateNative built.program machine fiber yielding built.table).fiber.id then (evaluateNative built.program machine fiber yielding built.table).fiber else prior).dispatcher
    split
    · exact kept.2
    · exact kept.1 prior priorIn
  rcases typed bucket bucketIn task taskIn with static | ⟨admitted, bound⟩
  · exact static.permission
  · cases admitted with
    | start id => exact .start id
    | resume id token code reply =>
      exact .resume id token code (reply.native_install fresh others id token code
        (bound (id, token) (List.mem_singleton_self _)))

end Test.Dogfood.Scenario.Atomic.StageConfiguration
