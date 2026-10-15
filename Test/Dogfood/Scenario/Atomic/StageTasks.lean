import Test.Dogfood.Scenario.Atomic.StageNativeJoin

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: Atomic's active joint machine and detached-task postconditions.
The shared action and primitive producers retain actual scheduler starts and void replies.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Every stored dispatcher retains this source's actual scheduler reply profile. -/
def TaskRows (machine : NativeMachine) : Prop :=
  ∀ fiber ∈ machine.fibers, DispatcherPredicate.All TaskAt fiber.dispatcher

/-- A real newborn dispatcher has no pending task. -/
theorem task_birth (id : FiberId) (program : NCode) (flag : Bool) (budget : Nat × Bool) (context : Ctx) :
    DispatcherPredicate.All TaskAt (RunFiber.make id program flag budget context).dispatcher := by
  intro bucket member
  cases member

/-- Installing the actual actor preserves other dispatchers and its certified task list. -/
theorem TaskRows.update (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : TaskRows machine) (actor : DispatcherPredicate.All TaskAt fiber.dispatcher) :
    TaskRows (machine.update fiber) := by
  intro row member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  change DispatcherPredicate.All TaskAt (if old.id = fiber.id then fiber else old).dispatcher
  split
  · exact actor
  · exact held old present

/-- The actual source roles all use the shared primitive dispatcher after their checked native reduction. -/
theorem role_primitive_eq (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) :
    evaluateNative built.program machine fiber yielding built.table =
      evaluatePrim (interpAt built.program machine.completedExits built.table) machine fiber yielding := by
  cases role with
  | root identity owned => exact RootGraph.native_primitive_eq built accepted world machine fiber yielding owned
  | daemon identity owned => exact DaemonGraph.native_primitive_eq built.program built.table world machine fiber yielding owned
  | request owner member identity owned =>
    exact StageGraph.native_primitive_eq built.program built.table owner world machine fiber yielding owned
      (metadata.recorded owner member identity)

/-- Actual native evaluation retains all stored task profiles and the returned actor's profile together. -/
theorem native_tasks_on (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (source : SourceScope.FrameAt built.program fiber.frame)
    (P : Guard.NTask → Prop)
    (voidReply : ∀ id token, P (.resume id token (.success .unit)))
    (startTask : ∀ id, P (.start id))
    (held : ∀ row ∈ machine.fibers, DispatcherPredicate.All P row.dispatcher)
    (actor : DispatcherPredicate.All P fiber.dispatcher) :
    (∀ row ∈ (evaluateNative built.program machine fiber yielding built.table).machine.fibers,
      DispatcherPredicate.All P row.dispatcher) ∧
      DispatcherPredicate.All P (evaluateNative built.program machine fiber yielding built.table).fiber.dispatcher := by
  rw [role_primitive_eq built accepted world machine fiber yielding role metadata]
  apply Moves.evaluatePrim_dispatcher_on (interpAt built.program machine.completedExits built.table) machine fiber yielding
    (fun rows => ∀ row ∈ rows, DispatcherPredicate.All P row.dispatcher) P
    voidReply held actor
  intro thunk action current unparked found
  have owned : SourceScope.ThunkAt built.program thunk := by
    have code := source.1
    rw [current] at code
    exact code
  have programs := SourceScope.interp_action_at built.program fragment machine.completedExits built.table thunk action owned found
  exact SourceScope.with_fiber_rows_dispatcher built.program machine.completedExits built.table (fun _ => True)
    (fun row => DispatcherPredicate.All P row.dispatcher) P machine fiber yielding action held
    (SourceScope.ActionProgramsAt.mono built.program (P := fun _ => SourceScope.CodeAt built.program) (Q := fun _ _ => True) action programs (fun _ _ _ => True.intro))
    (fun _ _ _ _ _ _ bucket member => (List.not_mem_nil member).elim) actor startTask


/-- The original static task profile is the fixed instance of the supplied task assertion. -/
theorem native_tasks (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (source : SourceScope.FrameAt built.program fiber.frame)
    (held : TaskRows machine) (actor : DispatcherPredicate.All TaskAt fiber.dispatcher) :
    TaskRows (evaluateNative built.program machine fiber yielding built.table).machine ∧
      DispatcherPredicate.All TaskAt (evaluateNative built.program machine fiber yielding built.table).fiber.dispatcher :=
  native_tasks_on built accepted fragment world machine fiber yielding role metadata source TaskAt
    (fun id token => .resume id token (.success .unit) .unit) TaskAt.start held actor

end Test.Dogfood.Scenario.Atomic.StageConfiguration
