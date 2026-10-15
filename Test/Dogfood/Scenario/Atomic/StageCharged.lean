import Test.Dogfood.Scenario.Atomic.StageWaits
import Effect4.Laws.Program.NativeCommands

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: Atomic's actual loop command and coupled stage history.
Charging and forced yield use the same native join as direct delivery.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Charging retains the actor's actual request recording and row metadata. -/
theorem RowAt.charged (world : StageWorld.World) (fiber : SourceScope.SourceFiber) (held : RowAt world fiber) :
    RowAt world (countOp (runloopTop fiber)) := by
  unfold countOp runloopTop
  split
  all_goals exact ⟨held.recorded, held.published, held.childless, held.observers⟩

/-- The charged actor retains the source role's actual interruption authority. -/
theorem role_charged (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (typed : StageRoles.FrameAt root table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    StageRoles.FrameAt root table world (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).frame := by
  have identity : (countOp (runloopTop fiber)).id = fiber.id := Guard.Interruption.runloopTop_id fiber
  rw [identity]
  cases typed with
  | root identity owned => exact .root identity (RootGraph.loop_top root table world fiber owned)
  | daemon identity owned => exact .daemon identity (DaemonGraph.loop_top root table world fiber owned)
  | request owner member identity owned =>
    exact .request owner member identity
      (StageGraph.loop_top root table owner world fiber owned (metadata.recorded owner member identity) consistent)

/-- A real scheduler wrapper retains its deferred code under each actor's own answer class. -/
theorem role_injected (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (typed : StageRoles.FrameAt root table world fiber.id fiber.frame) :
    StageRoles.FrameAt root table world fiber.id
      { fiber.frame with current := .onSuccessConst (.yieldNowWith 0) fiber.frame.current } := by
  cases typed with
  | root identity owned => exact .root identity (RootGraph.injected_frame root table world fiber.frame owned)
  | daemon identity owned => exact .daemon identity ⟨.constant (.pause 0) owned.1, owned.2⟩
  | request owner member identity owned =>
    exact .request owner member identity (StageGraph.injected_frame root table owner world fiber.frame owned)

/-- Trace emission retains the active machine assertion without changing its chosen world. -/
theorem Configuration.emit (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (held : Configuration root table world machine) : Configuration root table world (machine.emit events) :=
  ⟨held.heap, held.fresh, held.counter, held.roles, held.metadata, held.noRaces, held.noDeferreds⟩

/-- The actual charged loop and optional yield wrapper share the existing native-cut producer. -/
theorem iteration_cut (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (raceFree : SourceScope.RaceFreeSource built.program)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : Configuration built.program built.table world machine)
    (lookup : machine.fiber? fiber.id = some fiber) (running : fiber.running = true)
    (source : SourceScope.ConfigurationAt built.program machine) (actorSource : SourceScope.FiberAt built.program fiber)
    (guard : Guard.GuardState machine)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame) :
    letI := evaluatorFor built.program built.table
    ∃ next, Future world next ∧ NativeCut built.program built.table next
      (iteration (interpOf built.program built.table) machine fiber yielding) := by
  letI := evaluatorFor built.program built.table
  have member := RunMachine.mem_of_fiber? lookup
  have metadata := held.metadata fiber member
  have consistent := guard.deferredCause fiber member
  have top := role_charged built.program built.table world fiber role metadata consistent
  have topMetadata := metadata.charged world fiber
  have topSource := SourceScope.count_at built.program _ (SourceScope.loop_top_at built.program fiber actorSource)
  have topConsistent := Guard.DeferredCause.runloopTop_deferredCause fiber consistent
  have topRunning : (countOp (runloopTop fiber)).running = true :=
    (Guard.ReturnFields.runloopTop_running fiber).trans running
  have topBelow : (countOp (runloopTop fiber)).id.value < machine.nextId := by
    change (runloopTop fiber).id.value < machine.nextId
    rw [Guard.Interruption.runloopTop_id]
    exact guard.fibersBelow fiber member
  unfold iteration
  dsimp only
  split
  · rename_i result injected
    have retained := SourceScope.yield_at built.program machine _ yielding result source topSource injected
    unfold injectYield at injected
    split at injected
    · cases injected
      apply native_cut_fields built accepted fragment raceFree world
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true (held.emit built.program built.table world machine _) _ topBelow topRunning retained.machine retained.fiber topConsistent
      · exact role_injected built.program built.table world _ top
      · exact ⟨topMetadata.recorded, topMetadata.published, topMetadata.childless, topMetadata.observers⟩
    · cases injected
  · exact native_cut_fields built accepted fragment raceFree world machine _ yielding held topMetadata topBelow
      topRunning source topSource topConsistent top

end Test.Dogfood.Scenario.Atomic.StageConfiguration
