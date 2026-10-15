import Test.Dogfood.Scenario.Atomic.StageStoreFields
import Effect4.Laws.Program.NativeExecutor
import Effect4.Laws.Program.SourceOpportunityPrimitive

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: Atomic's actual joint command settlement producer.
One chosen world retains the native heap, stored rows, returned actor and completion exit.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- A real native result supplies one complete local installation and its own completion-command permission. -/
structure NativeCut (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Moves.NIteration) : Prop where
  installation : LocalConfiguration root table world result.fiber.id result.machine
  actor : RowAt world result.fiber
  role : OutcomeRole root table world result
  completed : ∀ exit, result.outcome = .finished exit → CompletedAt world result.fiber.id exit

/-- The three checked actor producers join the actual native state at one shared next world. -/
theorem native_cut (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (raceFree : SourceScope.RaceFreeSource built.program)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : Configuration built.program built.table world machine)
    (lookup : machine.fiber? fiber.id = some fiber) (running : fiber.running = true)
    (source : SourceScope.ConfigurationAt built.program machine) (actorSource : SourceScope.FiberAt built.program fiber)
    (guard : Guard.GuardState machine)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame) :
    ∃ next, Future world next ∧ NativeCut built.program built.table next
      (evaluateNative built.program machine fiber yielding built.table) := by
  have member := RunMachine.mem_of_fiber? lookup
  have fields := Moves.evaluateNative_footprint built.program built.table machine fiber yielding
  have sourceNext := (SourceScope.native_at built.program fragment built.table machine fiber yielding source actorSource).machine
  have races := SourceScope.Opportunities.races_nil built.program _ raceFree sourceNext
  cases role with
  | root identity owned =>
    obtain ⟨next, future, fresh, counter, heap, actor, rows⟩ :=
      RootGraph.native_result built accepted world held.fresh machine fiber yielding owned held.heap held.counter
        Inactive (fun row present different => held.roles row present)
    have metadata : RowsAt next (evaluateNative built.program machine fiber yielding built.table).machine := by
      rw [RootGraph.native_primitive_eq built accepted world machine fiber yielding owned]
      exact RowsAt.primitive built.program fragment built.table machine.completedExits world next future
        machine fiber yielding actorSource.frame held.metadata
    refine ⟨next, future, ⟨?_, RowAt.native built.program built.table world next future machine fiber yielding
      (held.metadata fiber member), ?_, ?_⟩⟩
    · refine ⟨heap, fresh, counter, ?_, metadata, races, ?_⟩
      · intro row present different
        apply rows row present
        rw [fields.id, identity] at different
        exact different
      · exact (root_native_deferreds built accepted world held.fresh machine fiber yielding owned held.heap held.counter).trans held.noDeferreds
    · exact OutcomeRole.root built.program built.table machine.completedExits next _ (fields.id.trans identity)
        (fields.running.trans running) actor
    · intro exit finished
      rw [fields.id, identity]
      exact CompletedAt.root next exit
  | daemon identity owned =>
    have actor := DaemonGraph.native_frame built.program built.table world machine fiber yielding owned held.heap
    have metadata : RowsAt world (evaluateNative built.program machine fiber yielding built.table).machine := by
      rw [DaemonGraph.native_primitive_eq built.program built.table world machine fiber yielding owned]
      exact RowsAt.primitive built.program fragment built.table machine.completedExits world world (order.refl world)
        machine fiber yielding actorSource.frame held.metadata
    refine ⟨world, order.refl world, ⟨?_, RowAt.native built.program built.table world world (order.refl world)
      machine fiber yielding (held.metadata fiber member), ?_, ?_⟩⟩
    · refine ⟨actor.1, held.fresh, (DaemonGraph.native_counter built.program built.table world machine fiber yielding owned).trans held.counter,
        ?_, metadata, races, ?_⟩
      · intro row present different
        exact DaemonGraph.native_rows built.program built.table world machine fiber yielding owned
          (RoleAt built.program built.table world) held.roles row present
      · exact (daemon_native_deferreds built.program built.table world machine fiber yielding owned).trans held.noDeferreds
    · exact OutcomeRole.daemon built.program built.table world _ (fields.id.trans identity)
        (fields.running.trans running) actor.2
    · intro exit finished
      rw [fields.id, identity]
      exact CompletedAt.daemon world exit
  | request owner requested identity owned =>
    have recorded := (held.metadata fiber member).recorded owner requested identity
    have consistent : Guard.DeferredCause.DeferredCause fiber.frame :=
      guard.deferredCause fiber member
    obtain ⟨next, future, change, heap, actor⟩ :=
      StageGraph.native_result built.program built.table owner requested world machine fiber yielding owned held.heap recorded consistent
    have counter : (evaluateNative built.program machine fiber yielding built.table).machine.nextId = next.nextId := by
      rw [StageGraph.native_counter built.program built.table owner world machine fiber yielding owned recorded, change.1]
      exact held.counter
    have allocated : owner + 1 < world.nextId := by
      have bound := guard.fibersBelow fiber member
      rw [identity, held.counter] at bound
      exact bound
    have metadata : RowsAt next (evaluateNative built.program machine fiber yielding built.table).machine := by
      rw [StageGraph.native_primitive_eq built.program built.table owner world machine fiber yielding owned recorded]
      exact RowsAt.primitive built.program fragment built.table machine.completedExits world next future
        machine fiber yielding actorSource.frame held.metadata
    have oldRows : (evaluateNative built.program machine fiber yielding built.table).machine.fibers = machine.fibers :=
      (StageGraph.native_rows built.program built.table owner world machine fiber yielding owned recorded
        (fun _ => True) (fun _ _ => True.intro) (fun _ _ _ _ => True.intro)).1
    refine ⟨next, future, ⟨?_, RowAt.native built.program built.table world next future machine fiber yielding
      (held.metadata fiber member), ?_, ?_⟩⟩
    · refine ⟨heap, fresh_request world next owner held.fresh change allocated, counter, ?_, metadata, races, ?_⟩
      · intro row present different
        rw [oldRows] at present
        apply RoleAt.request_other built.program built.table world next owner future change row
        · rw [fields.id, identity] at different
          exact different
        · exact held.roles row present
      · exact (request_native_deferreds built.program built.table world owner machine fiber yielding owned recorded).trans held.noDeferreds
    · exact OutcomeRole.request built.program built.table machine.completedExits next owner requested _
        (fields.id.trans identity) (fields.running.trans running) actor
    · intro exit finished
      rw [fields.id, identity]
      apply CompletedAt.request built.program built.table machine.completedExits next owner exit
      simpa only [External.Native.ResultAt, finished] using actor

end Test.Dogfood.Scenario.Atomic.StageConfiguration
