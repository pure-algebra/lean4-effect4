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
theorem native_cut_owned (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (raceFree : SourceScope.RaceFreeSource built.program)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : Configuration built.program built.table world machine)
    (actorMetadata : RowAt world fiber) (below : fiber.id.value < machine.nextId) (running : fiber.running = true)
    (source : SourceScope.ConfigurationAt built.program machine) (actorSource : SourceScope.FiberAt built.program fiber)
    (consistent : Guard.DeferredCause.DeferredCause fiber.frame)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (owners : List FiberId)
    (queued : ∀ row ∈ machine.fibers, row.id ∈ owners → StageRoles.FrameAt built.program built.table world row.id row.frame) :
    ∃ next, Future world next ∧ NativeCut built.program built.table next
      (evaluateNative built.program machine fiber yielding built.table) ∧
      (∀ row ∈ (evaluateNative built.program machine fiber yielding built.table).machine.fibers,
        row.id ∈ owners → row.id ≠ (evaluateNative built.program machine fiber yielding built.table).fiber.id →
        StageRoles.FrameAt built.program built.table next row.id row.frame) := by
  have fields := Moves.evaluateNative_footprint built.program built.table machine fiber yielding
  have sourceNext := (SourceScope.native_at built.program fragment built.table machine fiber yielding source actorSource).machine
  have races := SourceScope.Opportunities.races_nil built.program _ raceFree sourceNext
  cases role with
  | root identity owned =>
    obtain ⟨next, future, fresh, counter, heap, actor, rows⟩ :=
      RootGraph.native_result built accepted world held.fresh machine fiber yielding owned held.heap held.counter
        (fun row => Inactive row ∧ row.id ∉ owners) (by
          intro row present different
          by_cases pending : row.id ∈ owners
          · exact Or.inl (queued row present pending)
          · rcases held.roles row present with live | inactive
            · exact Or.inl live
            · exact Or.inr ⟨inactive, pending⟩)
    have metadata : RowsAt next (evaluateNative built.program machine fiber yielding built.table).machine := by
      rw [RootGraph.native_primitive_eq built accepted world machine fiber yielding owned]
      exact RowsAt.primitive built.program fragment built.table machine.completedExits world next future
        machine fiber yielding actorSource.frame held.metadata
    refine ⟨next, future, ⟨?_, RowAt.native built.program built.table world next future machine fiber yielding
      actorMetadata, ?_, ?_⟩, ?_⟩
    · refine ⟨heap, fresh, counter, ?_, metadata, races, ?_⟩
      · intro row present different
        have other : row.id ≠ ⟨0⟩ := by rw [fields.id, identity] at different; exact different
        rcases rows row present other with live | inactive
        · exact Or.inl live
        · exact Or.inr inactive.1
      · exact (root_native_deferreds built accepted world held.fresh machine fiber yielding owned held.heap held.counter).trans held.noDeferreds
    · exact OutcomeRole.root built.program built.table machine.completedExits next _ (fields.id.trans identity)
        (fields.running.trans running) actor
    · intro exit finished
      rw [fields.id, identity]
      exact CompletedAt.root next exit
    · intro row present pending different
      have other : row.id ≠ ⟨0⟩ := by rw [fields.id, identity] at different; exact different
      rcases rows row present other with live | inactive
      · exact live
      · exact False.elim (inactive.2 pending)
  | daemon identity owned =>
    have actor := DaemonGraph.native_frame built.program built.table world machine fiber yielding owned held.heap
    have metadata : RowsAt world (evaluateNative built.program machine fiber yielding built.table).machine := by
      rw [DaemonGraph.native_primitive_eq built.program built.table world machine fiber yielding owned]
      exact RowsAt.primitive built.program fragment built.table machine.completedExits world world (order.refl world)
        machine fiber yielding actorSource.frame held.metadata
    refine ⟨world, order.refl world, ⟨?_, RowAt.native built.program built.table world world (order.refl world)
      machine fiber yielding actorMetadata, ?_, ?_⟩, ?_⟩
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
    · intro row present pending different
      exact DaemonGraph.native_rows built.program built.table world machine fiber yielding owned
        (fun old => old.id ∈ owners → StageRoles.FrameAt built.program built.table world old.id old.frame)
        queued row present pending
  | request owner requested identity owned =>
    have recorded := actorMetadata.recorded owner requested identity
    obtain ⟨next, future, change, heap, actor⟩ :=
      StageGraph.native_result built.program built.table owner requested world machine fiber yielding owned held.heap recorded consistent
    have counter : (evaluateNative built.program machine fiber yielding built.table).machine.nextId = next.nextId := by
      rw [StageGraph.native_counter built.program built.table owner world machine fiber yielding owned recorded, change.1]
      exact held.counter
    have allocated : owner + 1 < world.nextId := by
      have bound := below
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
      actorMetadata, ?_, ?_⟩, ?_⟩
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
    · intro row present pending different
      rw [oldRows] at present
      apply StageRoles.request_other built.program built.table world next owner future change row.id row.frame
      · rw [fields.id, identity] at different
        exact different
      · exact queued row present pending

/-- Contextual actor fields instantiate the same joined producer without pending owner obligations. -/
theorem native_cut_fields (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (raceFree : SourceScope.RaceFreeSource built.program)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : Configuration built.program built.table world machine)
    (actorMetadata : RowAt world fiber) (below : fiber.id.value < machine.nextId) (running : fiber.running = true)
    (source : SourceScope.ConfigurationAt built.program machine) (actorSource : SourceScope.FiberAt built.program fiber)
    (consistent : Guard.DeferredCause.DeferredCause fiber.frame)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame) :
    ∃ next, Future world next ∧ NativeCut built.program built.table next
      (evaluateNative built.program machine fiber yielding built.table) := by
  obtain ⟨next, future, cut, pending⟩ := native_cut_owned built accepted fragment raceFree world machine fiber yielding held
    actorMetadata below running source actorSource consistent role [] (fun _ _ absent => nomatch absent)
  exact ⟨next, future, cut⟩

/-- The stored actor supplies the contextual metadata required by the common native join. -/
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
  exact native_cut_fields built accepted fragment raceFree world machine fiber yielding held
    (held.metadata fiber member) (guard.fibersBelow fiber member) running source actorSource
    (guard.deferredCause fiber member) role

end Test.Dogfood.Scenario.Atomic.StageConfiguration
