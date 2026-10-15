import Test.Dogfood.Scenario.Atomic.StageDisposition

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: Atomic's native joint postcondition for shop_stages.
Actual emitted interruption waits retain their receiving suffix at the selected world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Actual native interruption waits retain their small owner and its receiving frame. -/
theorem native_after_permission (built : Api.Built) (_accepted : Api.Author.build (shop .none) = .ok built)
    (before after : StageWorld.World) (future : Future before after)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (heap : HeapAt before machine.state) (metadata : RowAt before fiber)
    (role : StageRoles.FrameAt built.program built.table before fiber.id fiber.frame)
    (cut : NativeCut built.program built.table after (evaluateNative built.program machine fiber yielding built.table))
    (waitYield : Bool) (kind : ParkKind)
    (member : .afterInterrupt fiber.id waitYield kind ∈
      (evaluateNative built.program machine fiber yielding built.table).nested) :
    fiber.id.value < 2 ∧ AfterPermission built.program built.table after
      ((evaluateNative built.program machine fiber yielding built.table).machine.update
        (evaluateNative built.program machine fiber yielding built.table).fiber) fiber.id kind := by
  have fields := Moves.evaluateNative_footprint built.program built.table machine fiber yielding
  cases role with
  | root identity owned =>
    refine ⟨by rw [identity]; decide, ?_⟩
    intro row inside same
    have actual := installed_actor _ _ row inside (same.trans fields.id.symm)
    cases actual
    constructor
    · intro rootId
      exact cut.rootAfter (fields.id.trans identity) fiber.id waitYield kind member
    · intro daemonId
      have impossible : (0 : Nat) = 1 := congrArg FiberId.value (identity.symm.trans daemonId)
      cases impossible
  | daemon identity owned =>
    refine ⟨by rw [identity]; decide, ?_⟩
    intro row inside same
    have actual := installed_actor _ _ row inside (same.trans fields.id.symm)
    cases actual
    constructor
    · intro rootId
      have impossible : (1 : Nat) = 0 := congrArg FiberId.value (identity.symm.trans rootId)
      cases impossible
    · intro daemonId
      exact DaemonGraph.frame_future built.program built.table before after future _
        (DaemonGraph.native_frame built.program built.table before machine fiber yielding owned heap).2
  | request owner requested identity owned =>
    have recorded := metadata.recorded owner requested identity
    rw [StageGraph.native_primitive_eq built.program built.table owner before machine fiber yielding owned recorded] at member
    obtain ⟨input, code, saved⟩ := owned
    have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits before input _ code
    have quiet := Moves.evaluatePrim_quiet (interpAt built.program machine.completedExits built.table)
      machine fiber yielding ordinary.1 ordinary.2.1
    have impossible := quiet.2 _ member
    cases impossible

/-- The actual native word supplies all emitted command certificates at the same chosen world. -/
theorem native_nested_queue (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (before after : StageWorld.World) (future : Future before after) (fresh : Fresh before)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (heap : HeapAt before machine.state) (counter : machine.nextId = before.nextId)
    (metadata : RowAt before fiber)
    (role : StageRoles.FrameAt built.program built.table before fiber.id fiber.frame)
    (cut : NativeCut built.program built.table after (evaluateNative built.program machine fiber yielding built.table)) :
    QueueAt built.program built.table after
      ((evaluateNative built.program machine fiber yielding built.table).machine.update
        (evaluateNative built.program machine fiber yielding built.table).fiber)
      (evaluateNative built.program machine fiber yielding built.table).nested := by
  have words := native_words built accepted before fresh machine fiber yielding role metadata heap counter
  intro command member
  cases words.commands command member with
  | drain => exact .drain
  | evaluate child => exact .evaluate child
  | track child allowed => exact .track fiber.id child (of_decide_eq_true allowed)
  | interrupt target who extra => exact .interrupt target who extra
  | after waitYield kind noRace =>
    have receiving := native_after_permission built accepted before after future machine fiber yielding
      heap metadata role cut waitYield kind member
    exact .afterInterrupt fiber.id waitYield kind receiving.1 noRace receiving.2

end Test.Dogfood.Scenario.Atomic.StageConfiguration
