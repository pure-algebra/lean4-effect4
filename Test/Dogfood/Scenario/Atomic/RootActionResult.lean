import Test.Dogfood.Scenario.Atomic.RootNativeShape
import Test.Dogfood.Scenario.Atomic.NativeEffects
import Test.Dogfood.Scenario.Atomic.RootAfter

/-!
Concept: store-typing R4.
Consumer: the actual root actor transition in `Atomic.Store.shop_stages`.
Source action evaluation joins its parent, allocated child and untouched rows at one world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- The actual source root action joins heap, parent and all nonroot rows at one next world. -/
theorem source_action_result (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (fresh : Fresh world)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (point : Point) (held : PointAt built.program world point) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId)
    (saved : Effect4.Contracts.Path (Edge built.program built.table world)
      (.rootAnswer point.env.length) .ordinary fiber.frame.stack)
    (action : NAction) (found : actionAt built.program (point.child 0) = some action)
    (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluatePrim.withFiber (interpAt built.program view built.table) machine fiber yielding action
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧ FrameAt built.program built.table next result.fiber.frame ∧
      (∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row) ∧
      result.machine.state = machine.state ∧ NativeEffects.ActionAt true fiber result ∧
      AfterResult built.program built.table next result := by
  rcases action_shape built accepted world point held action found with fork | interrupted
  · obtain ⟨owner, body, options, rest, small, binder, source, rfl⟩ := fork
    have parent := fork_parent built.program built.table view world machine fiber yielding point owner small held
      binder counter saved (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path
    have fields := fork_fields built.program built.table view machine fiber yielding
      (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path
    refine ⟨allocate world, allocate_future world, fresh_allocate world fresh, parent.1, ?_, parent.2, ?_, fields.1, NativeEffects.fork _ _ _ _ _ _ _, ?_⟩
    · rw [fields.1]
      exact allocate_heap world machine.state heap
    · exact fork_rows built accepted view world fresh machine fiber yielding point owner small held binder counter
        body rest options source Other rows
    · intro host afterYielding kind member
      exact False.elim ((NativeEffects.fork_with_no_after (interpAt built.program view built.table) machine fiber yielding
        (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path).2 host afterYielding kind member)
  · obtain ⟨binder, rfl⟩ := interrupted
    exact ⟨world, order.refl world, fresh, counter, heap,
      ⟨.rootAnswer point.env.length, interrupt_code built.program built.table view world point held binder ⟨1⟩ fiber.id,
        saved⟩, rows, rfl, NativeEffects.quiet true fiber _ rfl rfl rfl (fun impossible => by cases impossible),
      fun _ _ _ member => nomatch member⟩

/-- Every actual root native action joins the actor and stored nonroot rows at its chosen world. -/
theorem action_result (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (fresh : Fresh world)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input : StageWorld.Kind) (thunk : EffThunk) (action : NAction)
    (code : CodeAt built.program built.table world input (.withFiber thunk))
    (current : fiber.frame.current = .withFiber thunk)
    (heap : HeapAt world machine.state) (counter : machine.nextId = world.nextId)
    (saved : Effect4.Contracts.Path (Edge built.program built.table world) input .ordinary fiber.frame.stack)
    (found : (interpAt built.program view built.table).withFiberOf thunk = some action)
    (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluatePrim.withFiber (interpAt built.program view built.table) machine fiber yielding action
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧ FrameAt built.program built.table next result.fiber.frame ∧
      (∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row) ∧
      result.machine.state = machine.state ∧ NativeEffects.ActionAt true fiber result ∧
      AfterResult built.program built.table next result := by
  have prior : FrameAt built.program built.table world fiber.frame := ⟨input, current.symm ▸ code, saved⟩
  generalize equal : Prim.withFiber thunk = program at code
  cases code with
  | ignored owned =>
    have admin := DaemonGraph.action_shape built.program built.table thunk (equal.symm ▸ owned)
    rcases admin with ⟨targets, who, rfl⟩ | ⟨token, rfl⟩
    · change some (.interruptAll targets who) = some action at found
      cases found
      refine ⟨world, order.refl world, fresh, counter, heap, prior, rows, rfl,
        NativeEffects.interrupt_all true _ _ _ _ _ _, ?_⟩
      intro host yielding kind member
      rcases List.mem_append.mp member with target | after
      · obtain ⟨target, present, same⟩ := List.mem_map.mp target
        cases same
      · cases List.mem_singleton.mp after
        exact .ordinary (fun _ impossible => by cases impossible) saved
    · change some (.dropObservers token) = some action at found
      cases found
      exact ⟨world, order.refl world, fresh, counter, heap,
        ⟨.ordinary, .success True.intro, saved⟩, rows, rfl, NativeEffects.drop true _ _ _ _ token,
        fun _ _ _ member => nomatch member⟩
  | action owned =>
    cases equal
    change actionAt built.program _ = some action at found
    exact source_action_result built accepted view world fresh machine fiber yielding _ owned heap counter saved action found Other rows
  | @interrupting _ binder target who captured ignored =>
    cases equal
    change some (.interruptAs _ _) = some action at found
    cases found
    have effects : NativeEffects.ActionAt true fiber
        (evaluatePrim.withFiber (interpAt built.program view built.table) machine fiber yielding (.interruptAs target who)) :=
      NativeEffects.interrupt_as true (interpAt built.program view built.table) machine fiber yielding target who
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split
    · rename_i missing
      simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, missing] at effects
      exact ⟨world, order.refl world, fresh, counter, heap, prior, rows, rfl, effects,
        fun _ _ _ member => nomatch member⟩
    · rename_i other present
      simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, present] at effects
      refine ⟨world, order.refl world, fresh, counter, heap, prior, rows, rfl, effects, ?_⟩
      intro host yielding kind member
      cases List.mem_singleton.mp member
      exact .binder binder target rfl captured ignored saved
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, next, form⟩ | form
    all_goals rw [form] at equal
    all_goals cases equal
  | success good => cases equal
  | failure => cases equal
  | frontier zero => cases equal
  | await captured ignored => cases equal
  | sleep captured ignored => cases equal
  | readReply cell owned values => cases equal
  | read => cases equal
  | join target mode captured => cases equal
  | awaitAll targets captured => cases equal
  | pause => cases equal
  | pausing owned next => cases equal
  | bound owned first callback => cases equal

end Test.Dogfood.Scenario.Atomic.RootGraph
