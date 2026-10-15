import Test.Dogfood.Scenario.Atomic.RootReturn

/-!
Concept: store-typing R4.
Consumer: the Atomic actual root fork transition and coupled stage history.
The actual fork answer, counter and new child's source role share the allocated world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- The actual fork keeps the heap and installs its exact allocated handle in the parent frame. -/
theorem fork_fields (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    let result := evaluatePrim.withFiber (interpAt root view table) machine fiber yielding (.fork program options site)
    result.machine.state = machine.state ∧ result.machine.nextId = machine.nextId + 1 ∧
      result.fiber.frame = {fiber.frame with current := .success (.fiber ⟨machine.nextId⟩)} ∧
      result.machine.fibers = machine.fibers ++ [RunFiber.make ⟨machine.nextId⟩ program
        (match options.maskMode with | .interruptible => true | .uninterruptible => false | .inherit => fiber.frame.interruptible)
        ((interpAt root view table).budgetOf fiber.context) fiber.context] := by
  cases options with
  | mk immediate daemon mode => cases daemon <;> cases immediate <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The root's real fork answer retains its exact binder and saved older source suffix. -/
theorem fork_parent (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (point : Point) (owner : Nat) (small : owner < 7) (held : PointAt root world point)
    (binder : point.env.length = StageSource.forkBinder owner) (counter : machine.nextId = world.nextId)
    (saved : Effect4.Contracts.Path (Edge root table world) (.rootAnswer point.env.length) .ordinary fiber.frame.stack)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    let result := evaluatePrim.withFiber (interpAt root view table) machine fiber yielding (.fork program options site)
    result.machine.nextId = (allocate world).nextId ∧
      FrameAt root table (allocate world) result.fiber.frame := by
  have fields := fork_fields root table view machine fiber yielding program options site
  have allocated : world.nextId = owner + 1 := by
    rw [held.2.2.2.2, binder]
    exact (RootBindings.fork_rank owner small).1
  refine ⟨?_, ?_⟩
  · rw [fields.2.1, counter]
    rfl
  · rw [fields.2.2.1]
    refine ⟨.rootAnswer point.env.length, .success ?_, ?_⟩
    · rw [counter, allocated]
      exact fork_answer root world point owner small held binder
    · exact saved.map (edge_future root table world (allocate world) (allocate_future world))
/-- The newly allocated child receives the actual daemon or request role at its source fork. -/
theorem fork_child (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (point : Point) (owner : Nat) (small : owner < 7)
    (held : PointAt built.program world point) (binder : point.env.length = StageSource.forkBinder owner)
    (body rest : NativeEff) (options : Supervision.ForkOptions)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.bind (.withFiber (.fork body options)) rest)))
    (flag : Bool) (budget : Nat × Bool) (context : Ctx) :
    StageRoles.FrameAt built.program built.table (allocate world) ⟨owner + 1⟩
      (RunFiber.make ⟨owner + 1⟩ (resolve built.program (((point.child 0).child 0).child 0)) flag budget context : SourceScope.SourceFiber).frame := by
  by_cases daemon : owner = 0
  · subst owner
    apply StageRoles.FrameAt.daemon rfl
    exact ⟨DaemonGraph.root_child built accepted world point held binder, .nil ()⟩
  · have member : owner ∈ requests := by
      simp only [requests, List.mem_cons, List.not_mem_nil, or_false]
      omega
    apply StageRoles.FrameAt.request owner member rfl
    exact ⟨StageWorld.Kind.finalized owner, request_child built accepted world fresh point owner member body rest options held binder found,
      .nil (StageWorld.Kind.finalized owner)⟩

/-- Actual fork installation retypes every older nonroot row and gives the new child its declared role. -/
theorem fork_rows (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (fresh : Fresh world)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (point : Point) (owner : Nat) (small : owner < 7) (held : PointAt built.program world point)
    (binder : point.env.length = StageSource.forkBinder owner) (counter : machine.nextId = world.nextId)
    (body rest : NativeEff) (options : Supervision.ForkOptions)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.bind (.withFiber (.fork body options)) rest)))
    (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluatePrim.withFiber (interpAt built.program view built.table) machine fiber yielding
      (.fork (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path)
    ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table (allocate world) row.id row.frame ∨ Other row := by
  have fields := fork_fields built.program built.table view machine fiber yielding
    (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path
  have allocated : world.nextId = owner + 1 := by
    rw [held.2.2.2.2, binder]
    exact (RootBindings.fork_rank owner small).1
  dsimp only
  intro row member different
  rw [fields.2.2.2] at member
  rcases List.mem_append.mp member with old | added
  · rcases rows row old different with active | retired
    · exact .inl (StageRoles.allocate_other built.program built.table world row.id row.frame different active)
    · exact .inr retired
  · have same := List.mem_singleton.mp added
    subst row
    rw [counter, allocated]
    exact .inl (fork_child built accepted world fresh point owner small held binder body rest options found _ _ _)

end Test.Dogfood.Scenario.Atomic.RootGraph
