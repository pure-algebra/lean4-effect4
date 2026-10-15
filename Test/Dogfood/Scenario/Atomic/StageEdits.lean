import Test.Dogfood.Scenario.Atomic.StageConfiguration

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the actual Atomic contextual message and outside-interruption producers.
Each edit retains the actual target's source role and recorded interruption evidence.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Actual interruption leaves the scheduler and publication fields of its target unchanged. -/
theorem interruption_fields_with_stack (fiber : SourceScope.SourceFiber) (cause : CauseV) :
    let next := (interruptWithCause cause fiber).1
    next.id = fiber.id ∧ next.exit = fiber.exit ∧ next.running = fiber.running ∧
      next.children = fiber.children ∧ next.observers = fiber.observers ∧ next.frame.stack = fiber.frame.stack ∧ next.dispatcher = fiber.dispatcher := by
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The original metadata interface projects the same actual interruption witness. -/
theorem interruption_fields (fiber : SourceScope.SourceFiber) (cause : CauseV) :
    let next := (interruptWithCause cause fiber).1
    next.id = fiber.id ∧ next.exit = fiber.exit ∧ next.running = fiber.running ∧
      next.children = fiber.children ∧ next.observers = fiber.observers := by
  have fields := interruption_fields_with_stack fiber cause
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

/-- Actual interruption records a cause without changing its saved continuation. -/
theorem interruption_stack (fiber : SourceScope.SourceFiber) (cause : CauseV) :
    (interruptWithCause cause fiber).1.frame.stack = fiber.frame.stack :=
  (interruption_fields_with_stack fiber cause).2.2.2.2.2.1

/-- Actual interruption retains already queued dispatcher tasks. -/
theorem interruption_dispatcher (fiber : SourceScope.SourceFiber) (cause : CauseV) :
    (interruptWithCause cause fiber).1.dispatcher = fiber.dispatcher :=
  (interruption_fields_with_stack fiber cause).2.2.2.2.2.2

/-- Admitted interruption preserves the actual target's metadata and its published request exit. -/
theorem RowAt.interruption (world : StageWorld.World) (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : RowAt world fiber) (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail)
    (marked : MarkedCause cause) : RowAt world (interruptWithCause cause fiber).1 := by
  obtain ⟨identity, exit, running, children, observers⟩ := interruption_fields fiber cause
  constructor
  · intro owner member same
    rw [identity] at same
    exact StageGraph.interruption_recorded fiber cause (held.recorded owner member same) untyped marked
  · intro owner member same
    rw [identity] at same
    rw [exit]
    exact held.published owner member same
  · intro different
    rw [identity] at different
    exact children.trans (held.childless different)
  · rw [observers]
    exact held.observers

/-- Admitted interruption retains an actual live source-role certificate. -/
theorem live_interruption (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (active : StageRoles.FrameAt root table world fiber.id fiber.frame)
    (recorded : ∀ owner ∈ requests, fiber.id = ⟨owner + 1⟩ → StageGraph.Recorded fiber.frame)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    StageRoles.FrameAt root table world (interruptWithCause cause fiber).1.id (interruptWithCause cause fiber).1.frame := by
  have identity := (interruption_fields fiber cause).1
  rw [identity]
  exact StageRoles.interruption_frame_with root table world fiber cause active recorded untyped marked

/-- Admitted interruption preserves live roles and actual dormant scheduler rows together. -/
theorem RoleAt.interruption (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV) (held : RoleAt root table world fiber)
    (recorded : ∀ owner ∈ requests, fiber.id = ⟨owner + 1⟩ → StageGraph.Recorded fiber.frame)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    RoleAt root table world (interruptWithCause cause fiber).1 := by
  obtain ⟨identity, exit, running, children, observers⟩ := interruption_fields fiber cause
  rcases held with active | inactive
  · exact Or.inl (live_interruption root table world fiber cause active recorded untyped marked)
  · apply Or.inr
    change _ ∨ _
    rw [exit, running]
    exact inactive

/-- Installing an admitted observer retains the target's recorded causes and publication evidence. -/
theorem RowAt.observe (world : StageWorld.World) (fiber : SourceScope.SourceFiber)
    (observer : Observer) (held : RowAt world fiber) (allowed : ObserverAt observer) :
    RowAt world {fiber with observers := fiber.observers ++ [observer]} := by
  refine ⟨held.recorded, held.published, held.childless, ?_⟩
  intro seen member
  rcases List.mem_append.mp member with old | added
  · exact held.observers seen old
  · cases List.mem_singleton.mp added
    exact allowed

/-- Dropping a park token only removes observers from the admitted observer list. -/
theorem RowAt.filter_observers (world : StageWorld.World) (fiber : SourceScope.SourceFiber)
    (keep : Observer → Bool) (held : RowAt world fiber) :
    RowAt world {fiber with observers := fiber.observers.filter keep} := by
  exact ⟨held.recorded, held.published, held.childless,
    fun observer member => held.observers observer (List.mem_filter.mp member).1⟩

/-- Actual write-back retains every other source row and the exact machine heap. -/
theorem Configuration.update (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : Configuration root table world machine) (role : RoleAt root table world fiber)
    (metadata : RowAt world fiber) : Configuration root table world (machine.update fiber) := by
  refine ⟨held.heap, held.fresh, held.counter, ?_, RowsAt.update world machine fiber held.metadata metadata,
    held.noRaces, held.noDeferreds⟩
  intro row member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  change RoleAt root table world (if old.id = fiber.id then fiber else old)
  split
  · exact role
  · exact held.roles old present

/-- Actual observer admission preserves the complete active machine assertion. -/
theorem Configuration.observe (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (target : FiberId) (observer : Observer)
    (held : Configuration root table world machine) (allowed : ObserverAt observer) :
    Configuration root table world (machine.observe target observer) := by
  unfold RunMachine.observe RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    have member := RunMachine.mem_of_fiber? found
    exact Configuration.update root table world machine _ held (held.roles fiber member)
      (RowAt.observe world fiber observer (held.metadata fiber member) allowed)

/-- Actual token cleanup removes observers and changes no source frame or heap field. -/
theorem Configuration.drop (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (token : Nat) (held : Configuration root table world machine) :
    Configuration root table world (machine.dropToken token) := by
  refine ⟨held.heap, held.fresh, held.counter, ?_, ?_, held.noRaces, held.noDeferreds⟩
  · intro row member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact held.roles old present
  · intro row member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact RowAt.filter_observers world old _ (held.metadata old present)

/-- Actual admitted interruption retains the complete machine assertion at the same world. -/
theorem Configuration.interruption (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (present : fiber ∈ machine.fibers)
    (cause : CauseV) (held : Configuration root table world machine)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    Configuration root table world (machine.update (interruptWithCause cause fiber).1) :=
  Configuration.update root table world machine _ held
    (RoleAt.interruption root table world fiber cause (held.roles fiber present)
      (held.metadata fiber present).recorded untyped marked)
    (RowAt.interruption world fiber cause (held.metadata fiber present) untyped marked)

end Test.Dogfood.Scenario.Atomic.StageConfiguration
