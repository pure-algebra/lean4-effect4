import Test.Dogfood.Scenario.Atomic.StageNativeWords
import Test.Dogfood.Scenario.Atomic.StageQueueUpdate
import Effect4.Laws.Machine.ContextualMessages

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: Atomic's actual native settlement at its single chosen stage world.
The existing addressed-message word retains the selected actor's live or completed permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld
abbrev MessageContext := FiberId × Outcome EffName EffThunk Val Err Defect FiberId Ann

/-- The actual selected actor retains the permission required by its existing outcome. -/
def SelectedActor (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (context : MessageContext) (fiber : SourceScope.SourceFiber) : Prop :=
  fiber.id = context.1 → match context.2 with
    | .finished _ => fiber.running = true
    | _ => StageRoles.FrameAt root table world fiber.id fiber.frame

/-- Actual addressed messages retain one complete configuration and the selected actor together. -/
def MessageState (root : NativeEff) (table : RowTable) (context : MessageContext)
    (world : StageWorld.World) (machine : NativeMachine) : Prop :=
  Configuration root table world machine ∧ ∀ fiber ∈ machine.fibers, SelectedActor root table world context fiber

/-- Immediate interrupts emit only ordinary evaluation requests. -/
def EvaluationQueue (_context : MessageContext) (_world : StageWorld.World)
    (_machine : NativeMachine) (commands : List Guard.NCmd) : Prop :=
  ∀ command ∈ commands, ∃ id, command = .evaluate id

/-- Actual observer updates preserve the selected actor's existing frame and scheduler fields. -/
theorem MessageState.observe (root : NativeEff) (table : RowTable) (context : MessageContext)
    (world : StageWorld.World) (machine : NativeMachine) (target : FiberId) (observer : Observer)
    (held : MessageState root table context world machine) (allowed : ObserverAt observer) :
    MessageState root table context world (machine.observe target observer) := by
  refine ⟨held.1.observe root table world machine target observer allowed, ?_⟩
  unfold RunMachine.observe RunMachine.modify
  split
  · exact held.2
  · intro row member
    obtain ⟨old, inside, same⟩ := List.mem_map.mp member
    rw [← same]
    split
    · rename_i fiber found identity
      exact held.2 fiber (RunMachine.mem_of_fiber? found)
    · exact held.2 old inside

/-- Dropping an observer token changes no selected actor field. -/
theorem MessageState.drop (root : NativeEff) (table : RowTable) (context : MessageContext)
    (world : StageWorld.World) (machine : NativeMachine) (token : Nat)
    (held : MessageState root table context world machine) :
    MessageState root table context world (machine.dropToken token) := by
  refine ⟨held.1.drop root table world machine token, ?_⟩
  intro row member
  obtain ⟨old, inside, same⟩ := List.mem_map.mp member
  rw [← same]
  exact held.2 old inside

/-- Actual admitted interruption retains the selected actor and the complete machine together. -/
theorem MessageState.interruption (root : NativeEff) (table : RowTable) (context : MessageContext)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (member : fiber ∈ machine.fibers) (cause : CauseV)
    (held : MessageState root table context world machine)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    MessageState root table context world (machine.update (interruptWithCause cause fiber).1) := by
  refine ⟨held.1.interruption root table world machine fiber member cause untyped marked, ?_⟩
  intro row inside
  obtain ⟨old, present, same⟩ := List.mem_map.mp inside
  rw [← same]
  split
  · intro identity
    have fields := interruption_fields fiber cause
    have original : fiber.id = context.1 := fields.1.symm.trans identity
    have selected := held.2 fiber member original
    cases outcome : context.2
    all_goals simp only [outcome] at selected ⊢
    case finished exit => exact fields.2.2.1.trans selected
    all_goals exact (live_interruption root table world fiber cause selected
      (held.1.metadata fiber member).recorded untyped marked)
  · exact held.2 old present

/-- The existing contextual edit-word producer consumes actual observer and cause admission. -/
theorem messages_on (root : NativeEff) (table : RowTable) (editOrder : Effect4.Laws.Effects.WorldOrder StageWorld.World) :
    ContextualMessages.Admitted (order := editOrder) (P := MessageState root table)
      (Q := EvaluationQueue) (fun (_ : MessageContext) message => MessageAt message) := by
  constructor
  intro context world message machine commands admitted held queued
  cases message with
  | observe target observer =>
    exact ⟨world, editOrder.refl world, held.observe root table context world machine target observer admitted,
      fun command member => queued command (by simpa only [applyFiberEdit, List.append_nil] using member)⟩
  | dropToken token =>
    exact ⟨world, editOrder.refl world, held.drop root table context world machine token,
      fun command member => queued command (by simpa only [applyFiberEdit, List.append_nil] using member)⟩
  | interrupt target cause =>
    cases found : machine.fiber? target with
    | none =>
      refine ⟨world, editOrder.refl world, ?_, ?_⟩
      · simpa only [applyFiberEdit, found] using held
      · simpa only [applyFiberEdit, found, List.append_nil] using queued
    | some fiber =>
      refine ⟨world, editOrder.refl world, ?_, ?_⟩
      · simpa only [applyFiberEdit, found] using
          held.interruption root table context world machine fiber (RunMachine.mem_of_fiber? found) cause admitted.1 admitted.2
      · intro command member
        simp only [applyFiberEdit, found, List.mem_append] at member
        rcases member with prior | added
        · exact queued command prior
        · split at added
          · exact ⟨target, List.mem_singleton.mp added⟩
          · cases added

/-- Stage-world advancement remains the original admitted-message interface. -/
theorem messages (root : NativeEff) (table : RowTable) :
    ContextualMessages.Admitted (order := order) (P := MessageState root table)
      (Q := EvaluationQueue) (fun (_ : MessageContext) message => MessageAt message) :=
  messages_on root table order

/-- Addressed messages do not change the chosen stage world. -/
def fixedMessageOrder : Effect4.Laws.Effects.WorldOrder StageWorld.World where
  le := Eq
  refl := Eq.refl
  trans first second := first.trans second

/-- The existing actual-message producer retains its stage world exactly.
Consumer: the same-world command, snapshot and stored-task settlement join. -/
theorem message_fixed (root : NativeEff) (table : RowTable) (context : MessageContext)
    (world : StageWorld.World) (message : FiberEdit Err Defect FiberId Ann)
    (machine : NativeMachine) (commands : List Guard.NCmd) (admitted : MessageAt message)
    (held : MessageState root table context world machine) (queued : EvaluationQueue context world machine commands) :
    MessageState root table context world (applyFiberEdit message machine).1 ∧
      EvaluationQueue context world (applyFiberEdit message machine).1 (commands ++ (applyFiberEdit message machine).2) := by
  obtain ⟨next, same, state, queue⟩ :=
    (messages_on root table fixedMessageOrder).one context world message machine commands admitted held queued
  cases same
  exact ⟨state, queue⟩

/-- The existing addressed-word fold carries the selected actor and every queued reader together. -/
theorem messages_queue (root : NativeEff) (table : RowTable) :
    ContextualMessages.Admitted (order := order) (P := MessageState root table)
      (Q := fun _ world machine commands => QueueAt root table world machine commands)
      (fun (_ : MessageContext) message => MessageAt message) := by
  constructor
  intro context world message machine commands admitted held queued
  have state := (message_fixed root table context world message machine [] admitted held
    (fun _ member => by cases member)).1
  exact ⟨world, order.refl world, state,
    queued.edit root table world machine commands message held.1 admitted⟩

/-- Installing the actual native actor seeds its selected outcome permission. -/
theorem NativeCut.message_state (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Moves.NIteration) (cut : NativeCut root table world result) :
    MessageState root table (result.fiber.id, result.outcome) world (result.machine.update result.fiber) := by
  refine ⟨cut.installation.install root table world result.machine result.fiber ?_ cut.actor, ?_⟩
  · have role := cut.role
    cases outcome : result.outcome
    all_goals simp only [OutcomeRole, outcome] at role
    case finished exit => exact .inr (.inr role)
    all_goals exact .inl role
  · intro row member
    obtain ⟨old, inside, same⟩ := List.mem_map.mp member
    rw [← same]
    split
    · intro identity
      exact cut.role
    · rename_i different
      intro identity
      exact False.elim (different identity)

/-- Actual admitted settlement retains the complete stage configuration at one chosen world. -/
theorem NativeCut.settle_configuration (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (id : FiberId) (rest : List Guard.NCmd) (result : Moves.NIteration)
    (cut : NativeCut root table world result)
    (admitted : ∀ message ∈ result.edits, MessageAt message) :
    ∃ next, Future world next ∧ Configuration root table next (settle id rest result).1 := by
  refine (messages root table).settle (result.fiber.id, result.outcome) world id rest result admitted
    (fun next machine _ => Configuration root table next machine) ?_ ?_ ?_ ?_ ?_
  · intro empty
    exact ⟨world, order.refl world,
      cut.installation.settleOutcome root table world id rest result cut.actor cut.role⟩
  · intro nonempty
    exact cut.message_state root table world result
  · intro nonempty command member
    cases member
  · intro middle machine commands future held queued missing
    exact ⟨middle, order.refl middle,
      ⟨held.1.heap, held.1.fresh, held.1.counter, held.1.roles, held.1.metadata, held.1.noRaces, held.1.noDeferreds⟩⟩
  · intro middle machine commands owner future held queued found
    have member := RunMachine.mem_of_fiber? found
    have identity := Guard.fiber_id_of_lookup found
    have selected := held.2 owner member identity
    refine ⟨middle, order.refl middle, ?_⟩
    apply held.1.settleOutcome root table middle id rest
      {result with machine := machine, fiber := owner, nested := commands ++ result.nested, edits := []}
      (held.1.metadata owner member)
    exact selected

end Test.Dogfood.Scenario.Atomic.StageConfiguration
