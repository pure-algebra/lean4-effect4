import Effect4.Laws.Program.AnswerSlots.InitializedQueueTransport
import Effect4.Laws.Program.NativeSettlementCommands
import Effect4.Laws.Program.NativeSettlementOwner

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: actual returned native commands satisfy the initialized pending-command observation.
Reach: actual source actions, captured scopes, common native/charged folds and settlement messages.
Limit: pending old-tail transport and the actual command consumer remain the joint driver's facts.
Consumer: command_guarded and the Workers and QueueWorkers log-history endpoints.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The actual native command word carries its owner head and ready tracking, before settlement. -/
structure ReturnedDemand (spec : Spec) (next : Moves.NIteration) : Prop where
  admin : ∀ command ∈ next.nested, ∀ host, Guard.ReturnCommands.Local host command →
    host = next.fiber.id ∧ ∃ thunk, next.fiber.frame.current = .withFiber thunk
  finishFree : ∀ host exit, Cmd.finish host exit ∉ next.nested
  track : ∀ command ∈ next.nested, TrackDemand spec next.machine command

/-- Actual native command production supplies all three observations without assuming queued permission. -/
theorem native_returned (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    ReturnedDemand spec (evaluateNative spec.root machine fiber yielding spec.table) := by
  constructor
  · intro command member host isLocal
    have result := native_admin_path spec fragment machine fiber yielding acting scopes command host member
      (NativeAdminOrigin.of_guard command host isLocal)
    exact ⟨result.1.trans (Moves.evaluateNative_footprint spec.root spec.table machine fiber yielding).id.symm, result.2.2⟩
  · intro host exit member
    apply native_emitted spec.root spec.table machine fiber yielding (.finish host exit) (fun _ => False) _ member
    intro primitiveMember
    exact NativeAdminOrigin.primitive_no_finish spec.root spec.table (interpAt spec.root machine.completedExits spec.table)
      machine fiber yielding host exit primitiveMember
  · intro command member
    cases command <;> simp only [TrackDemand]
    rename_i parent child
    exact native_track_ready spec machine fiber yielding acting parent child member

/-- The common charged fold supplies the same returned-command certificate. -/
theorem iteration_returned (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    ReturnedDemand spec (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding) := by
  apply iteration_fact spec machine fiber yielding acting scopes (fun _ next => ReturnedDemand spec next)
  intro m f y owned captured
  exact native_returned spec fragment m f y owned captured
end Effect4.Program.AnswerSlots.Initialized
