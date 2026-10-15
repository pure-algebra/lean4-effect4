import Effect4.Laws.Program.AnswerSlots.InitializedNativeRows
import Effect4.Laws.Program.Guard.ReturnCommands

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: administrative action commands retain the actual broad-root saved suffix.
Reach: native action entry and its actual post-operation store, including interruption metadata.
Limit: the coupled command queue carries this demand through actual command settlement.
Consumer: afterInterrupt and closePar fields of the initialized command producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- An administrative answer enters the broad root class at the actual retained suffix. -/
def RootPath (spec : Spec) (world : World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  Ready spec world ∧ ∃ output, Effect4.Contracts.Path (Edge spec [] world) (.stable .root) output frame.stack

/-- Administrative queue permission reads the addressed row's saved suffix, independently of current code. -/
def AdminDemand (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) : Prop :=
  ∀ host, Guard.ReturnCommands.Local host command →
    ∀ fiber, machine.fiber? host = some fiber → RootPath spec ⟨host, machine.state⟩ fiber.frame

/-- The actual action retains the same broad-root input at its post-operation store. -/
theorem action_root_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind) (thunk : EffThunk) (action : Guard.ReturnFields.NAction)
    (current : fiber.frame.current = .withFiber thunk)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec [] ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (found : (interpAt spec.root view spec.table).withFiberOf thunk = some action)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action
    RootPath spec ⟨fiber.id, next.machine.state⟩ next.fiber.frame := by
  obtain ⟨same, ready, permission⟩ := action_shape spec _ input thunk (current ▸ owned)
  subst input
  let next := evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action
  have counts := action_counts spec view machine fiber yielding action
  have future : Future ⟨fiber.id, machine.state⟩ ⟨fiber.id, next.machine.state⟩ :=
    ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
  have afterReady := ready_future spec _ _ future ready
  have actual := Typed.interp_action_at spec.toSpec fragment view thunk action permission found
  have programs := SourceScope.ActionProgramsAt.mono spec.root action actual
    (fun _ _ code => CodeAt.stable afterReady code)
  have result := SourceScope.with_fiber_path (model spec view) (Edge spec view)
    spec.root view spec.table ⟨fiber.id, next.machine.state⟩ (.stable .root) output machine fiber yielding action
    (action_facts spec view _ afterReady)
    (code_rebase spec _ _ _ owned _ future counts.1.symm counts.2.symm)
    (path_future spec view _ _ future _ output fiber.frame.stack saved) programs
    (by
      intro scope exit state program closed
      exact .stable afterReady ((Typed.interp_close spec.toSpec view scope exit fiber.frame.interruptible
        fiber.id machine.state state (some program) scopes closed).2 program rfl))
  exact ⟨afterReady, output, result.2⟩

/-- Interruption changes no saved continuation and therefore retains administrative demand. -/
theorem RootPath.interruption (spec : Spec) (world : World) (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : RootPath spec world fiber.frame) : RootPath spec world (interruptWithCause cause fiber).1.frame := by
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals exact held

/-- Growing stores retain an already-ready administrative suffix. -/
theorem RootPath.future (spec : Spec) (first last : World) (future : Future first last)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : RootPath spec first frame) :
    RootPath spec last frame := by
  obtain ⟨ready, output, saved⟩ := held
  exact ⟨ready_future spec first last future ready, output, path_future spec [] first last future _ _ _ saved⟩
end Effect4.Program.AnswerSlots.Initialized
