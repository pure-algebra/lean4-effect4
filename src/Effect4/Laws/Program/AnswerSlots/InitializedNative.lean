import Effect4.Laws.Program.AnswerSlots.InitializedIteration
import Effect4.Laws.Program.AnswerSlots.InitializedCounts
import Effect4.Laws.Program.AnswerSlots.InitializedScopes
import Effect4.Laws.Program.AnswerSlots.InitializedActionFacts

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: every actual native crew primitive retains its current class and saved answer path.
Reach: the shared primitive producer, actual store replies and protected captured scope fields.
Limit: stored rows, parked demands and command admission are joined by the coupled history driver.
Consumer: Workers and QueueWorkers initialized log-history producer.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The actual native primitive joins source classes, returned values and captured cleanup ownership. -/
theorem primitive_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec view ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec view) (Edge spec view) ⟨fiber.id, next.machine.state⟩ result
      next.fiber.frame.current next.fiber.frame.stack := by
  have producer := Moves.evaluatePrim_producer (interpAt spec.root view spec.table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding = result at producer ⊢
  dsimp only
  cases producer with
  | step unparked ordinary noSync noSuccess noFailure noYield noAsync =>
    have state := StatePreservation.stepFrame (interpAt spec.root view spec.table)
      (fun state => state = machine.state) machine fiber yielding rfl
    rw [state]
    exact step_frame spec fragment view _ input output machine fiber yielding owned saved noSuccess noFailure noSync
  | finalizer exit current =>
    have state := StatePreservation.finalizerOr (interpAt spec.root view spec.table)
      (fun state => state = machine.state) machine fiber yielding exit rfl
    rw [state]
    exact finalizer_frame spec fragment view _ input output machine fiber yielding exit current owned saved
  | action thunk action current unparked found =>
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
    refine ⟨output, SourceScope.with_fiber_family (model spec view) (Edge spec view)
      spec.root view spec.table ⟨fiber.id, next.machine.state⟩ (.stable .root) output machine fiber yielding action
      (action_facts spec view _ afterReady)
      (code_rebase spec _ _ _ owned _ future counts.1.symm counts.2.symm)
      (path_future spec view _ _ future _ output fiber.frame.stack saved) programs ?_⟩
    intro scope exit state program closed
    exact .stable afterReady ((Typed.interp_close spec.toSpec view scope exit fiber.frame.interruptible
      fiber.id machine.state state (some program) scopes closed).2 program rfl)
  | sync thunk state value current unparked found =>
    exact ⟨output, sync_frame spec view _ input output fiber.frame thunk state value current owned saved found⟩
  | fallback thunk current unparked missing =>
    exact ⟨output, fallback_frame spec view _ input output fiber.frame thunk current owned saved missing⟩
  | yieldNow priority current =>
    exact ⟨output, yield_frame spec view _ input output fiber.frame priority owned current saved⟩
  | asyncImmediate name signal cancel state code current registered =>
    exact ⟨output, immediate_frame spec view _ input output fiber.frame name signal cancel machine.nextToken
      state code owned current saved registered⟩
  | asyncParked name signal cancel state current registered =>
    have result := parked_frame spec view ⟨fiber.id, machine.state⟩ input output fiber.frame
      name signal cancel machine.nextToken state owned current saved registered
    dsimp only at result
    split
    · rename_i push
      rw [if_pos push] at result
      exact ⟨output, result⟩
    · rename_i push
      rw [if_neg push] at result
      exact ⟨output, result⟩
  | rejectedPark cause park =>
    exact ⟨output, input, .failure (code_phase spec _ input _ owned), saved⟩
  | racePark race park =>
    unfold registerRace
    split <;> exact ⟨output, input, owned, saved⟩
  | countdownPark targets next returned parked edits park counted =>
    obtain ⟨same, ready⟩ := park_shape spec view _ input fiber.frame.current owned (by rw [park]; intro wrong; cases wrong)
    subst input
    have result := countdown_frame spec view ⟨fiber.id, machine.state⟩ output machine fiber targets false ready owned saved
    have state := StatePreservation.countdown_plan_state (interpAt spec.root view spec.table) machine fiber targets .exitsValue false
    rw [counted] at result state
    dsimp only at result state
    rw [state]
    exact ⟨output, result⟩
  | joinMissing target mode park missing => exact ⟨output, input, owned, saved⟩
  | joinExited target mode other exit park found exited =>
    obtain ⟨same, ready⟩ := park_shape spec view _ input fiber.frame.current owned (by rw [park]; intro wrong; cases wrong)
    subst input
    exact ⟨output, .stable .root, joined_code spec view _ ready exit mode, saved⟩
  | joinWaiting target mode other park found live =>
    obtain ⟨same, ready⟩ := park_shape spec view _ input fiber.frame.current owned (by rw [park]; intro wrong; cases wrong)
    subst input
    exact ⟨output, .stable .root, owned, .cons (async_edge spec view _ ready _) saved⟩
end Effect4.Program.AnswerSlots.Initialized
