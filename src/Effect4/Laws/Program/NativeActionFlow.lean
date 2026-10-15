import Effect4.Laws.Program.NativeActions
import Effect4.Laws.Machine.AnswerFlowRun

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: initialized crew histories retain the parent's actual saved answer path through actions.
Reach: the native action evaluator, an external saved family, and its broad action input class.
Limit: store transport, child initialization and scope capture remain separate local facts.
Consumer: the shared initialized driver for Workers.logs_step and QueueWorkers.logs_history.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts Effect4.Machine.AnswerFlow
universe w
variable {World Kind : Type w}
variable (model : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
  (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) World Kind)
variable (Edge : World → Kind → Kind → NCode → Prop)

/-- The action input accepts administrative answers and the two actual saved control frames. -/
structure ActionFlowFacts (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (input : Kind) : Prop where
  value : ∀ value, model.value world input value
  cause : ∀ cause, model.cause world input cause
  interrupt : ∀ target, model.code world input ((interpAt root view table).interruptCode target)
  interruptAs : ∀ target owner, model.code world input ((interpAt root view table).interruptAsCode target owner)
  park : ∀ race, model.code world input ((interpAt root view table).parkCode (.race race))
  mask : ∀ flag, Edge world input input (.setInterruptible flag)
  cancel : ∀ owner token, Edge world input input
    (.asyncFinalizer ((interpAt root view table).cancelName (interpAt root view table).parkCancelName owner token))

/-- A mask pushes its actual restoring edge before the existing saved suffix. -/
theorem masked_family (world : World) (input output : Kind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (body : NCode) (code : model.code world input body)
    (mask : Edge world input input (.setInterruptible true))
    (stack : Contracts.Path (Edge world) input output frame.stack) :
    FamilyResult model Edge world output body frame.uninterruptible.stack := by
  unfold FrameFiber.uninterruptible
  split
  · exact ⟨input, code, .cons mask stack⟩
  · exact ⟨input, code, stack⟩

/-- Enabling interruption either enters the body or delivers the actual pending cause. -/
theorem interruptible_family (world : World) (input output : Kind)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (body : NCode)
    (code : model.code world input body)
    (mask : Edge world input input (.setInterruptible false))
    (causes : ∀ cause, model.cause world input cause)
    (stack : Contracts.Path (Edge world) input output frame.stack) :
    FamilyResult model Edge world output (frame.interruptibleRegion.2.getD body)
      frame.interruptibleRegion.1.stack := by
  unfold FrameFiber.interruptibleRegion
  split
  · exact ⟨input, code, stack⟩
  · cases actual : frame.interruptedCause with
    | none =>
      simp only [FrameFiber.setFiberInterruptible, actual]
      exact ⟨input, code, .cons mask stack⟩
    | some cause =>
      simp only [FrameFiber.setFiberInterruptible, actual]
      exact ⟨input, model.failure world input cause (causes cause), .cons mask stack⟩

/-- The countdown keeps the old current code when parked and its actual cancellation edge. -/
theorem countdown_family (root : NativeEff) (view) (table : RowTable)
    (world : World) (input output : Kind) (m : NativeMachine) (fiber : SourceFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (code : model.code world input fiber.frame.current)
    (stack : Contracts.Path (Edge world) input output fiber.frame.stack)
    (answer : ∀ exits, model.code world input (countdownPark.resumePrim (interpAt root view table) resume exits))
    (cancel : Edge world input input
      (.asyncFinalizer ((interpAt root view table).cancelName (interpAt root view table).parkCancelName fiber.id m.nextToken))) :
    let next := (countdownParkEdits (interpAt root view table) m fiber targets resume failFast).2.1
    FamilyResult model Edge world output next.frame.current next.frame.stack := by
  dsimp only
  unfold countdownParkEdits
  dsimp only
  split
  · exact ⟨input, answer _, stack⟩
  · exact ⟨input, code, .cons cancel stack⟩

/-- Every native action retains the parent's actual saved path at its supplied post-operation world.
The caller proves the store transfer separately; no arbitrary current-code monotonicity is assumed. -/
theorem with_fiber_family (root : NativeEff) (view) (table : RowTable)
    (world : World) (input output : Kind) (m : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (action : NAction)
    (facts : ActionFlowFacts model Edge root view table world input)
    (code : model.code world input fiber.frame.current)
    (stack : Contracts.Path (Edge world) input output fiber.frame.stack)
    (source : ActionProgramsAt root (fun _ => model.code world input) action)
    (closed : ∀ scope exit state program,
      (interpAt root view table).closeScope scope exit fiber.frame.interruptible fiber.id m.state = some (state, some program) →
      model.code world input program) :
    let next := evaluatePrim.withFiber (interpAt root view table) m fiber yielding action
    FamilyResult model Edge world output next.fiber.frame.current next.fiber.frame.stack := by
  dsimp only
  have success (value : Val) := model.success world input value (facts.value value)
  have failure (cause : CauseV) := model.failure world input cause (facts.cause cause)
  cases action
  case fork body options site =>
    cases options with
    | mk immediate daemon mode =>
      cases daemon <;> cases immediate
      all_goals exact ⟨input, success _, stack⟩
  case forkIn body options scope site =>
    cases options with
    | mk immediate daemon mode =>
      cases immediate
      all_goals exact ⟨input, success _, stack⟩
  case forkScoped body options site =>
    simp only [evaluatePrim.withFiber]
    split
    · cases options with
      | mk immediate daemon mode =>
        cases immediate
        all_goals exact ⟨input, success _, stack⟩
    · exact ⟨input, failure _, stack⟩
  case ambientScope =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨input, success _, stack⟩
    · exact ⟨input, failure _, stack⟩
  case runIn target scope => exact ⟨input, success _, stack⟩
  case interrupt target => exact ⟨input, facts.interruptAs target fiber.id, stack⟩
  case interruptAs target owner =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split
    all_goals exact ⟨input, code, stack⟩
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨input, success _, stack⟩
    · exact ⟨input, facts.interrupt target, stack⟩
  case interruptAll targets owner => exact ⟨input, code, stack⟩
  case awaitAll targets =>
    exact countdown_family model Edge root view table world input output m fiber targets .exitsValue false
      code stack (fun _ => success _) (facts.cancel fiber.id m.nextToken)
  case awaitAllFailFast targets =>
    exact countdown_family model Edge root view table world input output m fiber targets .exitsValue true
      code stack (fun _ => success _) (facts.cancel fiber.id m.nextToken)
  case snapshotChildren => exact ⟨input, success _, stack⟩
  case awaitNewChildren snapshot =>
    exact countdown_family model Edge root view table world input output m fiber _ .void false
      code stack (fun _ => success _) (facts.cancel fiber.id m.nextToken)
  case raceAll bodies site => exact ⟨input, facts.park m.nextRace, stack⟩
  case raceAllFirst bodies site => exact ⟨input, facts.park m.nextRace, stack⟩
  case setInterruptible body flag =>
    cases flag with
    | false => exact masked_family model Edge world input output fiber.frame body source (facts.mask true) stack
    | true =>
      exact interruptible_family model Edge world input output fiber.frame body source
        (facts.mask false) facts.cause stack
  case setContext context => exact ⟨input, success _, stack⟩
  case getContext => exact ⟨input, success _, stack⟩
  case getId => exact ⟨input, success _, stack⟩
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨input, code, stack⟩
    · exact ⟨input, success _, stack⟩
    · rename_i state program actual
      exact masked_family model Edge world input output fiber.frame program
        (closed scope exit state program actual) (facts.mask true) stack
  case closePar programs => exact ⟨input, code, stack⟩
  case refuse cause => exact ⟨input, failure cause, stack⟩
  case dropObservers token => exact ⟨input, success _, stack⟩
  case cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨input, success _, stack⟩
    · exact ⟨input, code, stack⟩
  case getInterruptible =>
    exact masked_family model Edge world input output fiber.frame _ (success _) (facts.mask true) stack

end Effect4.Program.SourceScope
