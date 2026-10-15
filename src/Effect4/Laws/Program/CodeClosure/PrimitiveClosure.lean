import Effect4.Laws.Program.CodeClosure.NativeClosure
import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: actual primitive results retain full source templates.
Consumer: FinalizerSource.primitive_frame and its command invariant.
The shared primitive producer supplies every evaluator branch exactly once.
Instances supply actual action results and asynchronous reply certificates.
These local facts establish no history bound or execution progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.PredicateFamily
open Effect4 Effect4.Machine Effect4.Program

/-- Native primitives mint only these non-frame source certificates. -/
structure PrimitiveRules (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (view : List (FiberId × ExitV)) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) : Prop where
  action : ∀ thunk action, fiber.frame.current = .withFiber thunk →
    (interpAt root view table).withFiberOf thunk = some action →
    Frame P (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action).fiber.frame
  reply : ∀ register signal cancel state code, fiber.frame.current = .async register signal cancel →
    (interpAt root view table).registerAsync register fiber.id machine.nextToken machine.state = (state, some code) → P code
  cancel : ∀ register signal cancel, fiber.frame.current = .async register signal cancel →
    P (.asyncFinalizer ((interpAt root view table).cancelName
      (cancel.getD (interpAt root view table).abortName) fiber.id machine.nextToken))
  joinCancel : P (.asyncFinalizer ((interpAt root view table).cancelName
    (interpAt root view table).parkCancelName fiber.id machine.nextToken))
  countdown : ∀ targets, Frame P
    (countdownParkEdits (interpAt root view table) machine fiber targets .exitsValue false).2.1.frame

/-- Every actual primitive returns current and saved certificates from the common producer. -/
theorem primitive_frame (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (held : Frame P fiber.frame) (inputs : PrimitiveRules root table P view machine fiber yielding) :
    Frame P (evaluatePrim (interpAt root view table) machine fiber yielding).fiber.frame := by
  have pushed (code : NCode) (owned : P code) :
      ∀ saved ∈ code :: fiber.frame.stack, P saved := by
    intro saved member
    rcases List.mem_cons.mp member with same | present
    · rw [same]; exact owned
    · exact held.2 saved present
  have exitCode (exit : ExitV) (mode : Supervision.ObserverMode) : P ((interpAt root view table).exitValue exit mode) := by
    cases mode with
    | awaitValue => exact rules.success _
    | joinEffect =>
      cases exit with
      | success value => exact rules.success value
      | failure cause => exact rules.failure cause
  generalize actual : evaluatePrim (interpAt root view table) machine fiber yielding = next
  have producer := Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding
  rw [actual] at producer
  cases producer with
  | step unparked ordinary noSync noSuccess noFailure noYield noAsync =>
    exact step_frame root table P rules view machine fiber yielding held noSuccess noFailure noSync
  | finalizer exit current => exact finalizer_frame root table P rules view machine fiber yielding exit current held
  | action thunk action current unparked found => exact inputs.action thunk action current found
  | sync => exact ⟨rules.success _, held.2⟩
  | fallback => exact ⟨rules.success _, held.2⟩
  | yieldNow => exact ⟨rules.success _, held.2⟩
  | asyncImmediate register signal cancel state code current registered =>
    exact ⟨inputs.reply register signal cancel state code current registered, held.2⟩
  | asyncParked register signal cancel state current registered =>
    dsimp only
    split
    · exact ⟨held.1, pushed _ (inputs.cancel register signal cancel current)⟩
    · exact held
  | rejectedPark => exact ⟨rules.failure _, held.2⟩
  | racePark => unfold registerRace; split <;> exact held
  | countdownPark targets next returned parked edits park counted =>
    have closed := inputs.countdown targets
    rw [counted] at closed
    exact closed
  | joinMissing => exact held
  | joinExited => exact ⟨exitCode _ _, held.2⟩
  | joinWaiting => exact ⟨held.1, pushed _ inputs.joinCancel⟩

end Effect4.Program.CodeClosure.PredicateFamily
