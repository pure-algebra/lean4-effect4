import Effect4.Laws.Program.CodeClosure.PredicateFamily
import Effect4.Laws.Machine.AnswerFlowNativeIteration
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: full source templates retain actual current and saved code through native dispatch.
Consumer: the finalizer source command invariant.
The existing head, saved-family and native-return producers supply these projections.
These local results establish neither source funding nor complete histories.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.PredicateFamily
open Effect4 Effect4.Machine Effect4.Program

/-- An actual frame carries the same supplied certificate at its current and saved code. -/
def Frame (P : NCode → Prop) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  P fiber.current ∧ ∀ code ∈ fiber.stack, P code

/-- The actual unit-family result recovers its current and saved certificates. -/
theorem frame_of_result (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : ∃ output, AnswerFlow.FamilyResult ((spec root table P rules).model view)
      (edge P) () output fiber.current fiber.stack) : Frame P fiber := by
  obtain ⟨output, input, code, saved⟩ := held
  exact ⟨code, path_owned P saved⟩

/-- Native ordinary dispatch is a projection of the existing head producer. -/
theorem step_frame (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (held : Frame P fiber.frame)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    Frame P (evaluatePrim.stepFrame (interpAt root view table) machine fiber yielding).fiber.frame := by
  apply frame_of_result root table P rules view
  exact AnswerFlow.External.Native.step_frame ((spec root table P rules).model view)
    (interpAt root view table) (edge P) () () () machine fiber yielding
    held.1 (path P fiber.frame.stack held.2) (head root table P rules view _ held.1)
    noSuccess noFailure noSync

/-- Native finalizer dispatch reuses the actual saved-family result and terminal return producer. -/
theorem finalizer_frame (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (selected : fiber.frame.current = .ofExit exit) (held : Frame P fiber.frame) :
    Frame P (evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit).fiber.frame := by
  apply frame_of_result root table P rules view
  exact AnswerFlow.External.Native.finalizer_frame ((spec root table P rules).model view)
    (interpAt root view table) (edge P) (family root table P rules view)
    (fun _ _ => rules.mask true) () () () machine fiber yielding exit selected
    held.1 (path P fiber.frame.stack held.2) (by cases exit <;> trivial)
    (fun _ _ => trivial) (fun _ _ => rfl)

end Effect4.Program.CodeClosure.PredicateFamily
