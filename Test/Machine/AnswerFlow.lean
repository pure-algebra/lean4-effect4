import Effect4.Laws.Machine.AnswerFlowCausePop
import Effect4.Laws.Machine.AnswerFlowActions
import Effect4.Program.Compile
import Effect4.Laws.Auto.KernelRfl

/-!
Readers: the native constant and failure callbacks at an exact allocation stage.
Controls: current code does not survive a changed stage, and interruption can skip a failure callback.
These finite frame checks establish no scenario history or outside-runtime observation.
-/
set_option autoImplicit false
namespace Test.Machine.AnswerFlow
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow

private def stage : Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Nat Nat where
  future := Nat.le
  future_refl := Nat.le_refl
  future_trans := fun _ _ _ first second => Nat.le_trans first second
  value world kind value := world = kind ∧ value = .unit
  cause world kind _ := world = kind
  code world kind code := world = kind ∧ (code = .success .unit ∨ ∃ cause, code = .failure cause)
  finalizer _ _ _ := none
  success := by
    intro world kind answer good
    exact ⟨good.1, Or.inl (congrArg Prim.success good.2)⟩
  failure := fun _ _ cause good => ⟨good, Or.inr ⟨cause, rfl⟩⟩

private def native : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  interpOf (.succeed (.lit .unit)) []
private def interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann := native.toPrimInterp
private def acting : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx :=
  RunFiber.make ⟨0⟩ (.success .unit) true (2048, false) emptyCtx
private def machine : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  RunMachine.empty Stores.empty
private def frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann := FrameFiber.start (.success .unit)
private def name : EffName := .restore (.success .unit)
private def reason : CauseV := .empty

/-- The real constant pop reads a callback whose state condition follows its incoming unit answer. -/
example : FrameAt stage interp 1 1 {frame with current := .success .unit} := by
  have saved := saved_constant stage interp 1 1 1 (.yieldNowWith 0) (.success .unit)
    (fun _ _ _ good => ⟨good.1, Or.inl rfl⟩) (fun _ _ _ good => good)
  exact (resume_constant stage interp 1 1 1 1 frame (.yieldNowWith 0) (.success .unit) .unit none
    rfl ⟨rfl, rfl⟩ (by intro exit member; cases member) saved (.nil 1 1)).2

/-- The native restore callback reads the failure class at the selected handler. -/
example : FrameAt stage interp 1 1 {frame with current := interp.contE name reason} := by
  have saved := saved_failure stage interp 1 1 1 (.success .unit) name
    (fun _ _ _ good => good) (fun _ _ cause good => ⟨good, Or.inr ⟨cause, rfl⟩⟩)
    (fun _ _ _ _ _ good _ _ => good)
  exact (resume_failure stage interp 1 1 1 1 frame (.success .unit) name reason none
    rfl rfl rfl (by intro exit member; cases member) saved (.nil 1 1)).2

/-- A later allocation stage does not retain arbitrary transient current code. -/
example : ¬ stage.code 2 1 (.success .unit) := by
  intro held
  cases held.1

/-- The same native handler is skipped when the fiber carries an enabled interruption. -/
example : (match (({frame with interruptedCause := some reason, stack := [.onFailure (.success .unit) name]}).resumeCause interp reason none).1 with
    | .finished _ => true
    | .running _ => false) = true := by
  kernel_rfl

/-- A real onExit mask hook inserts a saved identity frame above its existing suffix. -/
example : StackAt stage interp 1 1 1 ((Prim.onExit (.success .unit) name false).ensure frame).1.stack := by
  exact ensure_stack stage interp 1 1 1 (.onExit (.success .unit) name false) frame (.nil 1 1)

/-- A restoring mask types its actual pending failure at the committed answer stage. -/
example : FrameAt stage interp 1 1
    {((Prim.setInterruptible true).ensure {frame with interruptedCause := some reason}).1 with
      current := .failure reason} := by
  exact ensure_replacement stage interp 1 1 1 1 (.setInterruptible true) (.failure reason)
    {frame with interruptedCause := some reason} (saved_mask stage interp 1 1 true)
    (fun _ _ => rfl) (.nil 1 1) (by kernel_rfl)

/-- The native resume crosses a mask and a missing value arm before invoking its actual callback. -/
example : ∃ next events,
    ({frame with stack := [.setInterruptible false, .onFailure (.success .unit) name,
      .onSuccessConst (.yieldNowWith 0) (.success .unit)]}).resumeValue interp .unit none =
      (.running next, events) ∧ FrameAt stage interp 1 1 next := by
  have failed := saved_failure stage interp 1 1 1 (.success .unit) name
    (fun _ _ _ good => good) (fun _ _ cause good => ⟨good, Or.inr ⟨cause, rfl⟩⟩)
    (fun _ _ _ _ _ good _ _ => good)
  have constant := saved_constant stage interp 1 1 1 (.yieldNowWith 0) (.success .unit)
    (fun _ _ _ good => ⟨good.1, Or.inl rfl⟩) (fun _ _ _ good => good)
  have result := resumeValue_selected stage interp 1 1 1
    {frame with stack := [.setInterruptible false, .onFailure (.success .unit) name,
      .onSuccessConst (.yieldNowWith 0) (.success .unit)]}
    .unit (.onSuccessConst (.yieldNowWith 0) (.success .unit)) (.success .unit) [] none
    (Or.inl rfl) ⟨rfl, rfl⟩
    (.cons (saved_mask stage interp 1 1 false) (.cons failed (.cons constant (.nil 1 1))))
    (by kernel_rfl) rfl rfl
  rcases result with ⟨events, equation, typed⟩
  exact ⟨_, events, equation, typed⟩

/-- A pending mask replacement does not satisfy the selected-frame premise of the callback law. -/
example : (({frame with
    interruptedCause := some reason
    stack := [.setInterruptible true, .onSuccessConst (.yieldNowWith 0) (.success .unit)]}).getCont .contA false).answer =
    .replacement (.failure reason) := by
  kernel_rfl

/-- The native failure pop discards an interrupted handler, passes a mask, then invokes the remaining handler. -/
example : ∃ next events,
    ({frame with
      interruptedCause := some reason
      stack := [.onFailure (.success .unit) name, .setInterruptible false,
        .onFailure (.success .unit) name]}).resumeCause interp reason none =
      (.running next, events) ∧ FrameAt stage interp 1 1 next := by
  have saved := saved_failure stage interp 1 1 1 (.success .unit) name
    (fun _ _ _ good => good) (fun _ _ cause good => ⟨good, Or.inr ⟨cause, rfl⟩⟩)
    (fun _ _ _ _ _ good _ _ => good)
  have result := resumeCause_selected stage interp 1 1 1
    {frame with
      interruptedCause := some reason
      stack := [.onFailure (.success .unit) name, .setInterruptible false,
        .onFailure (.success .unit) name]}
    reason (.onFailure (.success .unit) name) (.failure reason) [] rfl
    (.cons saved (.cons (saved_mask stage interp 1 1 false) (.cons saved (.nil 1 1))))
    (by kernel_rfl) rfl (by kernel_rfl)
  rcases result with ⟨events, equation, typed⟩
  exact ⟨_, events, equation, typed⟩

/-- The actual native mask producer consumes a pending cause only at interruptible entry. -/
example : FrameAt stage interp 1 1
    (evaluatePrim.withFiber native machine
      {acting with frame := {acting.frame with interruptible := false, interruptedCause := some reason}}
      false (.setInterruptible (.success .unit) true)).fiber.frame := by
  exact withFiber_mask stage native 1 1 1 machine _ false true (.success .unit)
    ⟨rfl, Or.inl rfl⟩ (.nil 1 1) (fun _ _ _ _ => rfl)

/-- The actual context setter returns the native unit answer above its existing saved suffix. -/
example : FrameAt stage interp 1 1
    (evaluatePrim.withFiber native machine acting false (.setContext emptyCtx)).fiber.frame := by
  exact withFiber_setContext stage native 1 1 1 machine acting false emptyCtx ⟨rfl, rfl⟩ (.nil 1 1)

private def exactAnswer : Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Unit Val where
  future := Eq
  future_refl := Eq.refl
  future_trans := fun _ _ _ first second => first.trans second
  value _ expected value := value = expected
  cause _ _ _ := True
  code _ expected code := code = .success expected ∨ ∃ cause, code = .failure cause
  finalizer _ _ _ := none
  success := fun _ _ _ good => Or.inl (congrArg Prim.success good)
  failure := fun _ _ cause _ => Or.inr ⟨cause, rfl⟩

/-- The actual native fork returns precisely the allocated child handle to its parent. -/
example : FrameAt exactAnswer interp () (.fiber ⟨machine.nextId⟩)
    (evaluatePrim.withFiber native machine acting false
      (.fork (.success .unit) ⟨false, true, .inherit⟩ [2,1])).fiber.frame := by
  exact withFiber_fork_parent exactAnswer native () (.fiber ⟨machine.nextId⟩) (.fiber ⟨machine.nextId⟩)
    machine acting false (.success .unit) ⟨false, true, .inherit⟩ [2,1] rfl (.nil () _)

/-- The same native fork retains the existing row and types the newly initialized child body. -/
example : ∀ row ∈ (evaluatePrim.withFiber native {machine with fibers := [acting], nextId := 1}
    acting false (.fork (.success .unit) ⟨false, true, .inherit⟩ [2,1])).machine.fibers,
    FrameAt stage interp 1 1 row.frame := by
  apply withFiber_fork_rows stage native (fun _ => 1) (fun _ => 1)
  · intro row member
    rw [List.mem_singleton.mp member]
    exact ⟨1, ⟨rfl, Or.inl rfl⟩, .nil 1 1⟩
  · exact ⟨rfl, Or.inl rfl⟩

end Test.Machine.AnswerFlow
