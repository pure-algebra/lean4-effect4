import Effect4.Machine.Frames
import Effect4.Laws.Auto.RuleSets

/-!
Concept: store-typing, R4; scope-lifetime-finalization, R11.
Question: the state-indexed saved-answer contract serves Workers.Assertions.logs_step,
Atomic.Cleanup.log_debits and Timeout cleanup ordering.
Reach: predicates over the existing primitive code and ordered saved stack.
The world and its future relation remain parameters. A native instance retains the owner and store.
Limit: these definitions supply no source, allocation or command preservation premise.
Consumer: the actual root allocation binders and cleanup callback instances.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- An answer predicate reads the actual world after the operation.
The code predicate annotates existing primitives; it is not stored syntax. -/
structure Model (World Kind : Type w) where
  future : World → World → Prop
  future_refl : ∀ world, future world world
  future_trans : ∀ first middle last, future first middle → future middle last → future first last
  value : World → Kind → β → Prop
  cause : World → Kind → Cause ε δ ι α → Prop
  code : World → Kind → Prim ν σ β ε δ ι α → Prop
  finalizer : World → ν → Exit β ε δ ι α → Option (Prim ν σ β ε δ ι α)
  success : ∀ world kind answer, value world kind answer → code world kind (.success answer)
  failure : ∀ world kind reason, cause world kind reason → code world kind (.failure reason)

variable {World Kind : Type w}
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)

/-- Each exit retains its own state and phase obligation. -/
def ExitAt (world : World) (kind : Kind) : Exit β ε δ ι α → Prop
  | .success value => model.value world kind value
  | .failure cause => model.cause world kind cause

/-- The native evaluator intercepts an answering onExit before invoking its pure arm.
The instance supplies the actual installed finalizer program, including its restore wrapper. -/
def programOf (world : World) : Prim ν σ β ε δ ι α → Exit β ε δ ι α → Option (Prim ν σ β ε δ ι α)
  | .onExit _ name _, exit => model.finalizer world name exit
  | _, _ => none

mutual
/-- A saved frame relates its incoming answer class to the remaining stack's class.
Its callback clauses read every permitted future world, not the world before allocation. -/
inductive SavedAt
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α) : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop
  | mk (world : World) (input output : Kind) (frame : Prim ν σ β ε δ ι α)
      (skip : ∀ nextWorld, model.future world nextWorld → ∀ value,
        model.value nextWorld input value → frame.hasArm .contA = false →
        model.value nextWorld output value)
      (skipCause : ∀ nextWorld, model.future world nextWorld → ∀ cause,
        model.cause nextWorld input cause → frame.hasArm .contE = false →
        model.cause nextWorld output cause)
      (answer : ∀ nextWorld, model.future world nextWorld → ∀ value provided next pushed,
        model.value nextWorld input value →
        (∀ exit ∈ provided, ExitAt model nextWorld input exit) →
        programOf model nextWorld frame (provided.getD (.success value)) = none →
        frame.armA interp value provided = some (next, pushed) →
        ResultAt model interp nextWorld output next pushed)
      (cause : ∀ nextWorld, model.future world nextWorld → ∀ cause provided next pushed,
        model.cause nextWorld input cause →
        (∀ exit ∈ provided, ExitAt model nextWorld input exit) →
        programOf model nextWorld frame (provided.getD (.failure cause)) = none →
        frame.armE interp cause provided = some (next, pushed) →
        ResultAt model interp nextWorld output next pushed)
      (program : ∀ nextWorld, model.future world nextWorld → ∀ exit next,
        ExitAt model nextWorld input exit → programOf model nextWorld frame exit = some next →
        model.code nextWorld output next) :
      SavedAt model interp world input output frame

/-- The actual saved list composes frame contracts through their intermediate answer classes. -/
inductive StackAt
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α) : World → Kind → Kind → List (Prim ν σ β ε δ ι α) → Prop
  | nil (world : World) (kind : Kind) : StackAt model interp world kind kind []
  | cons {world : World} {input middle output : Kind} {frame : Prim ν σ β ε δ ι α}
      {rest : List (Prim ν σ β ε δ ι α)}
      (head : SavedAt model interp world input middle frame)
      (tail : StackAt model interp world middle output rest) :
      StackAt model interp world input output (frame :: rest)

/-- A callback returns its current code and the saved frames it actually pushes. -/
inductive ResultAt
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α) : World → Kind → Prim ν σ β ε δ ι α →
      List (Prim ν σ β ε δ ι α) → Prop
  | mk (world : World) (middle output : Kind) (next : Prim ν σ β ε δ ι α)
      (pushed : List (Prim ν σ β ε δ ι α))
      (current : model.code world middle next) (stack : StackAt model interp world middle output pushed) :
      ResultAt model interp world output next pushed
end

/-- The current answer class joins the saved list's input class.
Consumer: state-changing native operations and actual primitive frame steps. -/
def FrameAt (world : World) (output : Kind) (frame : FrameFiber ν σ β ε δ ι α) : Prop :=
  ∃ input, model.code world input frame.current ∧ StackAt model interp world input output frame.stack

/-- A saved contract retains its future clauses when the store advances.
Current code deliberately has no such unrestricted law: allocation phases are transient. -/
theorem saved_mono {world nextWorld : World} (future : model.future world nextWorld)
    {input output : Kind} {frame : Prim ν σ β ε δ ι α}
    (held : SavedAt model interp world input output frame) :
    SavedAt model interp nextWorld input output frame := by
  cases held with
  | mk _ _ _ _ skip skipCause answer cause program =>
    exact .mk nextWorld input output frame
      (fun last later => skip last (model.future_trans world nextWorld last future later))
      (fun last later => skipCause last (model.future_trans world nextWorld last future later))
      (fun last later => answer last (model.future_trans world nextWorld last future later))
      (fun last later => cause last (model.future_trans world nextWorld last future later))
      (fun last later => program last (model.future_trans world nextWorld last future later))

/-- The ordered saved suffix moves to the state after a successful store operation. -/
theorem stack_mono {world nextWorld : World} (future : model.future world nextWorld)
    {input output : Kind} {frames : List (Prim ν σ β ε δ ι α)}
    (held : StackAt model interp world input output frames) :
    StackAt model interp nextWorld input output frames := by
  induction frames generalizing input output with
  | nil => cases held; exact .nil nextWorld input
  | cons frame rest ih =>
    cases held with
    | cons head tail => exact .cons (saved_mono model interp future head) (ih tail)

/-- A state-changing sync answer joins the same saved input class in the new state.
Consumer: real native store-operation equations supply the returned value and future relation. -/
theorem sync_answer {world nextWorld : World} (future : model.future world nextWorld)
    (input output : Kind) (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (answered : model.value nextWorld input value)
    (stack : StackAt model interp world input output fiber.stack) :
    FrameAt model interp nextWorld output {fiber with current := .success value} :=
  ⟨input, model.success nextWorld input value answered, stack_mono model interp future stack⟩

/-- A value callback consumes the state after its body answers.
Consumer: actual root allocation binders and saved acquired-value binders. -/
theorem saved_success (world : World) (input output : Kind)
    (body : Prim ν σ β ε δ ι α) (name : ν)
    (callback : ∀ nextWorld, model.future world nextWorld → ∀ value,
      model.value nextWorld input value → model.code nextWorld output (interp.contA name value))
    (skipCause : ∀ nextWorld, model.future world nextWorld → ∀ cause,
      model.cause nextWorld input cause → model.cause nextWorld output cause) :
    SavedAt model interp world input output (.onSuccess body name) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_
  · intro nextWorld future value good absent
    cases absent
  · intro nextWorld future cause good absent
    exact skipCause nextWorld future cause good
  · intro nextWorld future value provided next pushed good supplied noProgram arm
    change some (interp.contA name value, []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ [] (callback nextWorld future value good) (.nil nextWorld output)
  · intro nextWorld future cause provided next pushed good supplied noProgram arm
    cases arm
  · intro nextWorld future exit next good program
    cases program

/-- A pushed success frame retains the original body only as inert saved data.
Consumer: the native source body's actual bind push. -/
theorem push_success (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (name : ν)
    (current : fiber.current = .onSuccess body name)
    (first : model.code world input body)
    (callback : SavedAt model interp world input middle (.onSuccess body name))
    (stack : StackAt model interp world middle output fiber.stack) :
    ∃ next events, fiber.step interp = (.running next, events) ∧ FrameAt model interp world output next := by
  simp only [FrameFiber.step, current]
  exact ⟨_, _, rfl, input, first, .cons callback stack⟩

end Effect4.Machine.AnswerFlow
