import Effect4.Laws.Machine.AnswerFlowFamilyPop

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: HeapSites.heap_sites_keep and Timeout's numeric history goals need actual current-head permission.
Consumers: NativeFrameScope.frame_step_at and the Ready form's actual native frame entry.
Reach: existing code and ordered saved edges at the current world, with actual return arms explicit.
This contract grants no future weakening, cleanup completion, source allocation or command history.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)

/-- A completed frame carries its exit permission; a running frame carries the actual code and saved path. -/
def FamilyStep (world : World) (output : Kind) : FrameStep ν σ β ε δ ι α → Prop
  | .running fiber => FamilyResult model Edge world output fiber.current fiber.stack
  | .finished exit => ExitAt model world output exit

/-- Current entry reads the present world and exposes the actual body, hook or saved edge.
The value and cause return arms remain separate, because a native finalizer may intercept them. -/
inductive HeadAt (world : World) (input : Kind) : Prim ν σ β ε δ ι α → Prop
  | success (value : β) (good : model.value world input value) : HeadAt world input (.success value)
  | failure (cause : Cause ε δ ι α) (good : model.cause world input cause) : HeadAt world input (.failure cause)
  | sync (thunk : σ) (good : model.value world input (interp.syncValue thunk)) : HeadAt world input (.sync thunk)
  | suspend (thunk : σ) (code : model.code world input (interp.suspendBody thunk)) : HeadAt world input (.suspend thunk)
  | withFiber (thunk : σ) (code : model.code world input (interp.suspendBody thunk)) : HeadAt world input (.withFiber thunk)
  | yieldableError (error : ε) (good : model.cause world input (Cause.fail error)) : HeadAt world input (.yieldableError error)
  | iterator (name : ν) (cursor : β) (code : model.code world input (.iterator name cursor))
      (answer : ∀ next pushed, (Prim.iterator name cursor : Prim ν σ β ε δ ι α).armA interp cursor none = some (next, pushed) →
        FamilyResult model Edge world input next pushed) : HeadAt world input (.iterator name cursor)
  | onSuccess (middle : Kind) (body : Prim ν σ β ε δ ι α) (name : ν)
      (code : model.code world middle body) (saved : Edge world middle input (.onSuccess body name)) :
      HeadAt world input (.onSuccess body name)
  | onSuccessConst (middle : Kind) (body next : Prim ν σ β ε δ ι α)
      (code : model.code world middle body) (saved : Edge world middle input (.onSuccessConst body next)) :
      HeadAt world input (.onSuccessConst body next)
  | onFailure (middle : Kind) (body : Prim ν σ β ε δ ι α) (name : ν)
      (code : model.code world middle body) (saved : Edge world middle input (.onFailure body name)) :
      HeadAt world input (.onFailure body name)
  | onSuccessAndFailure (middle : Kind) (body : Prim ν σ β ε δ ι α) (success failure : ν)
      (code : model.code world middle body) (saved : Edge world middle input (.onSuccessAndFailure body success failure)) :
      HeadAt world input (.onSuccessAndFailure body success failure)
  | exitFrame (middle : Kind) (body : Prim ν σ β ε δ ι α)
      (code : model.code world middle body) (saved : Edge world middle input (.exitFrame body)) :
      HeadAt world input (.exitFrame body)
  | onExit (middle : Kind) (body : Prim ν σ β ε δ ι α) (name : ν) (flag : Bool)
      (code : model.code world middle body) (saved : Edge world middle input (.onExit body name flag)) :
      HeadAt world input (.onExit body name flag)
  | setInterruptible (flag : Bool) (good : model.cause world input (Cause.die interp.notImplemented)) :
      HeadAt world input (.setInterruptible flag)
  | asyncFinalizer (name : ν) (good : model.cause world input (Cause.die interp.notImplemented)) :
      HeadAt world input (.asyncFinalizer name)
  | yieldNowWith (priority : Nat) (code : model.code world input (.yieldNowWith priority)) :
      HeadAt world input (.yieldNowWith priority)
  | async (register : ν) (signal : Bool) (cancel : Option ν) (code : model.code world input (.async register signal cancel)) :
      HeadAt world input (.async register signal cancel)
  | whileLoop (name : ν) (cursor : β)
      (proceed : ∀ next body, interp.loopEnter name cursor = .continue next body →
        FamilyResult model Edge world input body [.whileLoop name next])
      (finish : ∀ body, interp.loopEnter name cursor = .finish body → FamilyResult model Edge world input body []) :
      HeadAt world input (.whileLoop name cursor)

/-- One existing frame step consumes its current-head permission and actual return-arm producers.
Native store operations use PrimitiveProducer instead of the pure syncValue branch. -/
theorem frame_step (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α)
    (head : HeadAt model interp Edge world input fiber.current)
    (stack : Path (Edge world) input output fiber.stack)
    (valueReturn : ∀ value provided,
      ((fiber.current = .success value ∧ provided = some (.success value)) ∨
        ∃ thunk, fiber.current = .sync thunk ∧ value = interp.syncValue thunk ∧ provided = none) →
      model.value world input value →
      FamilyStep model Edge world output (fiber.resumeValue interp value provided).1)
    (causeReturn : ∀ cause, fiber.current = .failure cause → model.cause world input cause →
      FamilyStep model Edge world output (fiber.resumeCause interp cause (some (.failure cause))).1) :
    FamilyStep model Edge world output (fiber.step interp).1 := by
  generalize current : fiber.current = code at head
  cases head
  all_goals simp only [FrameFiber.step, current]
  case success value good => exact valueReturn value _ (.inl ⟨current, rfl⟩) good
  case failure cause good => exact causeReturn cause current good
  case sync thunk good => exact valueReturn _ none (.inr ⟨thunk, current, rfl, rfl⟩) good
  case iterator name cursor code answer =>
    cases actual : (Prim.iterator name cursor : Prim ν σ β ε δ ι α).armA interp cursor none with
    | none => exact ⟨input, by rw [current]; exact code, stack⟩
    | some result =>
      obtain ⟨next, pushed⟩ := result
      obtain ⟨middle, code, pushedPath⟩ := answer next pushed actual
      exact ⟨middle, code, Path.append pushedPath stack⟩
  case whileLoop name cursor proceed finish =>
    cases actual : interp.loopEnter name cursor with
    | «continue» next body =>
      obtain ⟨middle, code, pushedPath⟩ := proceed next body actual
      exact ⟨middle, code, Path.append pushedPath stack⟩
    | finish body =>
      obtain ⟨middle, code, pushedPath⟩ := finish body actual
      exact ⟨middle, code, Path.append pushedPath stack⟩
  case onSuccess middle body name code saved => exact ⟨middle, code, .cons saved stack⟩
  case onSuccessConst middle body next code saved => exact ⟨middle, code, .cons saved stack⟩
  case onFailure middle body name code saved => exact ⟨middle, code, .cons saved stack⟩
  case onSuccessAndFailure middle body success failure code saved => exact ⟨middle, code, .cons saved stack⟩
  case exitFrame middle body code saved => exact ⟨middle, code, .cons saved stack⟩
  case onExit middle body name flag code saved => exact ⟨middle, code, .cons saved stack⟩
  case suspend thunk code => exact ⟨input, code, stack⟩
  case withFiber thunk code => exact ⟨input, code, stack⟩
  case yieldableError error good => exact ⟨input, model.failure world input _ good, stack⟩
  case setInterruptible flag good => exact ⟨input, model.failure world input _ good, stack⟩
  case asyncFinalizer name good => exact ⟨input, model.failure world input _ good, stack⟩
  case yieldNowWith priority code => exact ⟨input, by rw [current]; exact code, stack⟩
  case async register signal cancel code => exact ⟨input, by rw [current]; exact code, stack⟩
end Effect4.Machine.AnswerFlow
