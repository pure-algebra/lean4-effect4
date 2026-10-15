import Effect4.Laws.Program.AnswerSlots.TypedFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: protected native code supplies the existing current-head contract.
Reach: every stable native primitive and its actual interpreter callbacks.
Limit: the native store evaluator and initialization remain separate producers.
Consumer: AnswerFlow.frame_step and the joint initialized crew driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Cancellation frames retain the actual administrative cancellation and incoming failure. -/
theorem async_edge (spec : Spec) (completed : List (FiberId × ExitV)) (name : EffName) :
    Edge spec completed () Kind.root Kind.root (.asyncFinalizer name) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, by intro body previous scope flag same; cases same⟩
  refine ⟨?_, ?_, ?_⟩
  · intro view
    refine .mk () Kind.root Kind.root _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro world future value good absent
      trivial
    · intro world future reason good absent
      cases absent
    · intro world future value provided next pushed good supplied absent arm
      cases arm
    · intro world future cause provided next pushed good supplied absent arm
      change some (if cause.hasInterrupts then (interpAt spec.root view spec.table).cancelThenFail name cause
        else .failure cause, []) = some (next, pushed) at arm
      cases arm
      refine .mk world Kind.root Kind.root _ [] ?_ (.nil world Kind.root)
      split
      · exact interp_cancel_at spec view name cause
      · trivial
    · intro world future exit next good program
      cases program
    · intro world future fiber cause delivered good selected interrupted skipped
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- A zero-fuel native suspension stays a live source frontier at its existing answer class. -/
theorem frontier_suspend (spec : Spec) (completed : List (FiberId × ExitV))
    (kind : Kind) (point : Point) (zero : point.fuel = 0) (source : SourcePoint spec point) :
    CodeAt spec kind ((interpAt spec.root completed spec.table).suspendBody (.body point)) := by
  change CodeAt spec kind (suspendBodyAt spec.root (.body {point with completed}))
  simp only [suspendBodyAt, zero]
  exact .inl ⟨rfl, source⟩

/-- The protected stable source graph supplies every actual current-head obligation. -/
theorem head (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (kind : Kind) (code : NCode) (owned : CodeAt spec kind code) :
    AnswerFlow.HeadAt (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (Edge spec completed) () kind code := by
  cases code
  case success value => exact .success value owned
  case failure cause => exact .failure cause trivial
  case sync thunk => cases owned.1; exact .sync thunk trivial
  case suspend thunk =>
    cases thunk
    case body point =>
      rcases owned with ⟨zero, source⟩ | ⟨rfl, source⟩
      · exact .suspend _ (frontier_suspend spec completed kind point zero source)
      · exact .suspend _ (interp_suspend_at spec fragment completed _ source)
    all_goals cases owned.1; exact .suspend _ (interp_suspend_at spec fragment completed _ owned.2)
  case withFiber thunk => cases owned.1; exact .withFiber thunk (interp_suspend_at spec fragment completed thunk owned.2)
  case yieldableError error => cases owned; exact .yieldableError error trivial
  case onSuccess body name =>
    obtain ⟨input, first, callback⟩ := owned
    exact .onSuccess input body name first (success_edge spec fragment completed input kind body name callback)
  case onSuccessConst body next =>
    exact .onSuccessConst Kind.root body next owned.1 (constant_edge spec completed kind body next owned.2)
  case onFailure body name =>
    obtain ⟨rfl, first, callback⟩ := owned
    exact .onFailure Kind.root body name first (failure_edge spec fragment completed body name callback)
  case onSuccessAndFailure body success failure =>
    obtain ⟨rfl, first, positive, negative⟩ := owned
    exact .onSuccessAndFailure Kind.root body success failure first (both_edge spec fragment completed body success failure positive negative)
  case exitFrame body =>
    obtain ⟨rfl, first⟩ := owned
    exact .exitFrame Kind.root body first (exitFrame_edge spec completed body)
  case onExit body name flag =>
    obtain ⟨rfl, first, callback⟩ := owned
    exact .onExit Kind.root body name flag first (onExit_edge spec fragment completed body name flag callback)
  case setInterruptible flag => cases owned; exact .setInterruptible flag trivial
  case asyncFinalizer name => cases owned.1; exact .asyncFinalizer name trivial
  case yieldNowWith priority => exact .yieldNowWith priority owned
  case async register signal cancel => exact .async register signal cancel owned
  case whileLoop name cursor =>
    obtain ⟨rfl, named⟩ := owned
    have bodies := interp_loopEnter_at spec fragment completed name cursor named
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      rw [actual] at bodies
      exact ⟨.root, bodies, .cons (.loop next named) (.nil Kind.root)⟩
    · intro body actual
      rw [actual] at bodies
      exact ⟨.root, bodies, .nil Kind.root⟩
  case iterator name cursor =>
    obtain ⟨rfl, named⟩ := owned
    refine .iterator name cursor ⟨rfl, named⟩ ?_
    intro next pushed arm
    exact (family spec fragment completed).answer () Kind.root Kind.root _ (.iterator cursor named)
      () trivial cursor none next pushed trivial (by intro exit member; cases member)
      rfl arm
end Effect4.Program.AnswerSlots.Typed
