import Effect4.Laws.Program.AnswerSlots.TypedInterp
import Effect4.Laws.Machine.AnswerFlowRecursive
import Effect4.Laws.Machine.AnswerFlowHooks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the protected native graph supplies the common recursive saved family.
Reach: every actual native callback and protected acquisition class of the direct fragment.
Limit: initialization and guarded command history remain separate producers.
Consumer: the initialized crew native head and evaluator connection.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Stable loops and iterators use the common recursive saved-family abstraction. -/
theorem hooks (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV)) :
    AnswerFlow.RecursiveHooks (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp .root
      (fun _ => OrdinaryName spec) (fun _ => OrdinaryName spec) where
  loop_future := fun _ _ _ _ held => held
  iter_future := fun _ _ _ _ held => held
  loop_resume := by
    intro world name cursor answer held
    have result := interp_loopResume_at spec fragment completed name cursor answer held
    cases actual : (interpAt spec.root completed spec.table).loopResume name cursor answer <;>
      rw [actual] at result <;> exact result
  iter_next := by
    intro world name answer held
    have result := interp_iter_at spec completed name answer held
    cases actual : ((interpAt spec.root completed spec.table).iterNext name answer).2 <;>
      rw [actual] at result <;> exact result

/-- The stable graph shares semantic saved frames with its recursive broad-class names. -/
def Edge (spec : Spec) (completed : List (FiberId × ExitV)) :=
  AnswerFlow.RecursiveEdge (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp .root
    (fun _ => OrdinaryName spec) (fun _ => OrdinaryName spec)

/-- The actual source callback producers instantiate all six saved-family obligations once. -/
theorem family (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (Edge spec completed) :=
  AnswerFlow.recursive_family _ _ _ _ _ (hooks spec fragment completed)

/-- Protected value binders use the actual intermediate acquisition class. -/
theorem success_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (input output : Kind) (body : NCode) (name : EffName) (owned : NameAt spec input output name) :
    Edge spec completed () input output (.onSuccess body name) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_success
  · intro world future value good
    exact interp_contA_at spec fragment completed input output name value owned good
  · intro world future reason good
    trivial

/-- A constant success continuation retains its next program through every stable future world. -/
theorem constant_edge (spec : Spec) (completed : List (FiberId × ExitV))
    (output : Kind) (body next : NCode) (owned : CodeAt spec output next) :
    Edge spec completed () .root output (.onSuccessConst body next) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_constant
  · intro world future value good
    exact owned
  · intro world future reason good
    trivial

/-- Failure handlers use their actual protected source callback. -/
theorem failure_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (name : EffName) (owned : OrdinaryName spec name) :
    Edge spec completed () .root .root (.onFailure body name) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_failure
  · intro world future value good
    trivial
  · intro world future reason good
    exact interp_contE_at spec fragment completed .root .root name reason owned
  · intro world future fiber cause delivered good interrupted skipped
    trivial

/-- Paired source callbacks preserve the broad answer class in either actual result arm. -/
theorem both_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (success failure : EffName) (first : OrdinaryName spec success) (second : OrdinaryName spec failure) :
    Edge spec completed () .root .root (.onSuccessAndFailure body success failure) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_both
  · intro world future value good
    exact interp_contA_at spec fragment completed .root .root success value first good
  · intro world future cause good
    exact interp_contE_at spec fragment completed .root .root failure cause second
  · intro world future cause
    trivial

/-- Reified exits return ordinary values after the actual native exit frame. -/
theorem exitFrame_edge (spec : Spec) (completed : List (FiberId × ExitV)) (body : NCode) :
    Edge spec completed () .root .root (.exitFrame body) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_exitFrame
  · intro world future exit good
    trivial
  · intro world future cause
    trivial

/-- Source and stored finalizers retain their actual installed restore wrapper. -/
theorem onExit_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (name : EffName) (flag : Bool) (owned : OrdinaryName spec name) :
    Edge spec completed () .root .root (.onExit body name flag) := by
  apply AnswerFlow.RecursiveEdge.saved
  apply AnswerFlow.saved_onExit
  · intro world future exit good absent
    exact exit_at spec _
  · intro world future exit next good installed
    change Option.map (finalizerCode (interpAt spec.root completed spec.table) exit)
      ((interpAt spec.root completed spec.table).finalizerProgram name exit) = some next at installed
    cases found : (interpAt spec.root completed spec.table).finalizerProgram name exit with
    | none => rw [found] at installed; cases installed
    | some program =>
      rw [found] at installed
      cases installed
      exact finalizerCode_at spec completed exit program (interp_fin_at spec fragment completed name exit program owned found)
  · intro world future cause
    trivial
end Effect4.Program.AnswerSlots.Typed
