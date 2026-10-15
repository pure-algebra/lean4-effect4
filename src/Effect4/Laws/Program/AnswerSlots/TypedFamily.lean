import Effect4.Laws.Program.AnswerSlots.TypedInterp
import Effect4.Laws.Machine.AnswerFlowRecursiveFamily
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

/-- Native semantic callbacks retain their class endpoints under every completed-fiber view. -/
def Semantic (spec : Spec) :=
  AnswerFlow.ViewSavedAt (fun view => model spec view)
    (fun view => (interpAt spec.root view spec.table).toPrimInterp)

/-- The stable graph retains uniform callbacks and the existing recursive source-name classes. -/
def Edge (spec : Spec) (_completed : List (FiberId × ExitV)) :=
  AnswerFlow.RecursiveFamilyEdge (Semantic spec) Kind.root
    (fun _ => OrdinaryName spec) (fun _ => OrdinaryName spec)

/-- One actual view projects the common class endpoints and actual uniform pushed suffixes. -/
theorem family (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (Edge spec completed) :=
  AnswerFlow.recursive_family_of _ _ _ _ _ _
    (AnswerFlow.ViewSavedAt.family (fun view => model spec view)
      (fun view => (interpAt spec.root view spec.table).toPrimInterp) completed) (hooks spec fragment completed)

/-- Protected value binders use the actual intermediate acquisition class. -/
theorem success_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (input output : Kind) (body : NCode) (name : EffName) (owned : NameAt spec input output name) :
    Edge spec completed () input output (.onSuccess body name) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_success
    · intro world future value good
      exact interp_contA_at spec fragment view input output name value owned good
    · intro world future reason good
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- A constant success continuation retains its next program through every stable future world. -/
theorem constant_edge (spec : Spec) (completed : List (FiberId × ExitV))
    (output : Kind) (body next : NCode) (owned : CodeAt spec output next) :
    Edge spec completed () .root output (.onSuccessConst body next) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_constant
    · intro world future value good
      exact owned
    · intro world future reason good
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- Failure handlers use their actual protected source callback. -/
theorem failure_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (name : EffName) (owned : OrdinaryName spec name) :
    Edge spec completed () .root .root (.onFailure body name) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_failure
    · intro world future value good
      trivial
    · intro world future reason good
      exact interp_contE_at spec fragment view .root .root name reason owned
    · intro world future fiber cause delivered good interrupted skipped
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- Paired source callbacks preserve the broad answer class in either actual result arm. -/
theorem both_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (success failure : EffName) (first : OrdinaryName spec success) (second : OrdinaryName spec failure) :
    Edge spec completed () .root .root (.onSuccessAndFailure body success failure) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_both
    · intro world future value good
      exact interp_contA_at spec fragment view .root .root success value first good
    · intro world future cause good
      exact interp_contE_at spec fragment view .root .root failure cause second
    · intro world future cause
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- Reified exits return ordinary values after the actual native exit frame. -/
theorem exitFrame_edge (spec : Spec) (completed : List (FiberId × ExitV)) (body : NCode) :
    Edge spec completed () .root .root (.exitFrame body) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_exitFrame
    · intro world future exit good
      trivial
    · intro world future cause
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- Source and stored finalizers retain their actual installed restore wrapper. -/
theorem onExit_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV))
    (body : NCode) (name : EffName) (flag : Bool) (owned : OrdinaryName spec name) :
    Edge spec completed () .root .root (.onExit body name flag) := by
  apply AnswerFlow.RecursiveFamilyEdge.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_onExit
    · intro world future exit good absent
      exact exit_at spec _
    · intro world future exit next good installed
      change Option.map (finalizerCode (interpAt spec.root view spec.table) exit)
        ((interpAt spec.root view spec.table).finalizerProgram name exit) = some next at installed
      cases found : (interpAt spec.root view spec.table).finalizerProgram name exit with
      | none => rw [found] at installed; cases installed
      | some program =>
        rw [found] at installed
        cases installed
        exact finalizerCode_at spec view exit program (interp_fin_at spec fragment view name exit program owned found)
    · intro world future cause
      trivial
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

end Effect4.Program.AnswerSlots.Typed
