import Test.Dogfood.Proofs.HostTimeoutNumberPhasePureHead
import Effect4.Laws.Machine.AnswerFlowViewsRefined

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: both Timeout numeric goals retain one set of saved answer classes across actual interpreter views.
Consumer: the pending native producer and its actual finalizer installation.
Reach: nonrecursive numeric saved frames with common input and output classes.
Limit: source capture and actual cleanup provenance remain separate premises.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberUniform
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow

/-- One saved certificate keeps its answer classes when the actual completed-exit view changes. -/
abbrev Edge := AnswerFlow.ViewSavedAt (fun view => model view)
  (fun view => (HostTimeoutFlow.interpreter view).toPrimInterp)

/-- A numeric frame retains one input class and one uniformly certified saved path. -/
def FrameAt (state : Stores) (output : Kind) (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  AnswerFlow.FamilyResult (model []) Edge state output frame.current frame.stack

/-- The shared view family supplies actual callbacks without another saved-frame induction. -/
theorem family (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model view) (HostTimeoutFlow.interpreter view).toPrimInterp Edge :=
  AnswerFlow.ViewSavedAt.refined_family (fun view => model view)
    (fun view => (HostTimeoutFlow.interpreter view).toPrimInterp) Edge
    (fun _ _ _ _ held => held) view

/-- A uniformly certified saved path gives its ordinary semantic path at the actual view. -/
theorem path (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind) (stack : List NCode)
    (held : Effect4.Contracts.Path (Edge state) input output stack) :
    AnswerFlow.StackAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state input output stack := by
  exact AnswerFlow.path_stack (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    (Effect4.Contracts.Path.map (fun _ _ _ edge => edge.each view) held)

/-- The uniform frame supplies every previous view-specific frame reader with the same input class. -/
theorem FrameAt.each (state : Stores) (output : Kind) (frame : HostTimeoutFrames.NativeFrame)
    (held : FrameAt state output frame) (view : HostTimeoutFlow.View) :
    AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state output frame := by
  obtain ⟨input, code, saved⟩ := held
  exact ⟨input, code, path view state input output frame.stack saved⟩

/-- A saved interruptibility flag is uniform and retains exactly the same numeric answer class. -/
theorem mask (state : Stores) (kind : Kind) (flag : Bool) :
    Edge state kind kind (.setInterruptible flag) := by
  constructor
  · intro view
    exact AnswerFlow.saved_mask (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state kind flag
  · intro name cursor impossible; cases impossible
  · intro name cursor impossible; cases impossible

end Test.Dogfood.Proofs.HostTimeoutNumberUniform
