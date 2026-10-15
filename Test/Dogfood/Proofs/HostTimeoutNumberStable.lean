import Test.Dogfood.Proofs.HostTimeoutNumberRegion
import Test.Dogfood.Proofs.HostTimeoutNumberTimer

/-!
Concept: scope-lifetime-finalization R11, with reactive-scheduling R9.
Question: timer and scheduler edits retain the other numeric roles at the same reference heap.
Consumer: the numeric machine, command, and drained-task assertions of both Timeout goals.
Reach: the actual numeric value, cause, code, saved stack, and root region assertions.
Limit: a reference write needs its own phase transition and cannot use this transport.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutNumberStable
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberFlow HostTimeoutNumberRegion

/-- Numeric heap images inspect references only. -/
theorem image_refs (before after : Stores) (same : before.refs = after.refs) (image : Image)
    (owned : ImageAt image before) : ImageAt image after := same.symm.trans owned

/-- Numeric successful values retain their exact post-operation reference image. -/
theorem value_refs (before after : Stores) (same : before.refs = after.refs)
    (kind : HostTimeoutNumberFlow.Kind) (value : Val) (owned : ValueAt before kind value) :
    ValueAt after kind value := by
  cases kind <;> simpa only [ValueAt, ImageAt, same] using owned

/-- Numeric failure classes retain their published exit and reference image. -/
theorem cause_refs (before after : Stores) (same : before.refs = after.refs)
    (kind : HostTimeoutNumberFlow.Kind) (cause : CauseV) (owned : CauseAt before kind cause) :
    CauseAt after kind cause := by
  cases kind
  case read image => exact owned
  case unit image => exact owned
  all_goals simpa only [CauseAt, ImageAt, same] using owned

/-- Both sides of the active-or-cleaned cancellation phase inspect references only. -/
theorem phase_refs (before after : Stores) (same : before.refs = after.refs)
    (image : Image) (own : image.count = image.cleanups.length + 1)
    (phase : ImageAt image before ∨ ∃ exit, ImageAt (image.cleanup own exit) before) :
    ImageAt image after ∨ ∃ exit, ImageAt (image.cleanup own exit) after := by
  simpa only [ImageAt, same] using phase

/-- Numeric current code survives a timer edit because every code premise reads only reference cells. -/
theorem code_refs (before after : Stores) (same : before.refs = after.refs)
    (kind : HostTimeoutNumberFlow.Kind) (code : NCode) (owned : CodeAt before kind code) :
    CodeAt after kind code := by
  induction owned
  case cleanupBound image own view captured fuel delay n error exit count heap =>
    exact .cleanupBound image own view captured fuel delay n error exit count
      (image_refs before after same image heap)
  case cleanupWrite image own view captured fuel delay n error exit count heap =>
    exact .cleanupWrite image own view captured fuel delay n error exit count
      (image_refs before after same image heap)
  case completedBound image cleanupComplete own view captured fuel delay n error exit count heap =>
    exact .completedBound image cleanupComplete own view captured fuel delay n error exit count
      (image_refs before after same image heap)
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe constructors [HostTimeoutNumberFlow.CodeAt])
      (add safe apply [image_refs, value_refs, cause_refs, phase_refs])

/-- A reference-preserving edit retains current code and transports the saved callbacks to its future store. -/
theorem frame_refs (view : View) (before after : Stores) (same : before.refs = after.refs)
    (future : Future before after) (output : HostTimeoutNumberFlow.Kind)
    (frame : HostTimeoutFrames.NativeFrame)
    (owned : AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp before output frame) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp after output frame := by
  obtain ⟨input, code, stack⟩ := owned
  exact ⟨input, code_refs before after same input frame.current code,
    AnswerFlow.stack_mono (model view) (interpreter view).toPrimInterp future stack⟩

/-- A timer edit retains the actual numeric root prefix above the same source-handler suffix. -/
theorem region_refs (view : View) (before after : Stores) (same : before.refs = after.refs)
    (future : Future before after) (image : Image) (own : image.count = image.cleanups.length + 1)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (owned : RootRegionAt view before image own frame suffix) :
    RootRegionAt view after image own frame suffix := by
  obtain ⟨above, shape, typed⟩ := owned
  exact ⟨above, shape, frame_refs view before after same future (.retryResult image own) _ typed⟩

end Test.Dogfood.Proofs.HostTimeoutNumberStable
