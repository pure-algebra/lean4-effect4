import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: scheduler injection retains an unfinished numeric writer without assuming its future successful value.
Consumer: the actual injected iteration branch of both Timeout numeric history endpoints.
Reach: the same reference heap across a scheduler pause and the original incoming cause class.
Limit: this assertion transport establishes no writer or command history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPause
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow HostTimeoutNumberPhase

/-- Numeric value assertions read the unchanged existing reference heap. -/
theorem value_refs (before after : Stores) (same : after.refs = before.refs) (kind : Kind) (value : Val)
    (good : ValueAt before kind value) : ValueAt after kind value := by
  cases kind <;> simpa only [ValueAt, At, same] using good

/-- Numeric causes read the same reference heap, including the original cause class behind a pause. -/
theorem cause_refs (before after : Stores) (same : after.refs = before.refs) (kind : Kind) (cause : CauseV)
    (good : CauseAt before kind cause) : CauseAt after kind cause := by
  induction kind with
  | paused phase incoming ih => exact ih good
  | read phase => exact False.elim good
  | unit phase => exact False.elim good
  | _ => all_goals simpa only [CauseAt, At, same] using good

/-- The existing numeric code assertion transports across an unchanged heap and its admitted future metadata.
Consumer: the saved scheduler pause callback below; this induction follows proof assertions, not program syntax. -/
theorem code_refs (before : Stores) (kind : Kind) (program : NCode)
    (owned : CodeAt before kind program) :
    ∀ after, HostTimeoutNumberFlow.Future before after → after.refs = before.refs → CodeAt after kind program := by
  induction owned with
  | success kind value good =>
    intro after future same
    exact .success kind value (value_refs _ _ same _ _ good)
  | failure kind cause good =>
    intro after future same
    exact .failure kind cause (cause_refs _ _ same _ _ good)
  | bind input output first name head ordered region owner valid callback skip ih =>
    intro after future same
    apply CodeAt.bind input output first name (ih after future same) ordered region owner valid
    · intro next later value good view
      exact callback next ((model view).future_trans _ _ _ future later) value good view
    · intro next later cause good
      exact skip next ((model []).future_trans _ _ _ future later) cause good
  | constant input output first body head ordered region owner valid callback skip ih =>
    intro after future same
    apply CodeAt.constant input output first body (ih after future same) ordered region owner valid
    · intro next later value good
      exact callback next ((model []).future_trans _ _ _ future later) value good
    · intro next later cause good
      exact skip next ((model []).future_trans _ _ _ future later) cause good
  | get phase heap =>
    intro after future same
    exact .get phase (same.trans heap)
  | form phase captured fuel delay n previous selected heap =>
    intro after future same
    exact .form phase captured fuel delay n previous selected (same.trans heap)
  | write phase view captured fuel delay n previous selected heap =>
    intro after future same
    exact .write phase view captured fuel delay n previous selected (same.trans heap)
  | cleanup phase own captured fuel delay n previous selected heap =>
    intro after future same
    exact .cleanup phase own captured fuel delay n previous selected (same.trans heap)
  | cleanupBound phase own view captured fuel delay n previous selected heap =>
    intro after future same
    exact .cleanupBound phase own view captured fuel delay n previous selected (same.trans heap)
  | cleanupWrite phase own view captured fuel delay n previous selected heap =>
    intro after future same
    exact .cleanupWrite phase own view captured fuel delay n previous selected (same.trans heap)
  | cleanupReturn phase own selected body first ih =>
    intro after future same
    exact .cleanupReturn phase own selected body (ih after future same)
  | park phase parkKind heap =>
    intro after future same
    exact .park phase parkKind (same.trans heap)
  | cancelRace phase race heap =>
    intro after future same
    exact .cancelRace phase race (same.trans heap)
  | maskedCancelRace phase race heap =>
    intro after future same
    exact .maskedCancelRace phase race (same.trans heap)
  | pausing phase kind priority body heap first ih =>
    intro after future same
    exact .pausing phase kind priority body (same.trans heap) (ih after future same)
  | yieldNow kind priority good =>
    intro after future same
    exact .yieldNow kind priority (value_refs _ _ same _ _ good)
  | attemptReturn before entered own selected body first ih =>
    intro after future same
    exact .attemptReturn before entered own selected body (ih after future same)
  | attemptEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    intro after future same
    exact .attemptEntry phase n cleanups forms cursor captured fuel delay previous (same.trans heap)
  | attemptBody phase captured fuel delay n previous heap =>
    intro after future same
    exact .attemptBody phase captured fuel delay n previous (same.trans heap)
  | count phase n cleanups forms cursor captured fuel delay previous heap =>
    intro after future same
    exact .count phase n cleanups forms cursor captured fuel delay previous (same.trans heap)
  | countBind phase n cleanups forms cursor captured fuel delay previous heap =>
    intro after future same
    exact .countBind phase n cleanups forms cursor captured fuel delay previous (same.trans heap)
  | countEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    intro after future same
    exact .countEntry phase n cleanups forms cursor captured fuel delay previous (same.trans heap)
  | merge phase exit body first ih =>
    intro after future same
    exact .merge phase exit body (ih after future same)
  | restore phase selected body first ih =>
    intro after future same
    exact .restore phase selected body (ih after future same)

/-- A scheduler pause freezes its actual heap and resumes the original writer with its original cause class. -/
theorem saved (view : HostTimeoutFlow.View) (state : Stores) (phase : Phase) (kind : Kind)
    (priority : Nat) (body : NCode) (heap : At phase state) (owned : CodeAt state kind body) :
    AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state
      (.paused phase kind) kind (.onSuccessConst (.yieldNowWith priority) body) := by
  apply AnswerFlow.saved_constant
  · intro next future value good
    exact code_refs state kind body owned next future (good.trans heap.symm)
  · intro next future cause good
    exact good

end Test.Dogfood.Proofs.HostTimeoutNumberPause
