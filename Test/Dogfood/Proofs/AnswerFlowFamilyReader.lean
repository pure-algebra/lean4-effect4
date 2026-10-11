import Effect4.Laws.Machine.AnswerFlowFamily
import Effect4.Laws.Program.NativeFrameScope
import Test.Dogfood.Proofs.HostTimeoutNumberCounted

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: one external callback interface serves lexical and numeric native frame transport.
Reach: actual interpreter callbacks, actual state-indexed count binder, and the shared saved path.
Consumer: replacement of NativeFrameScope transport, then Timeout's reached numeric producer.
The instances supply no command preservation, source history, or progress premise.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.AnswerFlowFamilyReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- The actual Timeout source reads the shared lexical callback contract. -/
theorem timeout_callbacks (fragment : SourceScope.Fragment HostTimeoutSource.program)
    (completed : List (FiberId × Exit Val Err Defect FiberId Ann)) (table : RowTable) :
    AnswerFlow.SavedFamily (SourceScope.lexicalModel HostTimeoutSource.program)
      (interpAt HostTimeoutSource.program completed table).toPrimInterp
      (SourceScope.lexicalEdge HostTimeoutSource.program) :=
  SourceScope.lexical_family HostTimeoutSource.program fragment completed table

/-- The existing numeric count binder consumes its actual post-count image through the same family. -/
theorem numeric_count_answer (view : HostTimeoutFlow.View) (before after : Stores)
    (image : HostTimeoutNumberFlow.Image) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1)
    (future : HostTimeoutNumberFlow.Future before after)
    (value : Val) (next : NCode) (pushed : List NCode)
    (good : HostTimeoutNumberFlow.ValueAt after (.unit image) value)
    (arm :
      let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error
      (.onSuccess (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm point.env))) (.cont (point.child 0)) : NCode).armA
        (HostTimeoutFlow.interpreter view).toPrimInterp value none = some (next, pushed)) :
    AnswerFlow.FamilyResult (HostTimeoutNumberFlow.model view)
      (AnswerFlow.SavedAt (HostTimeoutNumberFlow.model view) (HostTimeoutFlow.interpreter view).toPrimInterp)
      after (.at image) next pushed := by
  let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error
  exact (AnswerFlow.saved_family (HostTimeoutNumberFlow.model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp).answer before (.unit image) (.at image) _
      (HostTimeoutNumberCounted.count_saved view before image captured fuel delay n error count)
      after future value none next pushed good (by intro exit member; cases member) rfl arm

/-- The real count binder admits no failure exit before the attempt body starts. -/
theorem count_failure_refuses (view : HostTimeoutFlow.View) (state : Stores)
    (image : HostTimeoutNumberFlow.Image) (cause : CauseV) :
    ¬ AnswerFlow.ExitAt (HostTimeoutNumberFlow.model view) state (.unit image) (.failure cause) := by
  intro invalid
  exact invalid

end Test.Dogfood.Proofs.AnswerFlowFamilyReader
