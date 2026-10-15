import Test.Dogfood.Proofs.QueueWorkersNotificationCallbacks
import Effect4.Laws.Program.CodeClosure.Arms

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through its request-filtered notification code class.
The shared predicate family supplies current heads and saved-frame closure.
The same source graph seeds detached helpers at an ordinary class.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.QueueWorkersNotificationFlow
open Effect4 Effect4.Machine Effect4.Program

/-- The actual suspension view refresh preserves all immutable source slots. -/
theorem interp_suspended {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (view : List (FiberId × ExitV)) (table : RowTable) (thunk : EffThunk)
    (owned : ThunkAt spec bindings thunk) : Code spec bindings ((interpAt root view table).suspendBody thunk) := by
  cases thunk
  case body point => exact suspended spec fragment bindings (.body {point with completed := view}) (point_view spec bindings point owned view)
  all_goals exact suspended spec fragment bindings _ owned

/-- The actual loop entry reads only its source point and the current cursor. -/
theorem interp_loop_enter {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (view : List (FiberId × ExitV)) (table : RowTable) (name : EffName) (cursor : Val)
    (owned : LoopName spec bindings name) :
    LoopResult (Code spec bindings) ((interpAt root view table).loopEnter name cursor) := by
  cases name
  case loop point => exact loop_next spec bindings _ cursor (point_view spec bindings point owned view)
  all_goals exact owned.elim

/-- The saved loop consumes the actual returned cursor at the refreshed source view. -/
theorem interp_loop_resume {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (view : List (FiberId × ExitV)) (table : RowTable) (name : EffName) (cursor answer : Val)
    (owned : LoopName spec bindings name) :
    LoopResult (Code spec bindings) ((interpAt root view table).loopResume name cursor answer) := by
  cases name
  case loop point => exact loop_resume spec bindings _ cursor answer (point_view spec bindings point owned view)
  all_goals exact owned.elim

/-- Only actual source success callbacks and loop hooks can answer in the notification graph. -/
theorem arm_rules {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (view : List (FiberId × ExitV)) (table : RowTable) :
    CodeClosure.Arms.Rules (Code spec bindings) (interpAt root view table).toPrimInterp where
  success _ := trivial
  failure _ := trivial
  value _ name value owned := callback_value spec bindings view table name value owned.2
  constant _ _ owned := owned.2
  bothValue _ _ _ _ owned := owned.elim
  cause _ _ _ owned := owned.elim
  bothCause _ _ _ _ owned := owned.elim
  cancel _ _ owned := owned.elim
  iterator _ _ _ owned := owned.elim
  loop := by
    intro name cursor answer owned
    have closed := interp_loop_resume spec bindings view table name cursor answer owned
    cases actual : (interpAt root view table).loopResume name cursor answer with
    | «continue» next body =>
      rw [actual] at closed
      exact ⟨closed, owned⟩
    | finish body =>
      rw [actual] at closed
      exact closed

/-- The shared constructor-aware family handles every current and saved notification frame. -/
theorem rules {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) :
    CodeClosure.PredicateFamily.Rules root table (Code spec bindings) where
  success _ := trivial
  failure _ := trivial
  children := by
    intro code owned
    cases code
    all_goals aesop (add norm simp [CodeClosure.PredicateFamily.Children, Code, algebra,
      CodeClosure.roleAlg, cata_prim])
  mask _ := trivial
  suspend := by
    intro view thunk owned
    rcases owned with owned | owned
    · exact interp_suspended spec fragment bindings view table thunk owned
    · exact interp_suspended spec fragment bindings view table thunk owned
  value := fun view => CodeClosure.Arms.value _ _ (arm_rules spec bindings view table)
  cause := by
    intro view frame cause provided next pushed owned actual
    have present := Prim.armE_isSome (interpAt root view table).toPrimInterp frame cause provided
    rw [actual, no_cause_arm spec bindings frame owned] at present
    cases present
  loopContinue := by
    intro view name cursor next body owned actual
    have closed := interp_loop_enter spec bindings view table name cursor owned
    rw [actual] at closed
    exact ⟨closed, owned⟩
  loopFinish := by
    intro view name cursor body owned actual
    have closed := interp_loop_enter spec bindings view table name cursor owned
    rw [actual] at closed
    exact closed
  finalizer := by
    intro view frame exit next owned actual
    cases frame
    all_goals aesop (add norm simp [Code, algebra, CodeClosure.roleAlg, cata_prim])

/-- Actual notification callbacks consume the one generic current-head and saved-family producer. -/
def stable_laws {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) :=
  CodeClosure.PredicateFamily.laws root table (Code spec bindings) (rules spec fragment bindings table)

end Test.Dogfood.Proofs.QueueWorkersNotificationFlow
