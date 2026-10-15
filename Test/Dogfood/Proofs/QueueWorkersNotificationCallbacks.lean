import Test.Dogfood.Proofs.QueueWorkersNotificationFlow
import Effect4.Laws.Program.CodeClosure.Suspension

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the notification instance of PredicateFamily.
Actual source callbacks reuse the single indexed compiler and source point transport.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.QueueWorkersNotificationFlow
open Effect4 Effect4.Machine Effect4.Program

/-- Refreshing completed exits changes neither the selected source region nor captured slots. -/
theorem point_view {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point)
    (owned : PointAt spec bindings point) (view : List (FiberId × ExitV)) :
    PointAt spec bindings {point with completed := view} := owned

/-- Actual child entry keeps every captured payload slot in the notification region. -/
theorem resolve_child {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point)
    (index : Nat) (owned : PointAt spec bindings point) : Code spec bindings (resolve root (point.child index)) :=
  resolve_at spec bindings _ ((QueueWorkersCustodySegments.transport spec.toSpec bindings).child owned index)

/-- Actual bound child entry appends only the value returned by the current binder. -/
theorem resolve_bound {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point)
    (index : Nat) (value : Val) (owned : PointAt spec bindings point) :
    Code spec bindings (resolve root (point.childWith index value)) :=
  resolve_at spec bindings _ ((QueueWorkersCustodySegments.transport spec.toSpec bindings).childWith owned index value)

/-- A source option decision preserves the actual optional binding chosen by its decision. -/
theorem resolve_selected {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point)
    (first : Bool) (bound : Option Val) (owned : PointAt spec bindings point) :
    Code spec bindings (resolve root (point.childBind (cond first 0 1) bound)) := by
  cases bound with
  | none => exact resolve_child spec bindings point _ owned
  | some value => exact resolve_bound spec bindings point _ value owned

/-- The actual unary success callback enters its existing source body with its actual answer. -/
theorem callback_value {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (view : List (FiberId × ExitV)) (table : RowTable) (name : EffName) (value : Val)
    (owned : SuccessName spec bindings name) :
    Code spec bindings ((interpAt root view table).contA name value) := by
  cases name
  case cont point => exact resolve_bound spec bindings _ 1 value (point_view spec bindings point owned view)
  all_goals exact owned.elim

/-- A loop's actual result expression returns a terminal code in the same source graph. -/
theorem loop_finish {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point) (cursor : Val) :
    Code spec bindings (loopFinishAt root point cursor) := by
  fun_cases loopFinishAt root point cursor
  all_goals trivial

/-- Both actual loop alternatives retain the same current-code annotation. -/
def LoopResult (P : NCode → Prop) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => P body

/-- A real loop decision returns its terminal code or its source body with the actual next cursor. -/
theorem loop_next {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point) (cursor : Val)
    (owned : PointAt spec bindings point) :
    LoopResult (Code spec bindings) (loopNextAt root point cursor) := by
  have body := resolve_bound spec bindings point 0 cursor owned
  have finished := loop_finish spec bindings point cursor
  have broken : Code spec bindings badShape := by trivial
  fun_cases loopNextAt root point cursor
  all_goals aesop (add norm simp [LoopResult]) (add safe apply [body, finished, broken])

/-- The actual saved loop uses its computed next cursor, retaining the same captured source region. -/
theorem loop_resume {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point)
    (cursor answer : Val) (owned : PointAt spec bindings point) :
    LoopResult (Code spec bindings) (loopResumeAt root point cursor answer) := by
  unfold loopResumeAt
  cases found : loopAt root point with
  | none => trivial
  | some row =>
    rcases row with ⟨test, step, body⟩
    simp only []
    cases evaluated : evalTerm (point.env ++ [cursor, answer]) step with
    | none => trivial
    | some next => exact loop_next spec bindings point next owned

/-- The source-body hook consumes the shared direct-fragment constructor contract. -/
theorem suspended {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (thunk : EffThunk) (owned : ThunkAt spec bindings thunk) :
    Code spec bindings (suspendBodyAt root thunk) := by
  cases thunk
  case body point =>
    exact CodeClosure.suspend_body_at root fragment (PointAt spec bindings) (Code spec bindings)
      { compiled := fun e point found owned => compile_at spec bindings e point found owned
        frontier := fun _ owned => owned
        child := fun point owned => resolve_child spec bindings point 0 owned
        selected := fun point first bound owned => resolve_selected spec bindings point first bound owned
        loop := fun _ _ owned => owned
        badShape := trivial } point owned
  case memoLookup => exact owned.elim
  case store stored =>
    cases stored
    case body => exact owned.elim
    case foreign => exact owned.elim
    all_goals trivial
  all_goals trivial

end Test.Dogfood.Proofs.QueueWorkersNotificationFlow
