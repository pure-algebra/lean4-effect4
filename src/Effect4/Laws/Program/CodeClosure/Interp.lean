import Effect4.Laws.Program.CodeClosure.Callbacks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native callback frames retain their supplied source annotations.
Consumer: the shared stable saved family and Timeout's pending source assertion.
Reach: actual completed-exit views within the existing direct source fragment.
Limit: initialization, numeric effects, and command histories remain separate obligations.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

/-- A stored iterator retains each residual source-bearing field. -/
def IterAt (point : Point → Prop) (env : List Val → Prop) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => CodeAt point env body ∧ NameAt point env next
  | _ => True

/-- Sequential close retains the annotations of its remaining captured finalizers. -/
theorem closeSeq_at (point : Point → Prop) (env : List Val → Prop) (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val)
    (owned : ∀ fin ∈ remaining, FinAt point env fin) :
    IterAt point env (embedStep (closeSeqStep remaining exit captured value)) := by
  cases remaining with
  | nil =>
    change IterAt point env (embedStep (closeDone (captured ++ reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  | cons fin rest =>
    exact ⟨finProgram_at point env fin exit (owned fin (.head _)),
      fun next member => owned next (.tail _ member)⟩

/-- Stored iterator callbacks advance the captures retained by their actual names. -/
theorem store_iter_at (point : Point → Prop) (env : List Val → Prop) (name : Name) (value : Val)
    (owned : StoreNameAt point env name) :
    IterAt point env (embedStep ((stores.iterNext name value).2)) := by
  cases name
  case closeSeq remaining exit captured => exact closeSeq_at point env remaining exit captured value owned
  case closeParDone =>
    change IterAt point env (embedStep (closeDone (reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  all_goals trivial

/-- Actual iterator invocation retains its body and saved continuation annotation. -/
theorem interp_iter_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (completed) (table : RowTable) (name : EffName) (value : Val) (owned : NameAt point env name) :
    IterAt point env (((interpAt root completed table).iterNext name value).2) := by
  cases name
  case gen p pc bind => exact owned.elim
  case store name => exact store_iter_at point env name value owned
  all_goals trivial

/-- Actual loop entry retains its source annotation under the current completed-exit view. -/
theorem interp_loopEnter_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (cursor : Val) (owned : NameAt point env name) :
    LoopAt point env ((interpAt root completed table).loopEnter name cursor) := by
  cases name
  case loop p => exact loopNext_at root fragment point env contract _ cursor (stable p owned completed)
  all_goals trivial

/-- Actual loop resumption retains its source annotation at the updated cursor. -/
theorem interp_loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (cursor answer : Val) (owned : NameAt point env name) :
    LoopAt point env ((interpAt root completed table).loopResume name cursor answer) := by
  cases name
  case loop p => exact loopResume_at root fragment point env contract _ cursor answer (stable p owned completed)
  all_goals trivial

/-- Actual asynchronous cancellation retains its cleanup code before restoring failure. -/
theorem interp_cancel_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (completed) (table : RowTable) (name : EffName) (cause : CauseV) :
    CodeAt point env ((interpAt root completed table).cancelThenFail name cause) :=
  ⟨cancel_at point env name, trivial⟩

/-- Actual finalizer invocation resolves the captured source child under its current exit view. -/
theorem interp_fin_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (owned : NameAt point env name)
    (found : (interpAt root completed table).finalizerProgram name exit = some body) : CodeAt point env body := by
  cases name
  case fin p =>
    cases found
    exact resolve_arg_at root fragment point env contract _ 1 (reifyExitVal exit) (stable p owned completed)
  case store name =>
    cases name
    case finalizerName fin =>
      cases found
      exact finProgram_at point env fin exit owned
    all_goals cases found
  case scopeClose scope => cases found; trivial
  case restoreCtx previous => cases found; trivial
  all_goals cases found

end Effect4.Program.CodeClosure.Slots
