import Effect4.Laws.Program.NativeCallbacks

/-!
# Native interpreter source scope

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The interpreter retains lexical scope under its current completed-exit view.
The laws cover saved iterator, loop, cause and finalizer callbacks.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- An iterator retains its next source program and saved continuation. -/
def IterAt (root : NativeEff) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => CodeAt root body ∧ NameAt root next
  | _ => True

/-- A stored sequential close iterator retains its remaining finalizer captures. -/
theorem closeSeq_at (root : NativeEff) (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val)
    (owned : ∀ fin ∈ remaining, FinAt root fin) :
    IterAt root (embedStep (closeSeqStep remaining exit captured value)) := by
  cases remaining with
  | nil =>
    change IterAt root (embedStep (closeDone (captured ++ reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  | cons fin rest =>
    exact ⟨finProgram_at root fin exit (owned fin (.head _)),
      fun next member => owned next (.tail _ member)⟩

/-- A stored iterator only advances the captures retained by its existing name. -/
theorem store_iter_at (root : NativeEff) (name : Name) (value : Val)
    (owned : StoreNameAt root name) : IterAt root (embedStep ((stores.iterNext name value).2)) := by
  cases name
  case closeSeq remaining exit captured => exact closeSeq_at root remaining exit captured value owned
  case closeParDone =>
    change IterAt root (embedStep (closeDone (reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  all_goals trivial

/-- Current completed exits change no callback source path or lexical length. -/
theorem interp_contA_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt root name) :
    CodeAt root ((interpAt root completed table).contA name value) := by
  apply contA_at root fragment
  cases name <;> exact owned

/-- Current completed exits change no cause callback source path or lexical length. -/
theorem interp_contE_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) (owned : NameAt root name) :
    CodeAt root ((interpAt root completed table).contE name cause) := by
  apply contE_at root fragment
  cases name <;> exact owned

/-- Current completed exits change no suspended source path or lexical length. -/
theorem interp_suspend_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (thunk : EffThunk) (owned : ThunkAt root thunk) :
    CodeAt root ((interpAt root completed table).suspendBody thunk) := by
  apply suspend_at root fragment
  cases thunk <;> exact owned

/-- Invoking a saved iterator retains its body and next name. -/
theorem interp_iter_at (root : NativeEff) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt root name) :
    IterAt root (((interpAt root completed table).iterNext name value).2) := by
  cases name
  case gen p pc bind => exact owned.elim
  case store name => exact store_iter_at root name value owned
  all_goals trivial

/-- A native loop entry retains the body at its next cursor. -/
theorem interp_loopEnter_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor : Val) (owned : NameAt root name) :
    LoopAt root ((interpAt root completed table).loopEnter name cursor) := by
  cases name
  case loop p => exact loopNext_at root fragment _ cursor owned
  all_goals trivial

/-- A native loop resumption retains the body at its updated cursor. -/
theorem interp_loopResume_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor answer : Val) (owned : NameAt root name) :
    LoopAt root ((interpAt root completed table).loopResume name cursor answer) := by
  cases name
  case loop p => exact loopResume_at root fragment _ cursor answer owned
  all_goals trivial

/-- Cancelling an asynchronous registration introduces no source writer. -/
theorem cancel_at (root : NativeEff) (name : EffName) : CodeAt root (cancelProgramOf name) := by
  fun_cases cancelProgramOf name
  all_goals aesop (add norm simp [CodeAt, ThunkAt, OpAt, store_cancel_at])

/-- Native asynchronous cancellation retains the represented cleanup program. -/
theorem interp_cancel_at (root : NativeEff) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) :
    CodeAt root ((interpAt root completed table).cancelThenFail name cause) :=
  by
    refine ⟨cancel_at root name, trivial, ?_⟩
    intro _ _ wrong
    cases wrong

/-- A registered source finalizer retains the release child at its actual exit invocation. -/
theorem interp_fin_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (owned : NameAt root name)
    (found : (interpAt root completed table).finalizerProgram name exit = some body) :
    CodeAt root body := by
  cases name
  case fin p =>
    cases found
    exact resolve_arg_at root fragment _ 1 (reifyExitVal exit) owned.1
  case store name =>
    cases name
    case finalizerName fin =>
      cases found
      exact finProgram_at root fin exit owned
    all_goals cases found
  -- the two names whose finalizer is a fiber action; every other name has none
  case scopeClose scope => cases found; trivial
  case restoreCtx previous => cases found; trivial
  all_goals cases found

end Effect4.Program.SourceScope
