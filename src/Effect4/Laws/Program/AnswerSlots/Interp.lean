import Effect4.Laws.Program.AnswerSlots.Callbacks

/-!
# Native interpreter source scope

Concept: store-typing R4, serving the Workers and QueueWorkers cleanup log claims.
The interpreter retains lexical scope under its current completed-exit view.
The laws cover saved iterator, loop, cause and finalizer callbacks.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- An iterator retains its next source program and saved continuation. -/
def IterAt (bindings : List Val) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => CodeAt bindings body ∧ NameAt bindings next
  | _ => True

/-- A stored sequential close iterator retains its remaining finalizer captures. -/
theorem closeSeq_at (bindings : List Val) (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val)
    (owned : ∀ fin ∈ remaining, FinAt bindings fin) :
    IterAt bindings (embedStep (closeSeqStep remaining exit captured value)) := by
  cases remaining with
  | nil =>
    change IterAt bindings (embedStep (closeDone (captured ++ reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  | cons fin rest =>
    exact ⟨finProgram_at bindings fin exit (owned fin (.head _)),
      fun next member => owned next (.tail _ member)⟩

/-- A stored iterator only advances the captures retained by its existing name. -/
theorem store_iter_at (bindings : List Val) (name : Name) (value : Val)
    (owned : StoreNameAt bindings name) : IterAt bindings (embedStep ((stores.iterNext name value).2)) := by
  cases name
  case closeSeq remaining exit captured => exact closeSeq_at bindings remaining exit captured value owned
  case closeParDone =>
    change IterAt bindings (embedStep (closeDone (reasonsOfVal value)))
    unfold closeDone
    split <;> trivial
  all_goals trivial

/-- Current completed exits change no callback source path or lexical length. -/
theorem interp_contA_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt bindings name) :
    CodeAt bindings ((interpAt root completed table).contA name value) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.interp_contA_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table name value owned

/-- Current completed exits change no cause callback source path or lexical length. -/
theorem interp_contE_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) (owned : NameAt bindings name) :
    CodeAt bindings ((interpAt root completed table).contE name cause) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.interp_contE_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table name cause owned

/-- Current completed exits change no suspended source path or lexical length. -/
theorem interp_suspend_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (thunk : EffThunk) (owned : ThunkAt bindings thunk) :
    CodeAt bindings ((interpAt root completed table).suspendBody thunk) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.interp_suspend_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table thunk owned

/-- Invoking a saved iterator retains its body and next name. -/
theorem interp_iter_at (root : NativeEff) (bindings : List Val) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt bindings name) :
    IterAt bindings (((interpAt root completed table).iterNext name value).2) := by
  cases name
  case gen p pc bind => exact owned.elim
  case store name => exact store_iter_at bindings name value owned
  all_goals trivial

/-- A native loop entry retains the body at its next cursor. -/
theorem interp_loopEnter_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor : Val) (owned : NameAt bindings name) :
    LoopAt bindings ((interpAt root completed table).loopEnter name cursor) := by
  cases name
  case loop p => exact loopNext_at root fragment bindings _ cursor owned
  all_goals trivial

/-- A native loop resumption retains the body at its updated cursor. -/
theorem interp_loopResume_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor answer : Val) (owned : NameAt bindings name) :
    LoopAt bindings ((interpAt root completed table).loopResume name cursor answer) := by
  cases name
  case loop p => exact loopResume_at root fragment bindings _ cursor answer owned
  all_goals trivial

/-- Cancelling an asynchronous registration introduces no source writer. -/
theorem cancel_at (bindings : List Val) (name : EffName) : CodeAt bindings (cancelProgramOf name) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.cancel_at (fun p => Prefix bindings p.env) (Prefix bindings) name

/-- Native asynchronous cancellation retains the represented cleanup program. -/
theorem interp_cancel_at (root : NativeEff) (bindings : List Val) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) :
    CodeAt bindings ((interpAt root completed table).cancelThenFail name cause) :=
  by
    exact ⟨cancel_at bindings name, trivial⟩

/-- A registered source finalizer retains the release child at its actual exit invocation. -/
theorem interp_fin_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (owned : NameAt bindings name)
    (found : (interpAt root completed table).finalizerProgram name exit = some body) :
    CodeAt bindings body := by
  cases name
  case fin p =>
    cases found
    exact resolve_arg_at root fragment bindings _ 1 (reifyExitVal exit) owned
  case store name =>
    cases name
    case finalizerName fin =>
      cases found
      exact finProgram_at bindings fin exit owned
    all_goals cases found
  -- the two names whose finalizer is a fiber action; every other name has none
  case scopeClose scope => cases found; trivial
  case restoreCtx previous => cases found; trivial
  all_goals cases found

end Effect4.Program.AnswerSlots
