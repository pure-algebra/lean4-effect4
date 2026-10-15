import Effect4.Laws.Program.AnswerSlots.Callbacks
import Effect4.Laws.Program.CodeClosure.Interp

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

/-- The iterator reading uses the same generated code fold in its residual branch. -/
theorem iterAt_fold (bindings : List Val) (result : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode) :
    IterAt bindings result ↔ CodeClosure.Slots.IterAt (fun p => Prefix bindings p.env) (Prefix bindings) result := by
  cases result with
  | done value => rfl
  | halt cause => rfl
  | resume body name =>
    change (CodeAt bindings body ∧ NameAt bindings name) ↔
      (CodeClosure.Slots.CodeAt (fun p => Prefix bindings p.env) (Prefix bindings) body ∧ NameAt bindings name)
    rw [codeAt_fold]
    rfl

/-- A stored sequential close iterator retains its remaining finalizer captures. -/
theorem closeSeq_at (bindings : List Val) (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val)
    (owned : ∀ fin ∈ remaining, FinAt bindings fin) :
    IterAt bindings (embedStep (closeSeqStep remaining exit captured value)) := by
  rw [iterAt_fold]
  exact CodeClosure.Slots.closeSeq_at (fun p => Prefix bindings p.env) (Prefix bindings) remaining exit captured value owned

/-- A stored iterator only advances the captures retained by its existing name. -/
theorem store_iter_at (bindings : List Val) (name : Name) (value : Val)
    (owned : StoreNameAt bindings name) : IterAt bindings (embedStep ((stores.iterNext name value).2)) := by
  rw [iterAt_fold]
  exact CodeClosure.Slots.store_iter_at (fun p => Prefix bindings p.env) (Prefix bindings) name value owned

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
  rw [iterAt_fold]
  exact CodeClosure.Slots.interp_iter_at root (fun p => Prefix bindings p.env) (Prefix bindings)
    completed table name value owned

/-- A native loop entry retains the body at its next cursor. -/
theorem interp_loopEnter_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor : Val) (owned : NameAt bindings name) :
    LoopAt bindings ((interpAt root completed table).loopEnter name cursor) := by
  rw [loopAt_fold]
  exact CodeClosure.Slots.interp_loopEnter_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table name cursor owned

/-- A native loop resumption retains the body at its updated cursor. -/
theorem interp_loopResume_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (cursor answer : Val) (owned : NameAt bindings name) :
    LoopAt bindings ((interpAt root completed table).loopResume name cursor answer) := by
  rw [loopAt_fold]
  exact CodeClosure.Slots.interp_loopResume_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table name cursor answer owned

/-- Cancelling an asynchronous registration introduces no source writer. -/
theorem cancel_at (bindings : List Val) (name : EffName) : CodeAt bindings (cancelProgramOf name) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.cancel_at (fun p => Prefix bindings p.env) (Prefix bindings) name

/-- Native asynchronous cancellation retains the represented cleanup program. -/
theorem interp_cancel_at (root : NativeEff) (bindings : List Val) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) :
    CodeAt bindings ((interpAt root completed table).cancelThenFail name cause) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.interp_cancel_at root (fun p => Prefix bindings p.env) (Prefix bindings)
    completed table name cause

/-- A registered source finalizer retains the release child at its actual exit invocation. -/
theorem interp_fin_at (root : NativeEff) (bindings : List Val) (fragment : SourceScope.Fragment root) (completed) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (owned : NameAt bindings name)
    (found : (interpAt root completed table).finalizerProgram name exit = some body) :
    CodeAt bindings body := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.interp_fin_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) completed table name exit body owned found

end Effect4.Program.AnswerSlots
