import Effect4.Laws.Program.AnswerSlots.Syntax
import Effect4.Laws.Program.CodeClosure.Stored

/-!
# Source scope through stored program interpretation

Concept: store-typing R4, serving the Workers and QueueWorkers cleanup log claims.
The laws interpret the existing synthetic program and finalizer names.
They retain foreign captures through every wrapper, without treating stored syntax as opaque.
The native history bridge consumes these laws for saved callbacks and finalizer execution.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- A named finalizer exposes only the captured release address it owns. -/
theorem finProgram_at (bindings : List Val) (fin : FinName) (exit : ExitV)
    (owned : FinAt bindings fin) : CodeAt bindings (embed (finProgram fin exit)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.finProgram_at (fun p => Prefix bindings p.env) (Prefix bindings) fin exit owned

/-- Interpreting a stored program retains every delayed source-bearing slot it owns. -/
theorem progOf_at (bindings : List Val) (name : ProgName) (owned : ProgAt bindings name) :
    CodeAt bindings (embed (progOf name)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.progOf_at (fun p => Prefix bindings p.env) (Prefix bindings) name owned

/-- Stored value callbacks retain their delayed program scopes. -/
theorem store_contA_at (bindings : List Val) (name : Name) (value : Val)
    (owned : StoreNameAt bindings name) : CodeAt bindings (embed (Effect4.Machine.contAOf name value)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.store_contA_at (fun p => Prefix bindings p.env) (Prefix bindings) name value owned

/-- Stored cause callbacks produce exits without adding a source-bearing residual. -/
theorem store_contE_at (bindings : List Val) (name : Name) (cause : CauseV) :
    CodeAt bindings (embed (Effect4.Machine.contEOf name cause)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.store_contE_at (fun p => Prefix bindings p.env) (Prefix bindings) name cause

/-- Stored cancel callbacks only expose administrative programs. -/
theorem store_cancel_at (bindings : List Val) (name : Name) :
    CodeAt bindings (embed (cancelProgram name)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.store_cancel_at (fun p => Prefix bindings p.env) (Prefix bindings) name

/-- A stored completion exposes only an exit or a reference read. -/
theorem completion_at (bindings : List Val) (completion : Completion Val Err Defect FiberId Ann) :
    CodeAt bindings (embed (completionPrim completion)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.completion_at (fun p => Prefix bindings p.env) (Prefix bindings) completion

end Effect4.Program.AnswerSlots
