import Effect4.Laws.Program.NativeScope

/-!
# Source scope through stored program interpretation

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The laws interpret the existing synthetic program and finalizer names.
They retain foreign captures through every wrapper, without treating stored syntax as opaque.
The native history bridge consumes these laws for saved callbacks and finalizer execution.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- A named finalizer exposes only the captured release address it owns. -/
theorem finProgram_at (root : NativeEff) (fin : FinName) (exit : ExitV)
    (owned : FinAt root fin) : CodeAt root (embed (finProgram fin exit)) := by
  revert owned
  fun_cases finProgram fin exit
  all_goals intro owned
  all_goals aesop (add norm simp [CodeAt, embed, ThunkAt, StoreThunkAt, StoreActionAt,
    OpAt, NameAt, StoreNameAt, FinAt])

/-- Interpreting a stored program retains every delayed source-bearing slot it owns. -/
theorem progOf_at (root : NativeEff) (name : ProgName) (owned : ProgAt root name) :
    CodeAt root (embed (progOf name)) := by
  revert owned
  fun_induction progOf name
  all_goals intro owned
  all_goals aesop (add norm simp [ProgAt, CodeAt, embed, ThunkAt, StoreThunkAt,
    StoreActionAt, NameAt, StoreNameAt, StrategyAt]) (add safe apply [finProgram_at])

/-- Stored value callbacks retain their delayed program scopes. -/
theorem store_contA_at (root : NativeEff) (name : Name) (value : Val)
    (owned : StoreNameAt root name) : CodeAt root (embed (Effect4.Machine.contAOf name value)) := by
  revert owned
  fun_cases Effect4.Machine.contAOf name value
  all_goals intro owned
  all_goals aesop (add norm simp [progOf_at, StoreNameAt, CodeAt, embed, ThunkAt, StoreThunkAt,
    StoreActionAt, OpAt, NameAt, FinAt, Prim.ofExit])

/-- Stored cause callbacks produce exits without adding a source-bearing residual. -/
theorem store_contE_at (root : NativeEff) (name : Name) (cause : CauseV) :
    CodeAt root (embed (Effect4.Machine.contEOf name cause)) := by
  fun_cases Effect4.Machine.contEOf name cause
  all_goals aesop (add norm simp [CodeAt, embed, Prim.ofExit])

/-- Stored cancel callbacks only expose administrative programs. -/
theorem store_cancel_at (root : NativeEff) (name : Name) :
    CodeAt root (embed (cancelProgram name)) := by
  fun_cases cancelProgram name
  all_goals aesop (add norm simp [CodeAt, embed, ThunkAt, StoreThunkAt,
    StoreActionAt, OpAt])

/-- A stored completion exposes only an exit or a reference read. -/
theorem completion_at (root : NativeEff) (completion : Completion Val Err Defect FiberId Ann) :
    CodeAt root (embed (completionPrim completion)) := by
  cases completion with
  | ofExit exit =>
    cases exit <;> trivial
  | ofRefGet key => trivial

end Effect4.Program.SourceScope
