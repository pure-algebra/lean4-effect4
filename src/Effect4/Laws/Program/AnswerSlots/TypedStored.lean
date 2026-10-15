import Effect4.Laws.Program.AnswerSlots.TypedAcquisition

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stored wrappers retain the protected acquisition capture they expose.
Reach: actual stored programs, finalizers and callback interpretation.
Limit: source callback and machine history closure remain separate producers.
Consumer: the protected stable saved family and native evaluation.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Interpreting a stored finalizer retains its certified foreign capture. -/
theorem finProgram_at (spec : Spec) (fin : FinName) (exit : ExitV)
    (owned : FinAt spec fin) : CodeAt spec .root (embed (finProgram fin exit)) := by
  revert owned
  fun_cases finProgram fin exit
  all_goals intro owned
  all_goals aesop (add norm simp [ValueAt, CodeAt, embed, ThunkAt, StoreThunkAt, StoreActionAt,
    OpAt, NameAt, OrdinaryName, ProtectedName, StoreNameAt, FinAt,
    AnswerSlots.CodeAt, AnswerSlots.ThunkAt, AnswerSlots.StoreThunkAt, AnswerSlots.StoreActionAt,
    AnswerSlots.NameAt, AnswerSlots.StoreNameAt, AnswerSlots.FinAt, AnswerSlots.OpAt,
    SourceScope.CodeAt, SourceScope.ThunkAt, SourceScope.StoreThunkAt, SourceScope.StoreActionAt,
    SourceScope.NameAt, SourceScope.StoreNameAt, SourceScope.FinAt, SourceScope.OpAt, CapturedPoint])

/-- Stored program interpretation retains its source, prefix and acquired-capture annotations. -/
theorem progOf_at (spec : Spec) (name : ProgName)
    (lexical : SourceScope.ProgAt spec.root name)
    (leading : AnswerSlots.ProgAt spec.bindings name) (owned : ProgAt spec name) :
    CodeAt spec .root (embed (progOf name)) := by
  revert lexical leading owned
  fun_induction progOf name
  all_goals intro lexical leading owned
  all_goals aesop (add norm simp [ValueAt, SourceScope.StrategyAt, ProgAt, CodeAt, embed, ThunkAt, StoreThunkAt,
    StoreActionAt, NameAt, OrdinaryName, ProtectedName, StoreNameAt,
    AnswerSlots.ProgAt, AnswerSlots.CodeAt, AnswerSlots.ThunkAt, AnswerSlots.StoreThunkAt,
    AnswerSlots.StoreActionAt, AnswerSlots.NameAt, AnswerSlots.StoreNameAt,
    SourceScope.ProgAt, SourceScope.CodeAt, SourceScope.ThunkAt, SourceScope.StoreThunkAt,
    SourceScope.StoreActionAt, SourceScope.NameAt, SourceScope.StoreNameAt]) (add safe apply [finProgram_at])

/-- Stored value callbacks retain their protected delayed programs. -/
theorem store_contA_at (spec : Spec) (name : Name) (value : Val)
    (lexical : SourceScope.StoreNameAt spec.root name)
    (leading : AnswerSlots.StoreNameAt spec.bindings name) (owned : StoreNameAt spec name) :
    CodeAt spec .root (embed (Effect4.Machine.contAOf name value)) := by
  revert lexical leading owned
  fun_cases Effect4.Machine.contAOf name value
  all_goals intro lexical leading owned
  all_goals aesop (add norm simp [ValueAt, StoreNameAt, CodeAt, embed, ThunkAt, StoreThunkAt,
    StoreActionAt, OpAt, NameAt, OrdinaryName, ProtectedName, FinAt,
    SourceScope.StoreNameAt, SourceScope.CodeAt, SourceScope.ThunkAt, SourceScope.StoreThunkAt,
    SourceScope.StoreActionAt, SourceScope.OpAt, SourceScope.NameAt,
    AnswerSlots.StoreNameAt, AnswerSlots.CodeAt, AnswerSlots.ThunkAt, AnswerSlots.StoreThunkAt,
    AnswerSlots.StoreActionAt, AnswerSlots.OpAt, AnswerSlots.NameAt, AnswerSlots.FinAt, SourceScope.FinAt, Prim.ofExit]) (add safe apply [progOf_at])
end Effect4.Program.AnswerSlots.Typed
