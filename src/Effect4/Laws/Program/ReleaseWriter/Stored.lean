import Effect4.Laws.Program.ReleaseWriter.Source

/-!
Concept: scope-lifetime-finalization R11.
Question: delayed wrappers retain the reservation consumed by Workers.Assertions.logs_step.
Reach: actual stored programs, continuations and cancellation code.
Consumer: the writer's frame and native evaluator debit.
This arithmetic establishes no acquired target or store predicate.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter.Stored
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseWriter

/-- Interpreting an existing stored program transfers its selected writes unchanged. -/
theorem program_exact (target : Target) (body : ProgName) :
    current target (embed (progOf body)) = ReleaseWriter.program target body := by
  fun_induction progOf body
  all_goals aesop (add norm simp [ReleaseWriter.program, current, pair, cata_prim, thunk, successName, name, storeName, storeAction,
    StoredWeights.program, StoredWeights.name, StoredWeights.action, operation, embed, finProgram]) (add safe cases [FinalizerStrategy])

/-- Stored value callbacks spend only their own retained reservation. -/
theorem value_bound (target : Target) (callback : Name) (value : Val) :
    current target (embed (Machine.contAOf callback value)) ≤ storeName target callback := by
  have folded (body : ProgName) :
      (cata_prim (PrimWeights.pairedAlgebra (weights target) (savedSuccess target))
        (embed (progOf body))).1 = ReleaseWriter.program target body := program_exact target body
  fun_cases Machine.contAOf callback value
  all_goals aesop (add norm simp [folded, current, pair, cata_prim, thunk, successName, name, storeName,
    storeAction, StoredWeights.name, StoredWeights.action, operation, embed, Prim.ofExit])

/-- Stored failure callbacks introduce no pending selected write. -/
theorem cause_zero (target : Target) (callback : Name) (cause : CauseV) :
    current target (embed (Machine.contEOf callback cause)) = 0 := by
  fun_cases Machine.contEOf callback cause
  all_goals aesop (add norm simp [current, pair, cata_prim, name, embed, Prim.ofExit])

/-- Cancellation code has no selected reference update. -/
theorem cancel_zero (target : Target) (callback : Name) :
    current target (embed (cancelProgram callback)) = 0 := by
  fun_cases cancelProgram callback
  all_goals rfl

end Effect4.Program.ReleaseWriter.Stored
