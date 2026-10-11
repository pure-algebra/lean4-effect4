import Effect4.Laws.Machine.FinalizerEvaluation
import Effect4.Laws.Program.FinalizerMoves
import Effect4.Laws.Program.Guard.ForkLedger

/-!
# Native finalizer accounting through commands

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The consumer is `Program.FinalizerRun.funded_reachable`, then `Atomic.cleans_once`.
The proof lifts the frame debit through native scoped exits and the actual command loop.
Reach: arbitrary programs, row tables, decisions and command budgets.
Source-use uniqueness, log provenance, progress and host agreement remain separate.
-/

set_option autoImplicit false
namespace Effect4.Program.FinalizerTransfer
open Effect4 Effect4.Machine Effect4.Machine.FinalizerCredits
open Effect4.Machine.ForkLedger.Invariant
open Effect4.Program.Guard

/-- Native scoped exit spends its popped frame exactly when it starts the close program. -/
theorem exitScoped_debit (choose : EffName → Bool) (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (y : Bool) (exit : ExitV) (ok : Ok m) :
    IterDebit choose m f (exitScoped p m f y exit) := by
  have _ := ok
  exact (Moves.exitScoped_tracedFootprint p m f y exit).frame.finalizer choose

/-- The native scoped exit retains the table before the driver replaces its selected row. -/
theorem exitScoped_kept (choose : EffName → Bool) (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (y : Bool) (exit : ExitV) (ok : Ok m) :
    IterKept choose m f (exitScoped p m f y exit) := by
  have views : let next := exitScoped p m f y exit
      total choose next.machine = total choose m ∧
      (∀ id, atFiber choose next.machine id = atFiber choose m id) ∧ next.fiber.id = f.id := by
    unfold exitScoped
    dsimp only
    split
    · split
      · exact ⟨rfl, fun _ => rfl, rfl⟩
      · rename_i state program _
        cases program <;> exact ⟨rfl, fun _ => rfl, rfl⟩
    · have kept := evaluatePrim_kept choose (interpAt p m.completedExits) m ok.idsUnique f y
      exact ⟨kept.1, kept.2.1, kept.2.2.1⟩
  exact ⟨views.1, views.2.1, views.2.2, exitScoped_debit choose p m f y exit ok⟩

/-- Both native evaluator routes satisfy the same finalizer accounting relation. -/
theorem evaluate_kept (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (y : Bool) (ok : Ok m) :
    IterKept choose m f (evaluateNative p m f y table) := by
  unfold evaluateNative
  split
  · split
    · exact IterKept.of_same (.refl choose m) rfl rfl
    · exact evaluatePrim_kept choose _ m ok.idsUnique f y
  · exact exitScoped_kept choose p m f y _ ok
  · exact exitScoped_kept choose p m f y _ ok
  · exact evaluatePrim_kept choose _ m ok.idsUnique f y

/-- A neutral machine edit and caller edit rebase an evaluator's accounting relation. -/
theorem rebase {choose : EffName → Bool} {m n : NativeMachine} {f g : NFiber}
    {next : Native.NIter} (same : Same choose m n) (key : g.id = f.id)
    (credit : fiberCredits choose g = fiberCredits choose f) (kept : IterKept choose n g next) :
    IterKept choose m f next := by
  refine ⟨kept.1.trans same.1, fun id => (kept.2.1 id).trans (same.2.1 id),
    kept.2.2.1.trans key, ?_⟩
  have debit := kept.2.2.2
  unfold IterDebit at debit ⊢
  rw [same.2.2.1, same.2.2.2] at debit
  change _ + _ + _ ≤ _ + fiberCredits choose g + _ at debit
  rw [credit] at debit
  exact debit

/-- Loop-top interruption and scheduler yield injection retain the selected frame credits. -/
theorem iteration_kept (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (y : Bool) (ok : Ok m) :
    letI := evaluatorFor p table
    IterKept choose m f (iteration (interpOf p table) m f y) := by
  letI := evaluatorFor p table
  have topKey : (countOp (runloopTop f)).id = f.id := by
    unfold countOp runloopTop
    split <;> rfl
  have topCredit : fiberCredits choose (countOp (runloopTop f)) = fiberCredits choose f := by
    unfold countOp runloopTop
    split <;> rfl
  unfold iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop f)) y with
  | none => exact rebase (.refl choose m) topKey topCredit (evaluate_kept choose p table m _ y ok)
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      apply rebase (same_emit choose m
        [.yieldInjected (countOp (runloopTop f)).id (countOp (runloopTop f)).currentOpCount] rfl rfl)
        topKey topCredit
      exact evaluate_kept choose p table _ _ _ (emit_ok ok _)
    · cases injected

end Effect4.Program.FinalizerTransfer
