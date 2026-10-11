import Effect4.Laws.Program.ReleaseCustody.NativeScopeDebit

/-!
Concept: scope-lifetime-finalization R11.
Question: whole native iteration accounting serves Execution.history and Workers.releases_step.
Reach: actual loop-top interruption, charged yield injection and native evaluator accounting.
Limit: the iteration bound establishes neither queued-frame preservation nor admitted-history closure.
Unlock: loop and delivery commands install one actual returned fiber using the shared scalar accounting.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeIterationDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

/-- A neutral evaluator entry spends only its selected local fiber's old reservation.
Consumer: both charged iteration branches below. -/
theorem entry (q : List Nat) (before after : NativeMachine) (fiber next : Control.Fiber)
    (it : RuntimeShape.Iteration) (key : next.id = fiber.id)
    (outside : outsideCredits q fiber.id after = outsideCredits q fiber.id before)
    (starts : after.trace.countP (ReleaseTrace.releaseAt q) = before.trace.countP (ReleaseTrace.releaseAt q))
    (registrations : after.trace.countP (ReleaseTrace.registeredAt q) = before.trace.countP (ReleaseTrace.registeredAt q))
    (bound : fiberCredits q next ≤ fiberCredits q fiber) (debit : IterDebit q after next it) :
    IterDebit q before fiber it := by
  unfold IterDebit at debit ⊢
  rw [key, outside, starts, registrations] at debit
  omega

/-- Actual loop charging, interruption and forced yield compose with the complete native debit.
Consumer: the loop command scalar bound, then the original admitted Workers history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem iteration (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment root) (owned : SourceScope.FrameAt root fiber.frame)
    (sequential : SourceScope.SequentialSource root)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (races : m.races = []) :
    IterDebit q m fiber (Effect4.Machine.iteration (evaluator := evaluatorFor root table)
      (interpOf root table) m fiber yielding) := by
  have kept := NativeSequencing.loop_top fiber held
  have source := NativeSequencing.loop_top_source root fiber owned
  have bound := Evaluation.loop_top_credits q fiber
  have key : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold runloopTop
    split <;> rfl
  unfold Effect4.Machine.iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop fiber)) yielding with
  | none =>
    change IterDebit q m fiber (evaluateNative root m (countOp (runloopTop fiber)) yielding table)
    have debit := NativeScopeDebit.native q root table m (countOp (runloopTop fiber)) yielding
      kept fragment source sequential fibers scopes fresh races
    exact entry q m m fiber _ _ key rfl rfl rfl bound debit
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      change IterDebit q m fiber (evaluateNative root _ _ true table)
      have wrapped := forced_wrapper kept 0
      have wrappedSource : SourceScope.FrameAt root
          { (countOp (runloopTop fiber)).frame with
            current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current } :=
        ⟨⟨trivial, source.1⟩, source.2⟩
      let next : Control.Fiber := {(countOp (runloopTop fiber)) with
          yieldOverride := none
          frame := {(countOp (runloopTop fiber)).frame with
            current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
      let after := m.emit [.yieldInjected (countOp (runloopTop fiber)).id
        (countOp (runloopTop fiber)).currentOpCount]
      have debit := NativeScopeDebit.native q root table
        after
        next
        true wrapped fragment wrappedSource sequential fibers scopes fresh races
      apply entry q m after fiber next _ key rfl _ _ _ debit
      · simp only [after, RunMachine.emit_trace, List.countP_append, List.countP_cons, List.countP_nil,
          ReleaseTrace.releaseAt, Bool.false_eq_true, if_false, Nat.add_zero]
      · simp only [after, RunMachine.emit_trace, List.countP_append, List.countP_cons, List.countP_nil,
          ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero]
      · dsimp only [next]
        rw [Evaluation.yield_wrapper_credits]
        exact bound
    · cases injected

end Effect4.Program.ReleaseCustody.NativeIterationDebit
