import Effect4.Laws.Program.ReleaseCustody.NativeParkDebit

/-!
Concept: scope-lifetime-finalization, R11.
Question: scoped native evaluator debit serves Execution.history and the original Workers release bound.
Reach: actual scope entry, continuation removal, state-first close and cleanup construction.
Limit: local debit establishes neither command-history closure nor source-use uniqueness or progress.
Unlock: the native evaluator aggregate uses the same scope store and continuation accounting.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeScopeDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

/-- Actual scoped entry creates an empty scope and retains the saved stack reservation.
Consumer: the source-action branch of the native evaluator aggregate. -/
theorem enter (q : List Nat) (root : NativeEff) (point : Point)
    (m : NativeMachine) (fiber : Control.Fiber) (yielding : Bool)
    (current : fiber.frame.current = .withFiber (.act point))
    (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (enterScoped root point m fiber yielding) := by
  have clean : NoAdd fiber.frame.stack := by
    apply opaque_noAdd (current ▸ held)
    · intro fin phase; cases phase
    · intro phase; cases phase
  have stored := ScopeTransfer.make q m.state.scopes m.state.nextName .sequential
  unfold ScopeTransfer.storedCredits at stored
  unfold IterDebit enterScoped outsideCredits fiberCredits
  simp only [List.map_nil, List.sum_nil, Nat.add_zero, noAdd_full q _ _ clean,
    currentCredits, Evaluation.resolve_credits, current, stored]
  omega

/-- State-first unsafe close transfers the selected cleanup order into its optional program.
Consumer: the actual scoped exit branch below. -/
theorem close_unsafe (q : List Nat) (scope : Nat) (exit : ExitV) (masked : Bool)
    {state next : Stores} {program : Option Program}
    (unique : (state.scopes.entries.map ScopeEntry.key).Nodup)
    (step : storesCloseScopeUnsafe scope exit masked state = some (next, program)) :
    ScopeTransfer.storedCredits q next.scopes +
      (program.map fun code => currentCredits q (embed code)).getD 0 =
        ScopeTransfer.storedCredits q state.scopes := by
  cases found : state.scopes.entryAt scope with
  | none =>
    simp only [storesCloseScopeUnsafe, scopeCloseSnapshot, found] at step
    cases step
  | some entry =>
    simp only [storesCloseScopeUnsafe, scopeCloseSnapshot, found, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, ScopeStore.closeState, Option.some.injEq,
      Prod.mk.injEq] at step
    obtain ⟨rfl, rfl⟩ := step
    have changed := ScopeTransfer.replace q state.scopes entry (Scope.closeState entry.scope exit)
      unique (List.mem_of_find?_eq_some found)
    have transferred := close_scope q entry.scope exit
    rw [transferred.1, Nat.add_zero] at changed
    have returned : ((match entry.scope.closeOrder with
        | [] => none
        | [fin] => some (finProgram fin exit)
        | _ => some (Prim.suspend (Thunk.body (ProgName.closeWalk entry.scope.strategy entry.scope.closeOrder exit)))).map
        fun code => currentCredits q (embed code)).getD 0 = scopeCredits q entry.scope := by
      rw [← transferred.2]
      cases entry.scope.closeOrder with
      | nil => rfl
      | cons fin rest =>
        cases rest with
        | nil =>
          simp only [Option.map_some, Option.getD_some, fin_program_credits, orderCredits,
            List.countP_cons, List.countP_nil, Nat.zero_add, credit]
        | cons second rest => rfl
    exact (congrArg (fun n => ScopeTransfer.storedCredits q
      (state.scopes.setEntry {entry with scope := Scope.closeState entry.scope exit}) + n) returned).trans changed

/-- Selecting an administrative scoped callback retains at most the saved stack's credits.
Consumer: the actual scoped exit debit. -/
theorem exit_pop_bound (q : List Nat) (fiber : Pop.Frame) (exit : ExitV)
    (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (found : (fiber.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body (.scopedExit previous scope) flag)) :
    stackCap q (fiber.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).fiber.stack ≤
        stackCredits q fiber.current fiber.stack := by
  cases exit with
  | success value =>
    have bounded := Pop.getCont_value q fiber.current fiber
    unfold Pop.valueCredits Pop.valueAnswer at bounded
    rw [found] at bounded
    simpa only [futureCredits, Nat.zero_add] using bounded
  | failure cause =>
    have bounded := CausePop.getCont_cause q fiber cause
    unfold CausePop.popCredits CausePop.answerCredits at bounded
    rw [found] at bounded
    have final := Nat.le_trans bounded (Evaluation.failure_stack_le q cause fiber.current fiber.stack)
    simpa only [futureCredits, Nat.zero_add] using final

/-- Scoped exit transfers the closed store's cleanup credits after the actual continuation pop.
Consumer: the complete native evaluator aggregate at both success and failure. -/
theorem exiting (q : List Nat) (root : NativeEff) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (exit : ExitV)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (fallback : IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits) m fiber yielding)) :
    IterDebit q m fiber (exitScoped root m fiber yielding exit) := by
  let pop := fiber.frame.getCont
    (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
    (match exit with | .success _ => none | .failure cause => some cause)
  have noPush := FrameDebit.noPush_counts q _ (FrameDebit.getCont_no_push fiber.frame
    (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
    (match exit with | .success _ => none | .failure cause => some cause))
  change FrameDebit.starts q pop.events = 0 ∧ FrameDebit.registrations q pop.events = 0 at noPush
  have counts := NativeAccounting.frame_counts q fiber.id pop.events
  simp only [exitScoped]
  split
  · rename_i body previous scope flag selected
    change pop.answer = .frame (.onExit body (.scopedExit previous scope) flag) at selected
    have tail : NoAdd pop.fiber.stack := by
      cases exit with
      | success value => exact NativeSequencing.exit_pop_noAdd fiber.frame held (.success value) body (.scopedExit previous scope) flag selected
      | failure cause => exact NativeSequencing.exit_pop_noAdd fiber.frame held (.failure cause) body (.scopedExit previous scope) flag selected
    have bounded : stackCap q pop.fiber.stack ≤ stackCredits q fiber.frame.current fiber.frame.stack := by
      cases exit with
      | success value => exact exit_pop_bound q fiber.frame (.success value) body previous scope flag selected
      | failure cause => exact exit_pop_bound q fiber.frame (.failure cause) body previous scope flag selected
    dsimp only [pop] at tail bounded counts noPush
    split
    · cases exit
      all_goals
        dsimp only at tail bounded counts noPush
        unfold IterDebit
        simp only [RunMachine.emit_trace, List.countP_append, List.map_nil, List.sum_nil,
          Nat.add_zero, fiberCredits, noAdd_full q _ _ tail, Evaluation.exit_credits,
          counts.1, counts.2, noPush.1, noPush.2]
        change _ + outsideCredits q fiber.id m + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
        omega
    · rename_i state program closed
      change storesCloseScopeUnsafe scope (pop.deliveredExit exit) pop.fiber.interruptible m.state =
        some (state, program) at closed
      have transferred := close_unsafe q scope (pop.deliveredExit exit) pop.fiber.interruptible unique closed
      unfold ScopeTransfer.storedCredits at transferred
      cases program <;> cases exit
      all_goals
        dsimp only at tail bounded counts noPush
        unfold IterDebit
        simp only [RunMachine.emit_trace]
        unfold outsideCredits
        simp only [RunMachine.emit, List.countP_append, List.map_nil, List.sum_nil,
          Nat.add_zero, fiberCredits, NativePrimitiveDebit.finalizer_code,
          noAdd_full q _ _ tail, Evaluation.exit_credits, List.countP_cons, List.countP_nil,
          ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false,
          counts.1, counts.2, noPush.1, noPush.2]
        simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
          Nat.add_zero] at transferred
        omega
  · exact fallback

/-- All native evaluator branches retain the actual scope and continuation debit.
Consumer: iteration accounting, then `Execution.history` at the original Workers statement. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem native (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment root) (owned : SourceScope.FrameAt root fiber.frame)
    (sequential : SourceScope.SequentialSource root)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (races : m.races = []) :
    IterDebit q m fiber (evaluateNative root m fiber yielding table) := by
  have ordinary := NativeParkDebit.primitive q root table m fiber yielding held fragment owned
    sequential fibers scopes fresh races
  have exitFallback := NativeParkDebit.primitive q root [] m fiber yielding held fragment owned
    sequential fibers scopes fresh races
  unfold evaluateNative
  split
  · rename_i point current
    split
    · exact enter q root point m fiber yielding current held
    · exact ordinary
  · exact exiting q root m fiber yielding _ held scopes exitFallback
  · exact exiting q root m fiber yielding _ held scopes exitFallback
  · exact ordinary

end Effect4.Program.ReleaseCustody.NativeScopeDebit
