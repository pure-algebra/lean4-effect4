import Effect4.Laws.Program.ReleaseCustody.Lift
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: scope-lifetime-finalization, R11.
Question: scope allocation preservation serves Execution.history and Workers.Assertions.releases_step.
Reach: actual native evaluation and every command prefix, with Execution.ScopeRows initially true.
Limit: scope identities and registration keys alone establish neither custody funding nor cleanup uniqueness.
Unlock: the custody command contract can carry its actual allocation premise through Machine.Lift.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.ScopeRows
open Effect4 Effect4.Machine Effect4.Program
open ScopeIdentity

/-- Unsafe scope close preserves identities and removes registrations before cleanup executes.
Consumer: both the native close hook and the special scoped-exit evaluator. -/
theorem close_unsafe (scope : Nat) (exit : ExitV) (masked : Bool)
    {state next : Stores} {program : Option Program} (held : Rows state)
    (step : storesCloseScopeUnsafe scope exit masked state = some (next, program)) : Rows next := by
  cases found : state.scopes.entryAt scope with
  | none =>
    simp only [storesCloseScopeUnsafe, scopeCloseSnapshot, found] at step
    cases step
  | some entry =>
    simp only [storesCloseScopeUnsafe, scopeCloseSnapshot, found, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
    obtain ⟨rfl, _⟩ := step
    exact Rows.of_allocated (held.allocated.closeState scope exit)
      (ScopeStore.keysBelow_closeState held.2.2)

/-- The actual native store hooks satisfy the shared command contract.
Consumer: native evaluation, loop and command preservation below. -/
theorem hooks (root : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV)) :
    StatePreservation.Hooks (interpAt root completed table) Rows := by
  constructor
  · intro name state next value held step
    have sync (operation : SyncOp) (step : syncOpStep operation state = some (next, value)) : Rows next :=
      Rows.of_allocated (syncOpStep_allocated held.allocated step) (syncOpStep_keysFresh held.2.2 step)
    cases name with
    | op operation => exact sync operation step
    | store stored =>
      cases stored with
      | op operation => exact sync operation step
      | _ => cases step
    | _ => cases step
  · intro name id token state held
    cases name with
    | store stored => cases stored <;> exact held
    | _ => exact held
  · intro mode scope id state next key held step
    exact Rows.of_allocated (scopeLinkFiber_allocated mode scope id held.allocated step)
      (Effect4.Machine.scopeLinkFiber_keysFresh mode scope id held.2.2 step)
  · intro scope exit flag id state next code held step
    change (storesCloseScope scope exit flag state).map (fun r => (r.1, embed r.2)) = some (next, code) at step
    obtain ⟨⟨changed, program⟩, closed, eq⟩ := Option.map_eq_some_iff.mp step
    have same := (Prod.mk.inj eq).1
    change changed = next at same
    subst changed
    obtain ⟨returned, unsafeStep⟩ := storesCloseScope_unsafe closed
    exact close_unsafe scope exit flag held unsafeStep
  · intro scope key state next held step
    change (match state.scopes.entryAt scope with
      | none => none
      | some _ => some {state with scopes := state.scopes.removeFinalizer scope key}) = some next at step
    split at step
    · cases step
    · cases Option.some.inj step
      exact Rows.of_allocated (held.allocated.removeFinalizer scope key)
        (ScopeStore.keysBelow_removeFinalizer held.2.2)
  · intro state held
    exact held
  · intro list phase state held
    change Rows (Stores.wakeList list phase state)
    unfold Stores.wakeList
    split <;> exact held

/-- Bookkeeping uses the same store hooks as callback evaluation.
Consumer: actual command preservation. -/
theorem hooks_of (root : NativeEff) (table : RowTable) :
    StatePreservation.Hooks (interpOf root table) Rows := by
  have checked := hooks root table []
  exact ⟨checked.sync, checked.async, checked.link, checked.close, checked.drop, checked.due, checked.wake⟩

/-- Ordinary primitive evaluation preserves the allocation invariant through shared store hooks.
Consumer: every native evaluator fallback. -/
theorem primitive (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Control.Fiber) (yielding : Bool) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (evaluatePrim (interpAt root m.completedExits table) m f yielding).machine :=
  StatePreservation.primitive _ Rows (hooks root table m.completedExits) m f yielding held

/-- Entering a scoped region allocates one empty scope at the current supply.
Consumer: native evaluation. -/
theorem enter (root : NativeEff) (point : Point) (m : NativeMachine)
    (f : Control.Fiber) (yielding : Bool) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (enterScoped root point m f yielding).machine :=
  Rows.of_allocated (held.allocated.make .sequential)
    ((ScopeStore.keysBelow_make held.2.2).mono (Nat.le_succ _))

/-- Scoped exit writes the close state before returning any cleanup code.
Consumer: native evaluation. -/
theorem exiting (root : NativeEff) (m : NativeMachine) (f : Control.Fiber)
    (yielding : Bool) (exit : ExitV) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (exitScoped root m f yielding exit).machine := by
  simp only [exitScoped]
  split
  · split
    · exact held
    · rename_i state program closed
      have kept := close_unsafe _ _ _ held closed
      cases program <;> exact kept
  · exact primitive root [] m f yielding held

/-- Every native evaluator branch preserves the same allocation predicate.
Consumer: actual loop and delivery commands. -/
theorem native (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Control.Fiber) (yielding : Bool) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (evaluateNative root m f yielding table).machine := by
  simp only [evaluateNative]
  split
  · split
    · exact enter root _ m f yielding held
    · exact primitive root table m f yielding held
  · exact exiting root m f yielding _ held
  · exact exiting root m f yielding _ held
  · exact primitive root table m f yielding held

/-- Every actual native command retains unique allocated scope identities and fresh registrations.
Consumer: Execution.history through the custody command contract. -/
theorem command (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (cmd : Cmd EffName EffThunk Val Err Defect FiberId Ann)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m cmd rest).1 := by
  exact StatePreservation.command (evaluator := evaluatorFor root table) _ Rows (hooks_of root table)
    (native root table) m cmd rest held

/-- Existing command induction covers every native command budget, including unfinished prefixes.
Consumer: task and decision custody transport. -/
theorem drive (root : NativeEff) (table : RowTable) (fuel : Nat) (m : NativeMachine)
    (cmds : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) (held : Execution.ScopeRows m) :
    Execution.ScopeRows (driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds).1 := by
  exact StatePreservation.drive (evaluator := evaluatorFor root table) _ Rows (hooks_of root table)
    (native root table) fuel m cmds held
end Effect4.Program.ReleaseCustody.ScopeRows
