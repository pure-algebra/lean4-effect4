import Effect4.Laws.Machine.StatePreservation
import Effect4.Laws.Program.NativeEvaluation

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: native scoped interception transports the same store predicate as its primitive hooks.
Reach: actual native primitive, sequential scope entry and state-first unsafe scope close.
Limit: local primitive and scope-store fields remain explicit premises.
Consumer: initialized allocation-count growth and other-row flow through actual crew iterations.
-/
set_option autoImplicit false
namespace Effect4.Program.NativeStatePreservation
open Effect4 Effect4.Machine Effect4.Program

/-- Scoped exit adds only its actual unsafe close to the existing primitive store contract. -/
theorem exit_scoped (root : NativeEff) (P : Stores → Prop)
    (primitive : ∀ (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool), P machine.state →
      P (evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding).machine.state)
    (close : ∀ scope exit flag state next program, P state →
      storesCloseScopeUnsafe scope exit flag state = some (next, program) → P next)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (held : P machine.state) : P (exitScoped root machine fiber yielding exit).machine.state := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact held
    · rename_i state program closed
      have kept := close _ _ _ machine.state state program held closed
      cases program <;> exact kept
  · exact primitive machine fiber yielding held

/-- The native dispatcher reuses its primitive store contract and the two scoped store writes. -/
theorem native (root : NativeEff) (table : RowTable) (P : Stores → Prop)
    (primitive : ∀ (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool), P machine.state →
      P (evaluatePrim (interpAt root view table) machine fiber yielding).machine.state)
    (emptyPrimitive : ∀ (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool), P machine.state →
      P (evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding).machine.state)
    (entry : ∀ (state : Stores), P state → P {state with scopes := state.scopes.make state.nextName .sequential, nextName := state.nextName + 1})
    (close : ∀ scope exit flag state next program, P state →
      storesCloseScopeUnsafe scope exit flag state = some (next, program) → P next)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : P machine.state) :
    P (evaluateNative root machine fiber yielding table).machine.state := by
  unfold evaluateNative
  split
  · split
    · exact entry machine.state held
    · exact primitive machine.completedExits machine fiber yielding held
  · exact exit_scoped root P emptyPrimitive close machine fiber yielding _ held
  · exact exit_scoped root P emptyPrimitive close machine fiber yielding _ held
  · exact primitive machine.completedExits machine fiber yielding held
end Effect4.Program.NativeStatePreservation
