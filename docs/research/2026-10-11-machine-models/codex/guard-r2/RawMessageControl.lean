import Effect4.Laws.Program.Guard.Settle
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.Settle
namespace R2GuardControl
set_option autoImplicit false
def program : NativeEff := .succeed (.lit .unit)
def machine : NativeMachine := Api.load program 0
def owner : NFiber := RunFiber.make Api.root (compile program 0) true
  (stores.budgetOf emptyCtx) emptyCtx
def raw : ReturnFields.NIter := ⟨machine, owner, false, .continue_, [],
  [.observe Api.root (.countdown Api.root 0)]⟩
theorem initial : GuardState machine := guardState_load program 0
theorem old_lookup : machine.fiber? owner.id = some owner := rfl
theorem old_valid : FiberGuardState machine (settledFiber raw) :=
  guardState_fiber initial (by exact List.mem_cons_self)
theorem old_keys : ReservedKeys machine (fiberKeys owner) := reservedKeys_nil machine
theorem not_guarded : ¬ GuardState (settle Api.root [] raw).1 := by
  intro guarded
  have bound := guarded.keysBelow (Api.root, 0) (by decide)
  exact Nat.not_lt_zero 0 bound
end R2GuardControl
