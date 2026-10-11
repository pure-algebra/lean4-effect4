import Effect4.Laws.Program.Guard.SettleQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
namespace R2QueueRawControls
set_option autoImplicit false

def program : NativeEff := .succeed (.lit .unit)
def owner : NFiber := {RunFiber.make Api.root (.success .unit) true (0, false) emptyCtx with
  running := true}
def empty : NativeMachine := {Api.load program 0 with fibers := []}
def missing : ReturnFields.NIter := ⟨empty, owner, false, .continue_, [], [.dropToken 0]⟩

/-- Raw missing-owner settlement drops its old command tail. -/
theorem missing_discards : (settle Api.root [.evaluate Api.root] missing).2 = [] := rfl

/-- The old precise tail equation fails without a selected-owner premise. -/
theorem missing_refutes_old_tail : (settle Api.root [.evaluate Api.root] missing).2 ≠
    (settle Api.root [] missing).2 ++ [.evaluate Api.root] := by
  intro equal
  change ([] : List NCmd) = [Cmd.evaluate Api.root] at equal
  cases equal

def idle : NFiber := RunFiber.make ⟨1⟩ (.success .unit) true (0, false) emptyCtx
def machine : NativeMachine := {Api.load program 0 with fibers := [owner, idle], nextId := 2}
def fresh : Cause Err Defect FiberId Ann :=
  Machine.interruptCause (interpOf program []) (some Api.root) ReasonAnnotations.empty idle.id
def changed : ReturnFields.NIter :=
  ⟨machine, owner, false, .continue_, [], [.interrupt idle.id fresh]⟩

/-- An idle unparked target may receive new current code from an interrupt message. -/
theorem idle_current_changes :
    ((settle Api.root [] changed).1.fiber? idle.id).map (fun f => f.frame.current) ≠
      some idle.frame.current := by decide

/-- Active-unparked or exited command controls remain available at this same cut. -/
theorem actual_controls : RegistrationQueue.ControlsAway machine
    (settle Api.root [] changed).1 Api.root := by
  apply SettleQueue.controlsAway_settle Api.root [] changed Api.root rfl
  intro fiber f found _ _
  exact ⟨f, found, rfl, rfl, rfl, fun h => h⟩

end R2QueueRawControls
