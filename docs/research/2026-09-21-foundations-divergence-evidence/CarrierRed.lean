import Effect4.Laws.Program.Typed.Contracts
set_option autoImplicit false
namespace Probe.InterruptCarrierRed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
abbrev Frame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev Interp := PrimInterp EffName EffThunk Val Err Defect FiberId Ann
def original : CauseV := Cause.fail (.tag 42)
def sanitized : CauseV := Cause.interrupt (some ⟨1⟩)
def exhausted : Frame := ⟨.failure sanitized, [], true, some sanitized, false⟩
-- The requested terminal exit cannot be obtained by changing the saved current code.
example (interp : Interp) :
    (exhausted.resumeCause interp original (some (.failure original))).1 =
      .finished (.failure sanitized) := rfl
end Probe.InterruptCarrierRed
