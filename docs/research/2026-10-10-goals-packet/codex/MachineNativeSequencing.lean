import Effect4.Laws.Program.ReleaseCustody.NativeDebit
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.RuntimeShape

example (b : Api.Built) (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt b.program fiber.frame) :
    Returned (iteration (evaluator := evaluatorFor b.program b.table)
      (interpOf b.program b.table) m fiber yielding) :=
  Effect4.Program.ReleaseCustody.NativeSequencing.iteration_returned _ _ _ _ _ active held source

example (q : List Nat) (s next : Stores) (scope : Nat) (fin : FinName)
    (value : Val) (frames : List NCode)
    (unique : (s.scopes.entries.map ScopeEntry.key).Nodup) (fresh : s.ScopeKeysFresh)
    (held : Kept (.sync (.op (.scopeAdd scope fin))) frames)
    (step : syncOpStep (.scopeAdd scope fin) s = some (next, value)) :
    ReleaseCustody.ScopeTransfer.storedCredits q next.scopes + ReleaseCustody.Control.stackCredits q (.success value) frames ≤
      ReleaseCustody.ScopeTransfer.storedCredits q s.scopes + ReleaseCustody.Control.opCredits q (.scopeAdd scope fin) +
        ReleaseCustody.Control.stackCredits q (.sync (.op (.scopeAdd scope fin))) frames :=
  ReleaseCustody.NativeDebit.sync_op q s next _ value frames unique fresh held step

namespace MachineMaskCreditControl
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control

def fin : FinName := .foreign {path := [], env := [], fuel := 1, tape := [], ctx := emptyCtx}
def frames : List NCode := [.setInterruptible true,
  .onSuccess (.sync (.op (.scopeAdd 0 fin))) (.afterScopeAdd .unit fin)]

#guard stackCredits [] (.sync (.op (.scopeAdd 0 fin))) frames == 1
#guard stackCredits [] (.success .unit) frames == 1
#guard credit [] fin == 1

example : ¬ Kept (.sync (.op (.scopeAdd 0 fin))) frames := by
  intro held
  change Kept (.sync (.op (.scopeAdd 0 fin)))
    [.setInterruptible true, .onSuccess (.sync (.op (.scopeAdd 0 fin))) (.afterScopeAdd .unit fin)] at held
  cases held
  case clean missing => exact missing _ (List.mem_cons_of_mem _ (List.mem_cons_self)) _ _ _ rfl

end MachineMaskCreditControl

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Sequencing
  Effect4.Laws.Program.ReleaseCustody.PopSequencing
  Effect4.Laws.Program.ReleaseCustody.FrameSequencing
  Effect4.Laws.Program.ReleaseCustody.RuntimeShape
  Effect4.Laws.Program.ReleaseCustody.NativeSequencing

#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeDebit
