import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import ProofGraph.AxiomAudit
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.ParallelControl
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

def root : NativeEff := .succeed (.lit .unit)
def fin : FinName := .foreign {path := [], env := [], fuel := 1, tape := [], ctx := emptyCtx}
def registration : NCode := .onSuccess (.sync (.op (.scopeAdd 0 fin))) (.afterScopeAdd .unit fin)
def original : Control.Fiber := RunFiber.make ⟨0⟩ (.withFiber (.store (.act (.closePar [fin] (.success .unit)))))
  true (2048, false) emptyCtx
def before : NativeMachine := {(Api.load root 1).update original with trace := [.frame ⟨0⟩ (.pushed registration)]}
def result : RuntimeShape.Iteration := evaluateNative root before original false []
def after : NativeMachine := result.machine.update result.fiber

#guard currentCredits [] original.frame.current == 1
#guard outsideCredits [] original.id before == 0
#guard outsideCredits [] original.id result.machine == 1
#guard fiberCredits [] result.fiber == 1
#guard result.outcome == .commands
theorem actual_commands : result.nested = [.evaluate ⟨1⟩, .closeParAwait ⟨0⟩ false [⟨1⟩]] := rfl

theorem before_funded : Funded [] before [] := by unfold Funded; decide
theorem actual_iteration_not_debit : ¬ IterDebit [] before original result := by unfold IterDebit; decide
theorem settled_not_funded : ¬ Funded [] after result.nested := by unfold Funded; decide
end Effect4.Program.ReleaseCustody.ParallelControl
#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeAccounting
