import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Auto.KernelRfl
import ProofGraph.AxiomAudit
set_option autoImplicit false
namespace Test.MachineModels.StackCreditContext
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.ReleaseCustody
open Control Effect4.Laws.Auto
private def captured : Capture := ⟨[], [], 1, [], emptyCtx, 0, [], []⟩
private def selected : FinName := .foreign captured
private def saved : NCode := .onSuccess (.success .unit) (.afterScopeAdd .unit selected)
-- One saved frame, two actual active response shapes. A fixed leaf sum cannot express both.
example : stackCredits [] (.sync (.op (.scopeAdd 0 selected))) [saved] = 0 := by kernel_rfl
example : stackCredits [] (.yieldNowWith 0) [saved] = 1 := by kernel_rfl
example : stackCap [] [saved] = 1 := by kernel_rfl
-- A saved constant continuation changes the active context seen by the lower registration frame.
example : stackCredits [] (.yieldNowWith 0)
    [.onSuccessConst (.success .unit) (.sync (.op (.scopeAdd 0 selected))), saved] = 1 := by kernel_rfl
end Test.MachineModels.StackCreditContext
#axiom_audit Effect4.Laws.Program.ReleaseCustody.Control
