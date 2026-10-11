import Effect4.Laws.Program.ReleaseCustody.Execution
import ProofGraph.AxiomAudit

/-!
Concept: scope-lifetime-finalization, R11.
Question: control for the internal command obligation used by worker release accounting.
Reach: an arbitrary command configuration admitted by the proposed Ready assertion.
This is not an admitted run and refutes no application claim or runtime behavior.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CommandControl
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

def root : NativeEff := .succeed (.lit .unit)
def fin : FinName := .foreign {path := [], env := [], fuel := 1, tape := [], ctx := emptyCtx}
def original : Fiber := RunFiber.make ⟨0⟩ (Api.compile root 1) true (2048, false) emptyCtx
def parked : Fiber := {original with
  parked := .withGuard 0
  frame := {original.frame with
    current := .success .unit
    stack := [.onSuccess (.sync (.op (.scopeAdd 0 fin))) (.afterScopeAdd .unit fin)]}}
def before : NativeMachine := (Api.load root 1).update parked
def command : Command := .resume ⟨0⟩ 0 (.success (reifyExitVal (.success .unit)))

def after : NativeMachine :=
  letI := evaluatorFor root []
  (driveStep (interpOf root []) before command []).1

#guard machineCredits [] before == 0
#guard machineCredits [] after == 1
#guard before.trace.countP (ReleaseTrace.registeredAt []) == 0
#guard after.trace.countP (ReleaseTrace.registeredAt []) == 0

theorem before_ready : Execution.Ready [] before := by
  apply Execution.ready_update [] (Api.load root 1) original parked
  · exact Execution.load root 1 []
  · rfl
  · rfl
  · intro p present
    cases present
  · intro bucket present
    cases present
  · decide

theorem before_funded : Funded [] before [command] := by unfold Funded; decide
theorem after_unfunded : ¬ Funded [] after [] := by unfold Funded; decide

/-- The former command contract admits the invalid state and cannot preserve its credit assertion. -/
theorem contract_refuted : ¬ Execution.CommandContract root [] [] := by
  intro contract
  letI := evaluatorFor root []
  obtain ⟨_, _, next, _⟩ := contract [] () before command [] rfl
    ⟨before_ready, fun _ => ⟨before_funded, by
      intro task member
      cases member⟩⟩
  exact after_unfunded next.funded

end Effect4.Program.ReleaseCustody.CommandControl
