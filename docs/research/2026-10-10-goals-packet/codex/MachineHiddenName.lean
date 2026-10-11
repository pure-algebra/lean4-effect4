import Effect4.Laws.Program.ReleaseCustody.Control
import ProofGraph.AxiomAudit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control

/-- The formerly hidden finalizer owns its credit before and after opening its stored program. -/
example (root : NativeEff) (q : List Nat) (c : Capture) (exit : ExitV) :
    currentCredits q (.suspend (.store (.body (.finalizerOf (.foreign c) exit)))) =
      credit q (.foreign c) ∧
    currentCredits q (suspendBodyAt root (.store (.body (.finalizerOf (.foreign c) exit)))) =
      credit q (.foreign c) := by
  constructor
  · rfl
  · exact prog_of_credits q (.finalizerOf (.foreign c) exit)

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Names Effect4.Laws.Program.ReleaseCustody.Control
