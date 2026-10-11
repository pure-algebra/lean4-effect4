import Effect4.Laws.Program.ReleaseCustody.OuterFrames
import Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue
import Effect4.Laws.Program.SourceOpportunityExecution
import Test.Dogfood.Scenario.Timeout
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Machine.ControlWeights Effect4.Laws.Program.SourceOpportunityExecution Effect4.Laws.Program.ReleaseCustody.LoopCommand Effect4.Laws.Program.ReleaseCustody.AdministrativeKept Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue Effect4.Laws.Program.ReleaseCustody.OuterFrames Test.Dogfood.Proofs.HostTimeoutCommands Test.Dogfood.Proofs.HostTimeoutHeap Test.Dogfood.Proofs.HostTimeoutState Test.Dogfood.Proofs.HostTimeoutScheduler Test.Dogfood.Proofs.HostTimeoutControls Test.Dogfood.Proofs.HostTimeoutAnswers Test.Dogfood.Proofs.HostTimeoutApplication Test.Dogfood.Proofs.HostTimeoutHistory
#axiom_audit Test.Dogfood.Scenario.Timeout
#plan_status Test.Dogfood.Scenario.Timeout.stale_never_applies Test.Dogfood.Scenario.Timeout.timeout
