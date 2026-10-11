import Effect4.Laws.Program.NativeHeapHistory
import Test.Dogfood.Proofs.HostTimeoutNumberFormFamily
import Test.Dogfood.Scenario.Timeout
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.EditObserverWords Test.Dogfood.Proofs.HostTimeoutStateSteps Test.Dogfood.Proofs.HostTimeoutParkSteps Test.Dogfood.Proofs.HostTimeoutLocalSteps Test.Dogfood.Proofs.HostTimeoutSettle Test.Dogfood.Proofs.HostTimeoutObservers Test.Dogfood.Proofs.HostTimeoutRaceCommands Test.Dogfood.Proofs.HostTimeoutCancellation Test.Dogfood.Proofs.HostTimeoutHistory
#axiom_audit Effect4.Laws.Program.NativeHeapExecution Test.Dogfood.Proofs.HostTimeoutNumberState
#axiom_audit Test.Dogfood.Scenario.Timeout
