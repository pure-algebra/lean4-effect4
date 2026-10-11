import Effect4.Laws.Machine.RefFootprint
import Effect4.Laws.Program.NativeHeapExecution
import Test.Dogfood.Scenario.Atomic.Store
import Test.Dogfood.Scenario.Atomic.WriterSync
import Test.Machine.ReferenceFootprint
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.RefFootprint Effect4.Laws.Program.NativeHeapExecution Test.Machine.ReferenceFootprint
#axiom_audit Test.Dogfood.Scenario.Atomic.Store Test.Dogfood.Scenario.Atomic.WriterSync
