import Effect4.Laws.Data.ListRel
import Effect4.Laws.Data.ListRelConnectors
import Effect4.Laws.Step.Reading
import Effect4.Laws.Step.Checking
import Effect4.Laws.Library.Pool.Ops
import Test.Program.StepConstruction
import Test.Program.PoolOps
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Data.ListRel Effect4.Laws.Data.ListRelConnectors Effect4.Laws.Step.Reading Effect4.Laws.Step.Checking Effect4.Laws.Library.Pool.Ops Test.Program.StepConstruction Test.Program.PoolOps
