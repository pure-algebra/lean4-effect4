import Effect4.Machine.Supervision.FirstExit
import Effect4.Machine.Fibers
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.RaceFirst
import Test.Machine.RaceFirst
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Machine.Supervision.FirstExit Effect4.Machine.Fibers Effect4.Laws.Machine.Clauses Effect4.Laws.Machine.RaceFirst Test.Machine.RaceFirst
