import Effect4.Laws.Machine.Book
import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.DenoteR
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Means
import Effect4.Laws.Program.Guard.RaceSites
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Machine.Fibers Effect4.Laws.Machine.Book Effect4.Laws.Program.Sched Effect4.Laws.Program.DenoteR Effect4.Laws.Program.EvaluateR Effect4.Laws.Program.Means Effect4.Laws.Program.Guard.RaceSites
