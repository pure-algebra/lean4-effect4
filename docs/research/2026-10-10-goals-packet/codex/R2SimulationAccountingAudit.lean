import Effect4.Laws.Machine.Book
import Effect4.Laws.Machine.FiberSumMessages
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Program.Simulation.Deliver
import Effect4.Laws.Program.Simulation.Actions
import Effect4.Laws.Program.Simulation.Evaluate
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.Simulation.Drive
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.ReleaseCustody.Evaluation
import Effect4.Laws.Program.ReleaseCustody.IterationDebit
import Effect4.Laws.Program.ReleaseCustody.NativeSequencing
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.Book Effect4.Laws.Machine.FiberSumMessages Effect4.Laws.Machine.WriterWeights Effect4.Laws.Program.Simulation.Fibers Effect4.Laws.Program.Simulation.Deliver Effect4.Laws.Program.Simulation.Actions Effect4.Laws.Program.Simulation.Evaluate Effect4.Laws.Program.Simulation.Pending Effect4.Laws.Program.Simulation.Drive Effect4.Laws.Program.RuntimeR Effect4.Laws.Program.ReleaseCustody.Evaluation Effect4.Laws.Program.ReleaseCustody.IterationDebit Effect4.Laws.Program.ReleaseCustody.NativeSequencing
