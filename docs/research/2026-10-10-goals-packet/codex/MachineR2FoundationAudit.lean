import MachineR2FoundationReader
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Program.Interference
import ProofGraph.AxiomAudit
#axiom_audit MachineR2FoundationReader Effect4.Machine.Fibers Effect4.Laws.Machine.Clauses Effect4.Laws.Machine.Handles Effect4.Laws.Machine.MaskRuns Effect4.Laws.Program.Interference Effect4.Laws.Program.Guard.Core Effect4.Laws.Machine.Ledger Effect4.Laws.Program.Guard.NativeAssembly Effect4.Laws.Machine.StatePreservation Effect4.Laws.Program.LedgerRun
