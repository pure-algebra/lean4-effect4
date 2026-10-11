import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Messages
import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.Guard.FinishQueue
import Effect4.Laws.Program.Guard.SettleQueue
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.Interference Effect4.Laws.Program.Guard.Core Effect4.Laws.Program.Guard.Messages Effect4.Laws.Program.Guard.RegistrationQueue Effect4.Laws.Program.Guard.FinishQueue Effect4.Laws.Program.Guard.SettleQueue
