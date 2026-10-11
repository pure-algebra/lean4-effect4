import Test.Program.CommandDebit
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Program.ReleaseCustody.CommandRaceDebit
  Effect4.Laws.Program.ReleaseCustody.CommandStoreDebit Test.Program.CommandDebit
