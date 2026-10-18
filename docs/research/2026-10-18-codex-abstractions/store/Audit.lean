import Effect4.Tool.Exchange
import Effect4.Laws.Tool.Exchange
import Test.Program.ExchangeControls
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Tool.Exchange Effect4.Laws.Tool.Exchange Test.Program.ExchangeControls
