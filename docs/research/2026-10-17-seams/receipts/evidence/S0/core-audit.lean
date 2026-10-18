import Effect4.Program.Check
import Effect4.Program.Formation
import Effect4.Program.LayerView
import Effect4.Program.Admit
import Effect4.Laws.Program.Typing.Closed
import Test.Program.SeamsS0
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Program.Check Effect4.Program.Formation Effect4.Program.LayerView Effect4.Program.Admit Effect4.Laws.Program.Typing.Closed Test.Program.SeamsS0
