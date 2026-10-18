import Effect4.Laws.Program.Admit
import Test.Program.TypedContract
import Effect4.Laws.Program.SourceTable
import Test.Program.SourceFeedControls
import Effect4.Laws.Tool.Exchange
import Test.Program.ExchangeControls
import Test.Program.ToolMethodsControls
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Program.Admit Effect4.Laws.Program.Admit Test.Program.TypedContract
#axiom_audit Effect4.Program.Typing.SourceSession Effect4.Laws.Program.SourceTable Test.Program.SourceFeedControls
#axiom_audit Effect4.Tool.Exchange Effect4.Laws.Tool.Exchange Test.Program.ExchangeControls
#axiom_audit Effect4.Tool.Methods Test.Program.ToolMethodsControls
