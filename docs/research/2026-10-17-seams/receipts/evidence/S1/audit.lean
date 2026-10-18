import Test.Program.CheckCacheControls
import Test.Program.FillSetControls
import Test.Program.SourceDocumentControls
import Test.Program.SourceFeedControls
import Effect4.Laws.Program.SourceDocument
import Effect4.Laws.Program.SourceTable
import Effect4.Program.Typing.FillSet
import Effect4.Program.Typing.SourceDocument
import Effect4.Program.Typing.SourceSession
import ProofGraph.AxiomAudit
#axiom_audit Test.Program.CheckCacheControls Test.Program.FillSetControls Test.Program.SourceDocumentControls Test.Program.SourceFeedControls Effect4.Laws.Program.SourceDocument Effect4.Laws.Program.SourceTable Effect4.Program.Typing.FillSet Effect4.Program.Typing.SourceDocument Effect4.Program.Typing.SourceSession
