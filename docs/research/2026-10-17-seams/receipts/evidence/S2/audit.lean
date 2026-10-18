import Test.Program.FillSetControls
import Effect4.Laws.Program.FillReference
import Effect4.Laws.Program.FillSet
import Effect4.Program.Typing.CheckCache
import Effect4.Program.Typing.FillSet
import ProofGraph.AxiomAudit
#axiom_audit Test.Program.FillSetControls Effect4.Laws.Program.FillReference Effect4.Laws.Program.FillSet Effect4.Program.Typing.CheckCache Effect4.Program.Typing.FillSet
