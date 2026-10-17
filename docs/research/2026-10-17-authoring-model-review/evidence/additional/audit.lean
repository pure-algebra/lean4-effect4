import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Run.Tree
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.Signature Effect4.Laws.Program.Typing.Rebase Effect4.Laws.Program.Typing.PartsTable Effect4.Laws.Program.SourceTable Effect4.Laws.Program.Sketch
#axiom_audit Effect4.Laws.Run.Tree
#plan_status Effect4.Program.SourceSession.feed_coherent Effect4.Program.SourceSession.view_type Effect4.Program.check_restrict Effect4.Program.Checker.check_rebase Effect4.Program.Sketch.table_fill Effect4.Run.Tree.ofProgram_approx Effect4.Run.Tree.ofProgram_eq_denoteRowsB Effect4.Run.Tree.probe_stable Effect4.Run.Tree.settle_sound
