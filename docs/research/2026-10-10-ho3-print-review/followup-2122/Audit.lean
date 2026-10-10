import Effect4.Laws.Codegen.PrintTyped
import Effect4.Laws.Codegen.PrintReadable
import Effect4.Laws.Api.ModuleReadable
import ProofGraph.AxiomAudit
import ProofGraph.Plan

/-! The existing claims and their five placement points are in PLAN.md. -/
#axiom_audit Effect4.Laws.Codegen.PrintTyped Effect4.Laws.Codegen.PrintReadable Effect4.Laws.Codegen.Read Effect4.Laws.Codegen.ReadLeaf Effect4.Laws.Codegen.ReadPrint Effect4.Laws.Codegen.Definitions Effect4.Laws.Codegen.Module Effect4.Laws.Api.ModuleReadable
#plan_status Effect4.Program.printTyped_eq_print Effect4.Codegen.eraseJoinArgs_printTyped Effect4.Codegen.readTyped_printTyped Effect4.Program.readModule_printModule_defs
