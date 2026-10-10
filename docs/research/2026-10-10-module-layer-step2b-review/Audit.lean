import Effect4.Laws.Api.ModuleReadable
import Effect4.Laws.Program.HoistingTotal
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Codegen.Module
  Effect4.Laws.Api.ModuleReadable
  Effect4.Laws.Program.Hoisting
  Effect4.Laws.Program.HoistingTotal

#plan_status Effect4.Program.readModule_printModule_defs
  Effect4.Program.readModule_printModule_defs_readable
  Effect4.Codegen.ModuleEmission.readModule
  Effect4.Api.printModule_roundTrip
  Effect4.Program.Eff.hoistAll_outside
  Effect4.Program.Eff.restoreAll_hoistAll
