import Effect4.Laws.Program.Typed.Results
import Effect4.Laws.Program.ReferenceExpansion
import Effect4.Laws.Program.Typing.PartsTable
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.Typed.Scope
  Effect4.Laws.Program.Typed.Denotation
  Effect4.Laws.Program.Typed.Assembly
  Effect4.Laws.Program.Typed.LayerArm
  Effect4.Laws.Program.Typed.Commands.Clauses.All
  Effect4.Laws.Program.Typed.Results
  Effect4.Laws.Program.PathOrder
  Effect4.Laws.Program.ReferenceExpansion
  Effect4.Laws.Program.Typing.PartsTable

#plan_status Effect4.Program.Typed.moduleLayersTyped_of_typeOf
  Effect4.Program.Typed.layerPointTyped_redirect_module
  Effect4.Program.Typed.ref_builds
  Effect4.Program.Typed.denotesTyped
  Effect4.Program.Typed.load_typed
  Effect4.Program.Typed.reachable_typed
  Effect4.Program.Typed.obs_typed
  Effect4.Program.Typed.root_exit_hasTy
  Effect4.Program.expanded_refs_nil_of_wf
  Effect4.Program.Sketch.annotate_eq_table
  Effect4.Program.Sketch.table_fill
