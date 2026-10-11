import Effect4.Laws.Program.Typed.Scope
import ScopeControls
import MemoControls
import CleanupControls
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.Typed.Scope
#axiom_audit ScopeControls MemoControls CleanupControls
#plan_status Effect4.Program.scopeParams_child Effect4.Program.scopeParams_below Effect4.Program.scopeParams_body Effect4.Program.scopeParams_decl Effect4.Program.Signature.withParams_param
