import Effect4.Api.Session
import Effect4.Api.RefusalsDerived
import Effect4.Laws.Api.Session
import Effect4.Codegen.Print
import Effect4.Laws.Codegen.Services
import Effect4.Laws.Api.ModuleReadable
import Test.Api.SessionContract
import Test.Codegen.ServicesPrint
import Test.Codegen.ProgramServices
import Test.Codegen.DefinitionsPrint
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Api.Session Effect4.Api.RefusalsDerived Effect4.Laws.Api.Session Test.Api.SessionFixtures Test.Api.SessionContract Effect4.Codegen.Print Effect4.Laws.Codegen.Services Effect4.Laws.Api.ModuleReadable Test.Codegen.ServicesPrint Test.Codegen.ProgramServices Test.Codegen.DefinitionsPrint
#plan_status Effect4.Api.Built.session_ok_iff Effect4.Api.Built.session_retains
