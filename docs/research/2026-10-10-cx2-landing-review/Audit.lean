import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Program.Typed.Adequacy
import Effect4.Laws.Program.Typed.Admission
import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.Body
import Effect4.Laws.Program.Typed.Commands.Bookkeeping
import Effect4.Laws.Program.Typed.Commands.Clauses.Gen
import Effect4.Laws.Program.Typed.Commands.Clauses.Loop
import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Typed.LayerArm
import Effect4.Laws.Program.Typed.Mask
import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Program.Typed.Scope
import Effect4.Laws.Program.Typed.Commands.Clauses.All
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.MeaningSound Effect4.Laws.Program.Typed.Adequacy Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Typed.Assembly Effect4.Laws.Program.Typed.Body Effect4.Laws.Program.Typed.Commands.Bookkeeping Effect4.Laws.Program.Typed.Commands.Clauses.Gen Effect4.Laws.Program.Typed.Commands.Clauses.Loop Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Typed.LayerArm Effect4.Laws.Program.Typed.Mask Effect4.Laws.Program.Typed.Residual Effect4.Laws.Program.Typed.Scope

#plan_status Effect4.Program.Typed.invoke_arm
#plan_status Effect4.Program.Typed.param_arm
#plan_status Effect4.Program.Typed.childDenotes_upto
#plan_status Effect4.Program.Typed.denotesTyped_of_layerFree
#plan_status Effect4.Program.Typed.denotesTyped
#plan_status Effect4.Program.Typed.m7_proved
