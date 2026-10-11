import Effect4.Laws.Program.Typing.HasTy
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Typing.CheckSound
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Definitions
import Effect4.Laws.Program.ExpandFix
import Effect4.Laws.Program.Typing.Closed
import Effect4.Laws.Program.Typing.Replace
import Effect4.Laws.Program.Typing.Restrict
import Effect4.Laws.Program.Typing.Annotate
import Effect4.Laws.Program.Typing.Splice
import Effect4.Laws.Program.Placement
import Effect4.Laws.Program.Typed.Sources
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.Typed.Sources Effect4.Laws.Program.Typing.HasTy Effect4.Laws.Program.Typing.CheckInversion Effect4.Laws.Program.Typing.CheckSound Effect4.Laws.Program.Signature Effect4.Laws.Program.Definitions Effect4.Laws.Program.ExpandFix Effect4.Laws.Program.Typing.Closed Effect4.Laws.Program.Typing.Replace Effect4.Laws.Program.Typing.Restrict Effect4.Laws.Program.Typing.Annotate Effect4.Laws.Program.Typing.Splice Effect4.Laws.Program.Placement
