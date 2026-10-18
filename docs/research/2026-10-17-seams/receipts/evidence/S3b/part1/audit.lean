import Effect4.Laws.Tool.CodecProfile
import Effect4.Laws.Tool.Wire
import Effect4.Store.Domain.ContextCanonical
import Effect4.Tool.CheckDerived
import Effect4.Tool.CodecProfile
import Effect4.Tool.ToolDerived
import Effect4.Tool.Wire
import Effect4.Tool.WireTypes
import Test.Program.SeamsS3bWire
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Tool.CodecProfile Effect4.Laws.Tool.Wire Effect4.Store.Domain.ContextCanonical Effect4.Tool.CheckDerived Effect4.Tool.CodecProfile Effect4.Tool.ToolDerived Effect4.Tool.Wire Effect4.Tool.WireTypes Test.Program.SeamsS3bWire
