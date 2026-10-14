import MeaningsPrefixProbe
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit MeaningsPrefixProbe
#plan_status Test.MeaningsPrefixProbe.prefix_conclusion_refuted
  Test.MeaningsPrefixProbe.fragment_admitted
  Test.MeaningsPrefixProbe.recorded_reached
  Test.MeaningsPrefixProbe.finalizer_binding_accepted

#check Effect4.Run.H9Blocks
#check Effect4.Run.CallTree.request_leads
