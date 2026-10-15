import M2Prefix
import M2FundedControl
import DenoteCtlInl
import OutlineDriver
import FinalizerAssembly
import ProofGraph.AxiomAudit
import ProofGraph.Plan

/-! The audit of the remaining-work probes. `M2Prefix` and `M2FundedControl` are the overwatch's
probes (`docs/research/2026-10-14-meanings/overwatch-probes/`), recompiled against the integrated
tree's oleans; the other three are this note's. -/

#axiom_audit M2Prefix
#axiom_audit M2FundedControl
#axiom_audit DenoteCtlInl
#axiom_audit OutlineDriver
#axiom_audit FinalizerAssembly

#plan_status Effect4.Run.Overwatch.block_awaits_at_every_cut Overwatch.M2FundedControl.host_driven_conclusion_refuted Effect4.Program.Denote.RemainingWork.denoteCtl_inl Effect4.Program.Denote.RemainingWork.denoteB_inl Effect4.Program.RemainingWork.OutlineDriver.outline_driver Effect4.Program.RemainingWork.OutlineDriver.step_of Effect4.Program.RemainingWork.OutlineDriver.history_of_lift Effect4.Program.RemainingWork.OutlineDriver.outline_history Effect4.Program.RemainingWork.OutlineDriver.shop_stages_of_lift Effect4.Program.RemainingWork.OutlineDriver.configured_reads Effect4.Program.RemainingWork.OutlineDriver.same_statement Effect4.Program.RemainingWork.FinalizerAssembly.custody_of_paths Effect4.Program.RemainingWork.FinalizerAssembly.custody Effect4.Program.RemainingWork.FinalizerAssembly.outside_census_of_custody Effect4.Program.RemainingWork.FinalizerAssembly.once_placed_outside_census_modulo
