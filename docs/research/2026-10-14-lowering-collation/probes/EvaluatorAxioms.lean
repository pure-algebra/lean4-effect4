import Conform.Lcnf.Semantics
import Conform.Lcnf.SemanticsTarget
import ProofGraph.AxiomAudit

/-!
# Probe A: which evaluator of the LCNF route sits under the trust ceiling (finite measurement)

    scratch/lean-slot.sh lake env lean docs/research/2026-10-14-lowering-collation/probes/EvaluatorAxioms.lean

A translation-validation theorem (rung 4 of `docs/research/type-tooling/seat-lcnf.md` §2) relates
two evaluators: `Conform.Lcnf.evalCode` over Lean's mono LCNF and `Conform.Lcnf.Target.evalT`
over the emitted fragment. A placed claim must rest on declarations inside
`[propext, Quot.sound]`. This probe asks the gate's own walk (`#axiom_audit`) about each module.

Evidence word: tested, finite (one run of the gate's walk over one build). The target evaluator
reaches `Classical.choice` through two `String` rules (decisions row 262); the probe asks whether the
source evaluator does too. Both audits refuse their module (`evaluator-axioms.log`).
-/

-- the source evaluator: mono `Code .pure`, the primitive table, the differential harness
#axiom_audit Conform.Lcnf.Semantics

-- the target evaluator: the emitted fragment, the word model, the primitive spellings
#axiom_audit Conform.Lcnf.SemanticsTarget
