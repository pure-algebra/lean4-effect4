import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.RuleSets
import ProofGraph.Goal
import ProofGraph.Sketch

/-!
# Planned goals in the law graph

The law graph's entry point for planned proof obligations (decisions row 203). A law module that
imports this one declares a goal with `proof_goal G binders : P`, a theorem whose body is `sorry`
(`ProofGraph.Goal`), and decomposes one with `proof_sketch` (`ProofGraph.Sketch`). Downstream proofs use
a goal as a theorem; a theorem that does is proved modulo the goals its proof reaches, never
proved. Proving a goal replaces `proof_goal G : P` by `theorem G : P := …` in place.

Before a goal is declared, it is placed in the theory (`AGENTS.md`, "Every proof obligation is
placed in the theory"). The axiom gate (`Test/Audit/AxiomGate.lean`) admits `sorryAx` only as a
goal's own body and refuses a goal in a module the `Effect4` root reaches. `#auto_census`
(`Effect4.Laws.Auto.Census`) reports which goals a search already closes from their statements.
-/
