# Module-layer law review plan

Finish when the changed law modules pass a dependency audit and their named consumers report their proof status.
Record the implementation commit, draft hashes, commands, outputs and evidence limits.
Keep the implementation worktree unchanged.

## Placement

This packet audits existing statements. It introduces no theorem or proof obligation.
The earlier placement is [the step 2a review plan](../2026-10-10-module-layer-step2a-review/PLAN.md).

| Concept and property | Claim, role and consumer | Reach | Limits | Unlock |
| --- | --- | --- | --- | --- |
| `residual-program-typing`; typed residuals | `denote-typed`, fundamental property; `ref_builds` and `load_typed` consume the module-layer check | Checked module layers, whole declaration references and signature extension | Typing does not establish progress, host agreement or termination | M5 to M7; R4 |
| `translation-simulation`; recorded exits satisfy their declared types | `m7-capstone-goals`; `root_exit_hasTy` consumes `obs_typed` | Checked programs and admitted tapes, at the existing frame-machine boundary | Recorded exits only; no target-runtime claim | M7; R4 |
| `initial-algebras-folds`; well-formed references expand | `reference-expansion-complete`, substitution; `expanded_refs_nil_of_wf` | Existing formation and reference-order premises, including whole module declarations | Expansion does not establish execution termination or per-call sharing | R5 |
| `initial-algebras-folds`; annotation agreement and subtree replacement | `module-annotate-table`, compatibility; `module-table-splices`, preservation; edit sessions consume both | Exact premises of `Sketch.annotate_eq_table` and `Sketch.table_fill` | No cost claim; reference-aware replacement remains outside the splice theorem | R14 |

## Method

Read compiled draft artifacts from Claude's worktree.
Run Lean only in the isolated review worktree.
Hash imported repository sources and artifacts before and after the audit.
Treat changed inputs as inconclusive.
Use `#axiom_audit` for the changed law modules and `#plan_status` for their public consumers.
The owner build log is observed evidence. This packet does not reproduce the implementation build or its behavior gates.
