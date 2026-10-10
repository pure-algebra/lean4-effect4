# Module-layer step 2a review plan

## Finishing criteria

Read Claude's current session and inspect the changed reference and typing declarations.
Keep Claude's source and build work unchanged.
Check whole-block editor controls that the earlier component probe leaves open.
Record exact sources, imported artifacts, commands, outputs and limits.
Retain the review packet in a local commit.

## Placement before probes

| Check | Concept and property | Claim and consumer | Reach | Limits | Requirement |
| --- | --- | --- | --- | --- | --- |
| Whole-block annotation | `initial-algebras-folds`; part tables agree with address tables | Compatibility: `module-annotate-table`; `Sketch.annotate_eq_table`; `EditSession.open` | Empty and nonempty module layers, refused programs and nested environments | Finite evaluations; no execution or cost claim | R14 |
| Module-layer edits | `initial-algebras-folds`; typed subtree replacement | Preservation: `module-table-splices`; `Sketch.table_fill`; `EditSession.feed` | Same-type fills, undo and a refused replacement in child 2 | No new general proof; reference-aware editing stays outside the splice claim | R14 |
| Call addresses | `host-session-protocol`; reply admission reads checked call instances | Preservation: `block-call-instance`; `checkModule_programCallAt`; `HostSession.callTable` | A native call in a module layer at its source address | No host execution or reply-admission claim | R6, R14 |
| Module-layer hop | `residual-program-typing`; typed residuals | Fundamental property: `denote-typed`; `ref_builds`; M5 to M7 | The current module check, whole module-layer targets and signature extension | Source review until the owner build and dependency audit finish | R4 |
| Reference expansion | `initial-algebras-folds`; well-formed references expand | Substitution: `reference-expansion-complete`; `expanded_refs_nil_of_wf`; program admission | Module-first order, whole-layer targets and existing formation premises | No runtime termination, printing or per-call memo claim | R5 |

## Evidence method

The primary checkout remains at `9fb3b66cd` during initial inspection.
Claude's module-layer worktree starts at `cd61d9337` and contains uncommitted changes.
The earlier review is commit `752d363f0`.
This packet starts after the deterministic-fragment packet, commit `acf7cf41`.

The probe uses Claude's compiled modules read-only from the isolated review worktree.
It runs no Lake process in Claude's worktree.
The runner retains source and artifact hashes before and after the probe.
A changed artifact makes that run inconclusive.
These checks do not reproduce the whole library build or certify a landing.

## Diagnostic compatibility control

Concept: `initial-algebras-folds`, the located reference refusal.
Question: `Eff.firstRefFault` and `Api.explain` at the new child-2 address range.
Consumer: the editor's refusal display and an agent's repair command.
Reach: one previously absent child-2 target, before and after adding an empty module-layer field.
Limits: both programs are refused; a changed reason does not establish changed admitted behavior.
Requirement: R14, under row 341's located reference refusals.

The same refusal placement covers guard precedence for internal module pieces.
It checks enclosing, forward and reference targets before the final scope guard.
A mixed-fault program checks source-order diagnostics separately from module-first expansion order.
