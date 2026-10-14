# Slice C receipt

Both frozen goals are proved without planned-goal dependencies. The parent must land the separate bodiesOf owner move before the proofs.

Base: 5290731d502d5a9f3335d950b8117b4146143eb4.
Prerequisite: 7ddfbc046, FragmentBlock owns bodiesOf and no longer imports ParamRows.
Proof commit: 453f2410cb3553cd965f54ba9bfec99f917257ba.
Worktree: /private/tmp/proc6-blockplain; branch codex/proc6-blockplain.

Changed files:
- src/Effect4/Laws/Program/FragmentBlock.lean
- src/Effect4/Laws/Program/Agreement/BlockPlain.lean

The proofs replace bodiesOf_blockRows and PlainHooks.of_blockRows in place. Their statements and fragment definitions stay unchanged. The helpers certify the Effs spine, compilation of each admitted body, and address descent through root blocks and invocation argument spines. Suspended calls and parameters return through the certified root resolver. Every helper names its rows-block-host consumer. No compile, machine, old Agreement, register or root import changes.

Commands (all from the isolated worktree):

    LAKE_CACHE_DIR=/tmp/proc6-blockplain-cache /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Effect4.Laws.Program.Agreement.BlockPlain

PASS, 377 jobs. narrow-build.log retains the final run. The first attempt failed because the sandbox refused the toolchain artifact cache; the supported cache redirect above resolved it. Intermediate proof errors were corrected and the saved final source rebuilt.

    LAKE_CACHE_DIR=/tmp/proc6-blockplain-cache /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build ProofGraph.AxiomAudit
    LAKE_CACHE_DIR=/tmp/proc6-blockplain-cache /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean /tmp/proc6-landing/blockplain/Audit.lean

PASS. Exact output: #axiom_audit: 183 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals.

No behavior gate is reached by this proof-only slice. No host or runtime claim is made. The rest of rows-block-host remains with its other placed obligations. No push or download occurred. git diff --check passed before commit.
