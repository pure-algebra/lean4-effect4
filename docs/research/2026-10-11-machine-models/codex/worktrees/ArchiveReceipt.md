# Retired worktrees: preserved research and removed checkouts

The named retired checkouts are removed. Their research and unmatched committed work remain available.

Base: `c1239f28bf60c70706921610406db0831cb23585`.
Authorization: machine-models `CODEX-PROMPT.md`, item 8.
The earlier `Receipt.md` records the first three removals.
This slice removes the remaining seven named checkouts.

## Preservation

The six research archives reside in the primary checkout:
`docs/research/2026-10-11-machine-models/codex/worktrees/archives/`.
These are ignored local archives, not generated output or published evidence.
`archive-manifest.json` records each absolute archive path, archive hash, file hash, and symbolic link target.
The archive contains exactly the ignored research entries returned by `git ls-files`.
It preserves 59 regular files, 318 symbolic links, and 24633816 regular-file bytes.
It does not copy the research directory or follow symbolic links into source trees.

`archive-research.py` creates each archive and checks every saved entry against its original.
`remove-archived.py` checks the source hashes again before removing each checkout.
Both scripts assert clean tracked and untracked status and reject unmatched patches.
The removal uses `git worktree remove` without force.

`archive-removals.json` records each removed head, branch, and branch-deletion result.
Branches whose heads are not ancestors remain available, despite matching patches.

## Unmatched step branch

`step-captured-folds` has no changed files or ignored research.
Its unmatched patch is `9c22719b851c29aad12ab33c3e5d093489779355`.
Inspection identifies option consumption and module-step scope proofs.
The cleanup retains `codex/queue-step-data`, including that patch and its descendants.
Only its clean checkout is removed.
`retained-step-branch.json` records the complete patch comparison and retained head.

## Verification

The scripts complete successfully.
Fresh status and patch checks precede each removal.
The archive verification checks regular-file bytes and symbolic-link targets separately.
No source file changes; no build or behavior gate belongs to this cleanup.
Active proof worktrees remain available.
