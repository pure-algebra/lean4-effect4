# Retired worktree cleanup

Three named retired worktrees are removed. Research-bearing worktrees remain available.

Base: `6c4bb709dfed0abcb5277fbab754dae64d4f50c2`.
The machine-models prompt, item 8, authorizes this cleanup.
The retained inventory covers its ten named worktrees.

## Checks and result

Each removal follows fresh checks:

```sh
git status --short
git status --short --ignored -- docs/research
git cherry refactor/phase1-phase3
git merge-base --is-ancestor HEAD refactor/phase1-phase3
```

The three removed worktrees have no changed files, ignored research, or unmatched patches.
`git worktree remove` succeeds without force.

| Worktree | Branch result |
| --- | --- |
| `unguard` | `git branch -d` succeeds |
| `live-graph-routes` | `git branch -d` succeeds |
| `module-construction` | Keep `codex/checked-product-print`; its patches match, but its head is not an ancestor |

`removed.json` records exact paths, heads, branches, and deletion results.
`inventory.jsonl` records the pre-removal status and patch comparisons.
No active goals worktree changes.
No source changes, builds, or behaviour gates belong to this cleanup.

## Remaining worktrees

Six named worktrees contain ignored research. Preserve that evidence before removing them.
`step-captured-folds` also retains unmatched patch `9c22719b851c29aad12ab33c3e5d093489779355`.
Inspect that patch before removal.
The cleanup remains partial; it does not classify those remaining files as disposable.
