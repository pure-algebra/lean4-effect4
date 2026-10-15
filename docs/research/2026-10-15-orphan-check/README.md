# Orphan check of the worktrees, 2026-10-15

Status: research note, not authority. Base: `68765c384` on `refactor/phase1-phase3`.
Role: the coordinator's check that no seat's work is orphaned, at the owner's request.

## The one thing to know first

No committed work of any seat is orphaned. The two Claude seats' finished slices are on the
branch. Every Codex tree matches its archive, and every declaration their unmatched commits add
is on the branch. One app-session commit holds a generator change the branch lacks. Its patch is
kept here.

## What was checked

| Tree | Branch | Finding | Evidence |
| --- | --- | --- | --- |
| `lean4-effect4-codegen` | `claude/codegen` | CR-8, CR-7 part 1, CR-2, CR-6 and CR-4 part A merged at `ca133153b`; proposals ruled in row 395; CR-4 continues | `git merge`, clean |
| `lean4-effect4-cleanup` | `claude/cleanup` | S1 and S2 merged at `68765c384`; S3 continues | `git merge`, clean |
| eight Codex trees, listed in `docs/research/2026-10-15-codex-integration/uncommitted/` | `codex/meanings*`, `codex/timeout-m3*` | each head and status, ignored files included, equals its archive | `git status --short --ignored` against `status.txt` |
| the same | the same | 34 commits have no equal patch on the branch; their 98 files are all on the branch, and no declaration they add is missing | `git cherry`, then a declaration comparison per file |
| `lean4-effect4-gemini` | `gemini/consolidation` | no commit off the branch, clean | `git rev-list` |
| `.claude/worktrees/brave-ishizaka-7a3804` | `claude/brave-ishizaka-7a3804` | no commit off the branch, clean | `git rev-list` |
| `.claude/worktrees/loving-heyrovsky-c198ad` | `fix/proof-style-ratchet` | one commit, `fc2a0bbd7`, off the branch | `git cherry` |

## The one unmerged commit

`fc2a0bbd7` has two halves. The ratchet's baseline is obsolete: row 375 removed the proof-style
ratchet. The other half makes the scoped-law generator (`tools/Effect4Gen/Authoring.lean`) emit
`simp only` with named sets in place of `simp` and `simp_all`. The branch lacks that change. The
patch is `0001-proof-style-the-ratchet-passes-on-the-typed-context-.patch` in this folder. The
worktree is the app's to remove.

## What this does not establish

- The declaration comparison reads names, not bodies. A renamed declaration would read as missing,
  and none did.
- The archives hold the trees' uncommitted work as patches and tarballs. Whether that work should
  land is the integration note's question, not this one.
