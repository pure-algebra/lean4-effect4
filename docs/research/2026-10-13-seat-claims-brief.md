# Seat brief: the application and claim records (seat CLAIMS)

Status: brief (history, not authority). 2026-10-13. Obligation O6 of
`docs/research/2026-10-13-authoring-obligations/README.md`.

**The one thing to know first.** Row 307 (9) asks that a program's theorems be part of its data,
and row 336 (9) ruled the claims packet's record (`docs/research/2026-10-07-packet-application-claims.md`).
Nothing landed. The packet's slices 6 to 10 waited on the call tree over host rows (DI-69), which
has landed as `denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`). So slices 1 to 6 can land
now. The packet was written against `0e9de44f`. The tree has moved since, so read it as a design
and its draft (appendix A) as a sketch.

## Read first

- The packet, whole, and the examination it tests (`docs/research/2026-10-07-theorems-of-a-program.md`).
- Decisions rows 203, 207, 254, 301, 307, 336 and 375.
- The tree: `Test/Dogfood/Scenario/Todo.lean`, `Test/Dogfood/Scenario.lean` (seat LIVE moved the
  events into `src/Effect4/Run/Event.lean` today), `tools/ProofGraph/Plan.lean` and
  `tools/ProofGraph/Registry.lean`, and `denoteRows` with `meaningUnder`.

## What to build, in order

1. **APP**: `src/Effect4/Program/Authoring/Application.lean`, the application and its entries.
2. **RECORD**: the claim record: each claim is a theorem or a planned goal with its placement, and
   the record adds its kind, the programs it reads and what it assumes, with its premise's grade.
3. **PROTOCOL**: a row's protocol as data, the reader `conforms`, one claim.
4. **MODEL**: the reference model, the reader `agrees`, two claims.
5. **QUERY-APP**: a request's row table, and the operation `claims`, which answers what is
   claimed of a program, by kind and status.
6. **TREE**: the tree forms of the to-do claims over `denoteRows`, so that the packet's planned
   goals become theorems where the call tree proves them (its §3.9).

## Rules from the last landings

1. **Reuse, never a second mechanism.** A claim's status comes from the plan (`#plan_status`), not
   from a field. A judgment already in the tree (`Typed`, the protocol judgment, `meaningUnder`) is
   used, not copied.
2. **No new gate.** Row 375 retired the goal gate's pin, so the packet's "the pin moves" no longer
   applies. The packet's second gate (`#application_gate`) becomes battery lines: readers and
   controls (row 301). Add no `#..._gate` command, no ratchet and no pinned count.
3. **Every reader of a changed definition builds.** Before a commit, list each reader with `git grep`
   and build them all. Seat LIVE missed one reader, and the merge found it.
4. **Place each obligation first** (`AGENTS.md`, "Trust"): its concept, its claim, its reach, what
   it does not establish, what it unlocks. A planned goal is `proof_goal` with `@[semantics]`.

## Boundaries

- Worktree: `git -C ~/Dev/lean4-effect4 worktree add ~/Dev/lean4-effect4-claims -b seat/claims
  refactor/phase1-phase3`, then `cp -c -R ~/Dev/lean4-effect4/.lake ~/Dev/lean4-effect4-claims/.lake`.
  Never copy `docs/research`.
- Edit `src/Effect4/Program/Authoring/**`, new modules under `src/Effect4/Program/` and
  `src/Effect4/Laws/Program/`, `Test/**`, and the root imports at their end. Propose registry claims
  in the receipt. Never edit `lakefile.toml`, `docs/core/**`, `tools/ProofGraph/Registry.lean`,
  `src/Effect4/Laws/Program/DenoteRows.lean` or `tools/Tools/View/`.
- Run every `lake` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh` (two build slots
  shared by every seat), narrow. Commit by named paths on `seat/claims`. Never push or merge. Stop
  under 8 GiB free.
- Stop at a question of meaning, or after slice 6, or at about six hours. The receipt
  `docs/research/2026-10-13-seat-claims-receipt.md` (force-added) names first the one thing to know
  before merging, then the base and head, the files, the commands and results, the axiom output
  (`#axiom_audit`), each placement, and the packet's slices 7 to 13 as they now stand.
