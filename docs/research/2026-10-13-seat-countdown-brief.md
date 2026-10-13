# Seat brief: the countdown goal (seat COUNTDOWN)

Status: brief (history, not authority). 2026-10-13. Decisions row 376 (2) reopens the goal.

**The one thing to know first.** `Evaluating.countdown_parks_positional`
(`src/Effect4/Laws/Program/Typed/Commands/Clauses/Park.lean`) blocks 11 claims and R1, R6 and R9:
all of M7 (`#goal_impact`). The machine keeps a fired countdown observer stored until `exitDone`,
so J must type a stale observer and a duplicate command (`docs/research/2026-10-12-countdown-guard-note.md`,
findings 1 to 4). Seat tc-B guarded `fireObserver` by `Pending.waitingOn` and rewrote the countdown
equations (branch `land/tc-seat-B`, `ab2e4c915`, `7268dec31`), and never proved the goal.
`waitingOn` was then removed as unread (`256b60ac5`). Row 376 (2) rules the guard: a countdown
observer acts only when its record waits on the firing fiber, read from the record itself.

## Read first

- The guard note, whole; the two tc-B commits; `256b60ac5`.
- The tree: `Pending`, `fireObserver`, `countdownWalk`, `countdownParkEdits`, `dropToken`
  (`src/Effect4/Machine/Fibers.lean`); J's observer clauses (`StoredObserverOk`,
  `ObserverCommandOk`, `CountdownAt`, `src/Effect4/Laws/Program/Typed/Scheduler.lean`); the goal
  and its two uses in `Park.lean`.

## What to do, in order

1. **Probe first, in a scratch file.** Restore the record's current target (the field `waitingOn`,
   now read by the guard; set by the park and by each advance), so that the tc-B commits apply
   with the least change. Check by finite runs that no Effect run changes: the truth corpus's
   countdown programs, and `Api.run` on `awaitAll` programs, before and after.
2. **The machine change** in `fireObserver`'s countdown arm only, with its rc.112 and 4.0.1 lines
   cited (row 331). Regenerate what reads `Effect4.Machine.Fibers` (`make gen-lcnf`).
3. **J simplified** as the guard note says: `CountdownAt` loses its column condition, and J needs
   no uniqueness of countdown keys. Re-prove what unfolds the arm, in place, never weakened.
4. **The goal proved** in place (`proof_goal` becomes `theorem`). Then `#plan_status` of M7's top
   nodes and `#goal_impact` measured again.

## Reuse first (row 376 (3))

- Cherry-pick or adapt tc-B's commits before writing anything new. Before any new lemma, search:
  `git grep`, `#why`, `#auto_census` on the module you touch. List what you reused in the receipt.
- Proofs use aesop and its banks where they close (`src/Effect4/Laws/Auto/RuleSets.lean`).
- Place every obligation first (`AGENTS.md`, "Trust").

## Boundaries

- Worktree: `~/Dev/lean4-effect4-tc-B`, switched by the coordinator to branch `seat/countdown` at the
  base. Its `.lake` is older: expect one long first build.
- Edit `src/Effect4/Machine/Fibers.lean` (the record and `fireObserver`'s countdown arm),
  `src/Effect4/Laws/Program/Typed/**`, the readers of what you change, the `lcnf` group's outputs by
  regeneration, `Test/**`, and the root imports at their end. Never edit
  `src/Effect4/Laws/Machine/AnswerFlow*` (seat FLOW) except to repair a reader, `src/Effect4/Laws/Run/**`
  (seat REPLAY), `lakefile.toml`, `docs/core/**` or the registry.
- Every `lake` and `make` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. The machine
  change owes `make check-truth`, `make check-compiler` and `make check-ocaml`. Every reader of a
  changed definition builds before its commit. Commit by named paths. Never push or merge. Stop
  under 8 GiB free.
- Stop if the probe shows a changed Effect run, at a question of meaning, or at about eight hours.
  The receipt `docs/research/2026-10-13-seat-countdown-receipt.md` (force-added) names first the
  one thing to know before merging, then the base and head, the files, the commands and results,
  `#axiom_audit`, the placement, the reused declarations and M7's status by `#plan_status`.
