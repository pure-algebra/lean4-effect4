# Seat brief: the writer debits and the log goals (seat GOALS-2)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it.

**The one thing to know first.** Seat GOALS proved the history step of the three cleanup-log
goals (`PlaceFunding.Local.history_funded`). What remains of each is local: one evaluation's
debit for Atomic, and a writer ledger's weights for Workers and QueueWorkers. Close them in that
order, each proof replacing its `proof_goal` in place.

## Read first

- The receipt `docs/research/2026-10-13-seat-goals-receipt.md`: §2 (slice 2, the route to
  `evaluation`), §5.2 (the shared law and its local facts) and §8 (the order).
- `src/Effect4/Laws/Program/PlaceFunding/Run.lean` (`PlaceFunding.Local`, its lifts) and
  `Test/Dogfood/Scenario/Atomic/WriterHistory.lean` (the first instance, the goal `evaluation`).
- The debits to reuse: under `Test/Dogfood/Scenario/Atomic/`, `WriterMachine`, `WriterSync`, `WriterSuspensions`, `WriterLoops`, the
  source ledger's `Opportunities.native_debit` and `iteration_debit` (the template), and
  `Machine.WriterWeights` (only `mask_bound` and `fork_bound` are generic today).
- `Test/Dogfood/Scenario/Workers/Assertions.lean` (`logs_step`) and
  `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean` (`logs_history`).
- `#plan_status` on `Atomic.atomic`, `Workers.workers` and `QueueWorkers.queueWorkers` first:
  trust the tool over this brief.

## What to do, in order

1. **`WriterHistory.evaluation`.** Make the per-arm debits of `SourceOpportunityNative` generic
   in the weight. Write writer copies of each arm only if the generic form costs more. Its
   proof makes `Atomic.cleans_once` rest on `shop_stages` alone.
2. **The Workers writer ledger.** Its weights for the release notes, its `PlaceFunding.Local`,
   then `logs_step` through `Local.history_funded`.
3. **The QueueWorkers writer ledger,** the same way, then `logs_history`.
4. Each landed theorem's placement (the five things of `AGENTS.md`, "Trust") in the receipt.

## Boundaries

- Worktree: `git -C ~/Dev/lean4-effect4 worktree add ~/Dev/lean4-effect4-goals2 -b seat/goals2
  refactor/phase1-phase3`, then `cp -c -R ~/Dev/lean4-effect4/.lake ~/Dev/lean4-effect4-goals2/.lake`.
  Never copy `docs/research`; read the notes from the main checkout.
- Edit only `Test/Dogfood/**` and `src/Effect4/Laws/**`, with new imports at the end of the root
  files. Never edit `lakefile.toml`, `docs/core/decisions.md`, the registry, or `tools/`.
- Build with `LEAN_NUM_THREADS=2`, one `lake` at a time, narrow. Audit with `#axiom_audit`.
- Proof style: aesop banks in `Laws`, `simp only`, no `simp_all`, `first` or `try`.
- Commit on `seat/goals2` by named paths after each narrow build. Never push or merge.
- Run `df -h /System/Volumes/Data` before each long build; stop under 8 GiB free.

## Stop rules

Stop at a goal false as stated, and refute it by the kernel. Stop at a question of meaning,
under 8 GiB free, or at five hours. Write the receipt `docs/research/2026-10-13-seat-goals2-receipt.md`
and force-add it. It names first the one thing to know before merging. Then it gives the base and
head, the files, the commands and results, the axiom output, each placement and the frontier.
