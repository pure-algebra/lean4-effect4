# Seat brief: the last planned goals (seat GOALS)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it.

**The one thing to know first.** The library rests on no planned goal, but the five example
applications do. Close as many of their goals as the time allows, the shared laws first, each
proof placed in the theory before it is worked (`AGENTS.md`, "Trust", the five things). A goal
that is false as stated is repaired or refuted by the kernel, never weakened in silence.

## Where things stand (read, then verify with the tools)

- `docs/STATE.md`, "Next, in order", item 00: of the fourteen application goals, three are proved;
  nine are proved modulo seven smaller goals; Timeout's retry and cleanup goals stay open.
- The goals packet `docs/research/2026-10-10-goals-packet/README.md` and its four folders, each
  with a `Probe.lean`: the families, the one frame with four spellings, the one large shared law
  (each fiber's position in its own code: control linearity, fiber-local positions, a stage
  table), the smaller general laws, the trap at a symbolic job count, and the two goals found
  false (`retries_declared`, refuted by `retries_declared_refuted`; `cleanup_keeps`, which holds on
  `RunReachable` runs).
- The open goals in the tree (`proof_goal`): `Test/Dogfood/Scenario/Timeout.lean`
  (`retries_declared`, `cleanup_keeps`), `Atomic/Cleanup.lean` (`log_debits`), `Atomic/Store.lean`
  (`shop_stages`), `QueueWorkers/Assertions.lean` (`jobs_step`, `rest_step`, `logs_history`),
  `Workers/Assertions.lean` (`logs_step`), and in the law graph
  `src/Effect4/Laws/Program/FinalizerRun.lean` (`once_placed_pushes_once`) and
  `src/Effect4/Laws/Run/CallTree.lean` (`request_leads`). `countdown_parks_positional` stays a
  planned goal by ruling (`docs/STATE.md`, item 000); leave it.
- Run `#plan_status` (`tools/ProofGraph/Plan.lean`) on each application's top claim first, and
  write down the frontier: which goals each rests on. Trust the tool over this list.

## What to do, in order

1. **The frontier.** `#plan_status` for every application claim; a table of goal → claims it
   blocks → the packet's plan for it. Put it at the head of your receipt.
2. **The shared law first**, if the frontier says it blocks the most: one step law of the frame
   machine for many fibers, stated once, its four spellings unified (the packet's "one frame, four
   spellings"). Place it: its concept, its registry claim (a `proof_goal` with its `@[semantics]`
   placement in `Effect4.Laws` where it is a library law), its reach, what it does not establish,
   and its consumers.
3. **Then the smaller goals** in the order the frontier gives, each proof replacing its
   `proof_goal` in place.
4. **Timeout.** The packet's seat recommends repairing `timeoutForm`
   (`Test/Dogfood/P1HttpCache.lean`) so the race settles at the body's own exit, as rc.112's
   `raceAllFirst` does. That is a change to a program the owner reads: write the repair as a
   proposal in your receipt with the refutation's evidence, and do not land it without the
   coordinator.

## Boundaries

- Make your worktree: `git -C ~/Dev/lean4-effect4 worktree add ~/Dev/lean4-effect4-goals -b
  seat/goals refactor/phase1-phase3`, then clone the build copy-on-write:
  `cp -c -R ~/Dev/lean4-effect4/.lake ~/Dev/lean4-effect4-goals/.lake`. Never copy `docs/research`.
- Edit only `Test/Dogfood/**`, `src/Effect4/Laws/**` and, for a new law's registry entry,
  `tools/ProofGraph/Registry.lean` at its end. Never edit `lakefile.toml`, `docs/core/decisions.md`,
  the root imports except at the end, or anything under `tools/Tools/View/`.
- Build with `LEAN_NUM_THREADS=2`, one `lake` at a time, narrow (`lake build <Module>`, or
  `lake env lean <file>` for a test). Three other Lean builds may run on this machine.
- Proof style: `AGENTS.md`'s rules hold (aesop banks in `Laws`, `simp only`, no `simp_all`,
  `first`, `try`; every warning an error). Audit each landing's modules with `#axiom_audit`.
- Commit on `seat/goals` by named paths after each narrow build. Never push. Never merge.
- Run `df -h /System/Volumes/Data` before each long build; stop under 8 GiB free.

## Stop rules

Stop and hand back at: a goal false as stated (prove its negation by the kernel and stop on that
goal); a change to an application's program; a question of meaning; under 8 GiB free; six hours
of work. The receipt, `docs/research/2026-10-13-seat-goals-receipt.md` on your branch (force-add
it), names first the one thing the coordinator must know before merging, then the base and head
commits, the files, the commands and results, the axiom output, each landed theorem's placement,
and the frontier after your work.
