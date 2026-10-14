# Codex: one meaning, the call tree past straight lines, and the last eight goals

## The one thing to know first

**Amended after Codex's first run (decisions row 388).** The first run stopped at M2's route with a
checked counterexample (`receipt.md`, `evidence/MeaningsPrefixProbe.lean`). An interruption
starts a finalizer's call that no reply-only tree explains. M2's route is now decided (below).
M1 and M3 never depended on M2, so the order is M1, M3, M2, and a stop in one slice stops only
that slice.

Before the faces chunk (`docs/research/2026-10-14-faces/prompt.md`), the owner wants the open
proof work closed and the meanings cleaned up and connected (2026-10-14). Three things are open,
measured at `d71ca9698`:

1. **Seven call-tree meanings, one shared fold that nothing uses.** `denoteCtl`
   (`src/Effect4/Laws/Program/DenoteCtl.lean`, cleanup C4) writes the control rules once. Six
   meanings are proved its instances (`denote_eq_ctl`, `denoteB_eq_ctl`, `denoteBWith_eq_ctl`,
   `denoteWith_eq_ctl`, `denoteRows_eq_ctl`, `denoteRowsB_eq_ctl`). But no caller moved: `denoteCtl`
   is used in one file, its own, while `denote` is used in 35. PROC-6's block meaning is a seventh
   copy: `blockAlgB` repeats the rules for `catchCause`, `matchCause`, `onExit`, `exit`,
   `catchIf`, `select` and `iterate`. It meets the others only on two fragments
   (`denoteBlockB_straight`, `denoteBlockB_loopedDataRows`).
2. **The recorded call tree holds on straight lines only.** `request_leads`, `request_in_tree`
   and `bound_in_tree` (`src/Effect4/Laws/Run/CallTree.lean`, claim
   `recorded-call-tree-prefix`) require `StraightRows` and `NoCauseHandler`. A program with
   definitions, a loop or a cause handler has no call-tree claim. The cached to-do is such a
   program.
3. **Eight planned goals** outside the audit fixtures (`#plan_status`, `generated/semantics.md`).

## Read first

- `AGENTS.md`, all of it.
- `src/Effect4/Laws/Program/DenoteCtl.lean`, its header first;
  `docs/research/2026-10-09-host-calls-and-cleanup.md`, cleanup C4.
- `src/Effect4/Laws/Program/BlockMeaning.lean` and PROC-6's receipt
  (`docs/research/2026-10-14-proc6-prep/landing-receipt.md`).
- `src/Effect4/Laws/Run/CallTree.lean`, its header and `request_leads`.
- `docs/research/2026-10-13-seat-flow-receipt.md` and `docs/research/2026-10-13-seat-goals2-receipt.md`
  (§7 and §8): the routes for the goals.
- Decisions rows 378 (12) and 387.

## Where you work

Your worktree, `/Users/pooks/Dev/lean4-effect4-codex`, on the branch the launch message names, at
the coordinator's head. The rules of PROC-6's brief hold
(`docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules that bind every slice").

## The slices, in order: M1, M3, M2

### M1: one meaning

- Widen `Ctl` so the block meaning is its instance. Its leaf reads the context and the parameter
  frames, and its call, invocation and parameter arms recurse at the budget. Prove
  `denoteBlockB_eq_ctl`, by `rfl` between generated algebras where the shapes allow, as the
  budgeted connectors are.
- Move every caller of the seven meanings onto `denoteCtl` and its instances. Then delete the
  copies: the exact connectors (`rfl`) make their old names abbreviations of the instance. Measure
  which cut-free meanings (`denote`, `denoteWith`, `denoteRows`) can follow, and do it. Report the
  rest with the reason. Never throw away a proof: each moved caller keeps its statement.
- The control rules then live in one algebra. SCOPE-1's new arms (masks, scopes, layers) are
  written once.
- Placement: concept `initial-algebras-folds` (two folds agree when their algebras do), cleanup
  C4's question. No behaviour gate is reached: no compile or machine definition changes.

### M2: the call tree past straight lines (the route decided)

- Widen `recorded-call-tree-prefix` from `StraightRows` with no cause handlers to `BlockRows`:
  definitions, loops and cause handlers.
- **The histories** (row 388 (1)): those with `Run.hostDriven`, the predicate `H9Blocks` already
  uses. It excludes the host's interruption, which the block meaning does not model, and your
  counterexample shows why. SCOPE-1's stage 5 adds the host's interruption to the meaning. The
  claim widens with it there, and your counterexample becomes this claim's red control until then.
- **The prefix simulation.** `h9_blocks` speaks of completed runs, and the call tree of pending
  calls at any command cut. Build the prefix connection: a reached, host-driven run's pending
  calls and bindings sit in the block tree under its submitted-reply tape, at some budget. Start
  from `compilesBlk_root`, and add the recorded-command invariant it lacks.
- **The source restriction.** `SourceScope.ExternalOnly` needs `directHead`, which refuses a
  block. Widen it to a block whose every body is direct.
- Scope the prefix simulation before a long proof, and put the scope in the receipt.
- Place the widened statements as planned goals first (`proof_goal`, with their `@[semantics]`
  placement), then prove them.
- Its first user: the cached to-do's version of `serves` (`Test/Dogfood/Scenario/Todo/Claims.lean`
  holds the straight one). An add on an empty list calls nothing, and every served request's
  calls are in the tree.
- It does not establish forks, scopes, layers or any outside host's agreement. The host boundary
  stays where `docs/core/host-boundary.md` puts it.

### M3: the eight goals (second, before M2)

- First the four that need a fact about values, through seat FLOW's answer flow
  (`PlaceFunding.NativeFlow.history`): `Workers.Assertions.logs_step`,
  `QueueWorkers.Assertions.logs_history`, `Timeout.cleanup_keeps`, `Timeout.retries_declared`.
- Then `QueueWorkers.Assertions.jobs_step` and `rest_step`, from the Queue's operation laws
  (`take_attempt`, `offer_attempt`, `poll_attempt`, the withdrawals) and the crew's own invariant.
- Then `Atomic.Store.shop_stages` (the GOALS-2 receipt's §7) and `once_placed_outside_census`
  (`src/Effect4/Laws/Program/FinalizerRun.lean`).
- Each proof replaces its `proof_goal` in place; the placement stays.

## Done means

- `#plan_status` reports every application claim proved, resting on no goal.
- `generated/semantics.md` shows no planned goal outside the audit fixtures (`make gen-semantics`).
- One control algebra holds the call-tree meanings.

## Stop and report at once when

- a goal is false as stated: give the counterexample;
- a slice needs an edit to the machine, `Eff`, `Ty` or `Store.Val`;
- M2's prefix simulation needs a machine change: report it, and keep M1 and M3.

A stop in one slice stops that slice only. The others go on.

## What you report

The receipt is `docs/research/2026-10-14-meanings/receipt.md`. It opens with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the `#axiom_audit` output;
- each goal's status;
- the callers moved and the copies deleted.

Propose decisions rows in the receipt, never in the register.
