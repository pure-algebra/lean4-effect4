# Codex: the last eight goals, one meaning, and the call tree past straight lines

## The one thing to know first

Revised after your first run (decisions rows 388 to 390). The owner's rule (row 390): robust and
rigorous, with no shortcuts, and no stop over a technicality. We know what each claim is for.
When a goal is false as written, state the true goal that serves the same users. Prove it and
record the counterexample as its boundary control, then go on. Consolidate rather than case-split.

- **M3 first, the bulk:** the eight open planned goals.
- **M1, consolidation:** the block meaning is the one meaning; the unused shared fold goes.
- **M2, the full claim:** the recorded call tree past straight lines, with pending calls at
  every cut, over host-driven histories.

## Read first

- `AGENTS.md`, all of it.
- Your receipt, `docs/research/2026-10-14-meanings/receipt.md`, and its counterexample.
- `docs/research/2026-10-13-seat-flow-receipt.md` and `docs/research/2026-10-13-seat-goals2-receipt.md`
  (§7 and §8): the routes for the goals.
- Decisions rows 344, 378 (12), 387, 388 and 389.

## Where you work

Your worktree, on `codex/meanings`, fast-forwarded to the coordinator's head named in the launch
message. The rules of PROC-6's brief hold
(`docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules that bind every slice").

## The slices, in order: M3, M1, M2

### M3: the eight goals

- First the four that need a fact about values, through seat FLOW's answer flow
  (`PlaceFunding.NativeFlow.history`): `Workers.Assertions.logs_step`,
  `QueueWorkers.Assertions.logs_history`, `Timeout.cleanup_keeps`, `Timeout.retries_declared`.
- Then `QueueWorkers.Assertions.jobs_step` and `rest_step`, from the Queue's operation laws
  (`take_attempt`, `offer_attempt`, `poll_attempt`, the withdrawals) and the crew's own invariant.
- Then `Atomic.Store.shop_stages` (the GOALS-2 receipt's §7) and `once_placed_outside_census`
  (`src/Effect4/Laws/Program/FinalizerRun.lean`).
- Each proof replaces its `proof_goal` in place; the placement stays.

### M1: one meaning

- The block meaning (`denoteBlockB`) is the one meaning (row 389 (1)). SCOPE-1 and CONC-1 extend
  it, and only it.
- Each older meaning is its restriction to a fragment, by a named connector:
  `denoteBlockB_loopedDataRows`, `denoteBlockB_straight`, `denoteRowsB_straight`,
  `denoteB_straight`. List the chain from each of `denote`, `denoteB`, `denoteWith`,
  `denoteBWith`, `denoteRows` and `denoteRowsB` to the block meaning. Prove any missing link, one
  theorem each.
- Delete `src/Effect4/Laws/Program/DenoteCtl.lean`: nothing uses it, and no registry claim cites
  it. Remove its import.
- Move every caller that its connector moves without a case split, and delete each older
  meaning left with no caller. Report the rest, with the reason each stays.

### M2: the recorded call tree past straight lines

- Widen `recorded-call-tree-prefix` (`request_leads`, `request_in_tree`, `bound_in_tree`) from
  `StraightRows` with no cause handlers to `BlockRows`: definitions, loops and cause handlers.
- **The histories:** those with `Run.hostDriven`, `H9Blocks`'s own premise (row 388 (1)). The
  block meaning does not model the host's interruption, and your counterexample is the boundary
  control. SCOPE-1's stage 5 brings interruption into the meaning, and the claim widens with it.
- **The prefix connection:** a reached, host-driven run's pending calls and bindings sit in the
  block tree under its submitted-reply tape, at some budget, at every command cut. Build it from
  `compilesBlk_root` and the recorded-command invariant it lacks.
- **The completed-run form** follows from it with `h9_blocks`: a completed run makes exactly its
  meaning's calls, in order.
- **The source restriction:** widen `SourceScope.ExternalOnly` to a block whose every body is
  direct (`directHead` refuses a block today).
- Its first user: the cached to-do's call clauses, as `serves` has them for the straight to-do
  (`Test/Dogfood/Scenario/Todo/Claims.lean`).

## Done means

- The eight goals are proved, and `#plan_status` reports the application claims proved.
- `DenoteCtl.lean` is gone, and each older meaning's chain to the block meaning is listed.
- The recorded call tree holds on `BlockRows` over host-driven histories, with the cached
  to-do's call clauses proved on it.

## Stop and report at once when

- a slice needs an edit to the machine, `Eff`, `Ty` or `Store.Val`;
- no true statement serves a goal's users: give the counterexample. A goal false only as
  written is corrected and proved, not stopped (row 390).

## What you report

Append to `docs/research/2026-10-14-meanings/receipt.md`. Open with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the `#axiom_audit` output;
- each goal's status.

Propose decisions rows in the receipt, never in the register.
