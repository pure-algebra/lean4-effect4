# Codex: the last eight goals, one meaning, and the block call claim

## The one thing to know first

Revised after your first run (decisions rows 388 and 389). The owner wants the clear paths landed,
not more boundary work. So the chunk is smaller:
- **M3 first, the bulk:** the eight open planned goals.
- **M1, a deletion:** the block meaning is the one meaning from now on. The unused shared fold
  `denoteCtl` goes. No caller moves.
- **M2, a corollary:** the call claim for completed block runs, from `h9_blocks`. The pending-call
  form waits for SCOPE-1, which brings the host's interruption into the meaning.

A stop in one slice stops that slice only.

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
- No caller moves. An older meaning goes when its last caller moves for a reason of its own.

### M2: the call claim for completed block runs

- The claim: a completed, host-driven run of a `BlockRows` program makes exactly its meaning's
  host calls, in order, under its submitted-reply tape. Prove it as a corollary of `h9_blocks`.
  The tape host refuses a call that differs from the record, so a completed meaning run makes
  the recorded calls.
- Its first user: the cached to-do's call clause, an add on an empty list calls nothing
  (`Test/Dogfood/Scenario/Todo/Claims.lean` holds the straight one).
- If it is not a short corollary, write why in the receipt and stop this slice; build no prefix
  simulation.
- Your counterexample stays, as this claim's boundary control: an interrupted run is outside it
  (`interrupted_not_host_driven`).

## Done means

- The eight goals are proved, and `#plan_status` reports the application claims proved.
- `DenoteCtl.lean` is gone, and each older meaning's chain to the block meaning is listed.
- The block call claim is proved, or its reason is written.

## Stop and report at once when

- a goal is false as stated: give the counterexample, and go on with the other slices;
- a slice needs an edit to the machine, `Eff`, `Ty` or `Store.Val`.

## What you report

Append to `docs/research/2026-10-14-meanings/receipt.md`. Open with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the `#axiom_audit` output;
- each goal's status.

Propose decisions rows in the receipt, never in the register.
