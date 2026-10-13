# Seat brief: the answer-flow history producer (seat FLOW)

Status: brief (history, not authority). 2026-10-13. Decisions row 376 (1). The open goals probe
(`docs/research/2026-10-13-open-goals-probe/README.md`) and seat GOALS-2's receipt §4.3 give the
route.

**The one thing to know first.** Four application goals wait on one missing fact: an answer-flow
invariant carried through whole histories. `Workers.Assertions.logs_step`,
`QueueWorkers.Assertions.logs_history`, `Timeout.cleanup_keeps` and `Timeout.retries_declared` each
need the value a release note writes, and only answer flow gives it. Codex's frame-level modules
hold the per-frame facts (`src/Effect4/Laws/Machine/AnswerFlow*.lean`). `DecisionLift`
(`src/Effect4/Laws/Machine/Lift.lean`) already carries invariants through histories in five
modules. Nothing instantiates it with answer flow. That instance is the slice.

## Read first

- Seat GOALS-2's receipt (`docs/research/2026-10-13-seat-goals2-receipt.md`), §4 and §8; seat GOALS's
  receipt (`docs/research/2026-10-13-seat-goals-receipt.md`), its `FiberLocal` proposal.
- `Lift.lean` (`DecisionLift`, `StepKeeps`, `Guarded`), and its five users: `NativeHistory`,
  `NativeReplies`, `NativeHeapHistory`, `ReleaseCustody/Lift`, `PlaceFunding/Run`.
- The goals' statements and their `#why` paths, from a scratch file through the slot.

## What to build, in order

1. The producer: a `DecisionLift` whose invariant is the configuration and each fiber's
   `AnswerFlow.FrameAt`, with its local facts (each fiber's evaluation, the fork's child, the
   edits, the commands). Reuse the per-arm transports that exist.
2. The crews' instance: the answer classes of the saved callbacks (§4.3, item 2).
3. `PlaceFunding.Local` over the carried invariant, then the writer ledgers of Workers and
   QueueWorkers (§4.3, items 3 and 4), with frame lemmas generic in the row table.
4. Close the four goals. Then `shop_stages`, `jobs_step` and `rest_step` if the producer reaches them.

## Reuse first (row 376 (3))

- Before any new definition or lemma, search: `git grep` by the concept, `#why` and `#goal_impact`
  (module `ProofGraph.Why`), the registry, and `#auto_census` on the module you touch. List what
  you reused, by name and path, in the receipt. A duplicate is a defect.
- Proofs use aesop and its banks (`src/Effect4/Laws/Auto/RuleSets.lean`) where they close. Put a
  reusable step in the fitting bank, with its fixture (`AGENTS.md`, the aesop rules).
- Place every obligation first (`AGENTS.md`, "Trust"). Turn a goal into a theorem in place.

## Boundaries

- Worktree: `~/Dev/lean4-effect4-flow`, branch `seat/flow`, made by the coordinator with a
  copy-on-write `.lake`. Never copy `docs/research`.
- Edit `src/Effect4/Laws/Machine/**`, `src/Effect4/Laws/Program/PlaceFunding/**`,
  `src/Effect4/Laws/Program/ReleaseCustody/**`, the scenario modules of Workers, QueueWorkers,
  Timeout and Atomic, `Test/**` batteries of those, and the root imports at their end. Never edit
  `Test/Dogfood/Scenario.lean` (seat CLAIMS), `src/Effect4/Laws/Run/**` (seat REPLAY),
  `src/Effect4/Machine/Fibers.lean` or `src/Effect4/Laws/Program/Typed/**` (seat COUNTDOWN),
  `lakefile.toml`, `docs/core/**` or `tools/ProofGraph/Registry.lean`.
- Every `lake` and `make` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, narrow.
  Every reader of a changed definition builds before its commit. Commit by named paths. Never push
  or merge. Stop under 8 GiB free.
- Stop at a question of meaning or at about six hours. The receipt
  `docs/research/2026-10-13-seat-flow-receipt.md` (force-added) names first the one thing to know
  before merging, then the base and head, the files, the commands and results, `#axiom_audit`, the
  placements, the reused declarations, and each goal's status by `#plan_status`.
