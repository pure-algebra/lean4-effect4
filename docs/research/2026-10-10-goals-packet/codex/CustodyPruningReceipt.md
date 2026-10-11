# Cleanup proof graph after history closure

Atomic and Workers cleanup each retain one log-writer obligation.
Their registration bounds now follow from actual admitted histories.

Base: `7092cbe2a`. Head: the commit containing this receipt.
The Atomic connector is the checked patch retained by that base commit.

## Placement and scope

Concept: scope-lifetime-finalization, R11.
Consumers: the original `Atomic.cleans_once` and `Workers.releases_once` claims.
Atomic retains its original shop, six request identities, compile budget and admitted histories.
Workers retains all job counts, compile budgets and admitted histories.
No original statement changes.
No result establishes cleanup progress or a host observation.

`Atomic.Cleanup.cleaned` now uses the actual source-registration theorem.
The broader `FinalizerRun.once_placed_pushes_once` remains open, but this application no longer depends on it.

The complete custody theorem supersedes the earlier isolated command cases.
A source scan checks `src`, `Test` and `tools`, ignoring comments.
It follows internal references from every retained declaration with an external consumer.
The scan identifies 23 command-case theorems outside that dependency closure.
`RetiredCustodyCases.tsv` records their names and removed blocks.
Their earlier proofs remain in Git history.
The retained command debit reader and original worker consumer both build after removal.
`Control.lean` changes from 1067 to 336 lines, removing 731 lines overall.
The retained shared accounting laws continue to serve the complete command and history proofs.

## Changed files

- `Test/Dogfood/Scenario/Atomic/Cleanup.lean`: actual source-bound connector.
- `src/Effect4/Laws/Program/ReleaseCustody/Control.lean`: remove superseded cases and repair consumer descriptions.
- `src/Effect4/Laws/Machine/ControlWeights.lean`: repair the consumer description only.
- This receipt, the removed-case table, the audit source, and their retained outputs.

## Verification

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Workers Test.Program.CommandDebit`: passed, 1180 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CustodyPruningAudit.lean`: passed.
- The audit reports 364 declarations within `[propext, Quot.sound]`, three modulo planned goals, and two planned goals.
- `Atomic.cleans_once` depends only on `Atomic.Cleanup.log_debits`.
- `Workers.releases_once` depends only on `Workers.Assertions.logs_step`.
- `git diff --check`: passed.

After the build, two consumer descriptions receive spelling corrections.
Those comment edits change no declaration or proof and require no dependent build under `AGENTS.md`.

## Remaining work

Both actual writer obligations remain open.
The other scenario and base-law obligations remain as recorded in the coordinator receipts.
Behavior gates remain scheduled after the major proof structures.
The full battery and whole-tree axiom gate are not run here.
