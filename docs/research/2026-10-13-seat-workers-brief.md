# Seat WORKERS brief: the Workers application's log goal (2026-10-13)

Status: brief (history, not authority). Coordinator: the main session. Branch `seat/workers`,
worktree `~/Dev/lean4-effect4-workers`, base `fa6b133df` on `refactor/phase1-phase3`.

## The one goal

Prove `Test.Dogfood.Scenario.Workers.Assertions.logs_step`
(`Test/Dogfood/Scenario/Workers/Assertions.lean`) in place: `proof_goal` becomes `theorem`, the
statement and the placement stay. It is the last open preservation obligation of `releases_once`,
the Workers application's custody claim.

## Its placement (AGENTS.md, Trust)

1. Concept: scope lifetime and finalization (`docs/core/semantics.md`); it serves R11's custody.
2. Question: the scenario's `releases_once` through `step` and `history`; the plan shows the goal
   as a next goal of R6 and R11 (`generated/semantics.md`, the open work).
3. Reach: actual crew histories, at every command boundary; built by `Api.Author.build (crew total)`.
4. Not established: no host behaviour, no release order beyond the log's debits.
5. Unlocks: `releases_once` proved, so the Workers application rests on no goal.

## The route (seat FLOW's receipt, §5; read it first)

`docs/research/2026-10-13-seat-flow-receipt.md` §5 and §8 give the route in four steps:

1. Adapt the crew's answer-class model to `FrameFlow`: Codex's `MachineWorkersSlots` (`World`,
   `Kind`, `CodeAt`, a saved `Edge`), in the main checkout's
   `~/Dev/lean4-effect4/docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean`
   (untracked; read it there). The world is `worldOf state id := ⟨id, state⟩`.
2. Prove `NativeFlow` for it: iteration and delivery facts are the bulk; structural facts reduce
   through `FrameFlow.fields` and `FrameFlow.replace`.
3. The writer ledger: the count of `nat i` in the `released` cell, a reservation per pending
   release of acquisition `i`, credits by `ReleaseTrace.releaseAt`. Reuse
   `PlaceFunding.action_debit`, `countdown_debit`, `iteration_debit`, `Evaluation.of_debits`, and
   `LocalOn` with `Q := Flows`.
4. `logs_step` from `PlaceFunding.LocalOn.history_funded` with `NativeFlow.decision_lift`.

The producer is landed: `AnswerFlow.Commands.step` (`src/Effect4/Laws/Machine/AnswerFlowRun.lean`),
`PlaceFunding.NativeFlow.history` and `PlaceFunding.LocalOn.history_funded`
(`src/Effect4/Laws/Program/PlaceFunding/Flow.lean`).

## Rules

- Reuse first (decisions row 376 (3)): search the registry, the proof graph and the aesop banks
  before a new definition or lemma; the receipt lists what was reused. A duplicate is a defect.
- Work only in the worktree. Edit only `Test/Dogfood/Scenario/Workers/*`, new modules beside them,
  and new modules under `src/Effect4/Laws/Program/PlaceFunding/` if a general fact belongs there.
  Root imports (`src/Effect4/Laws.lean`, `Test/All.lean`) only by appending at the end.
- Build through the slot script: `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`.
  Never a bare `lake build`; never `lake build Test`.
- Proofs: aesop and its banks where they close; `simp only [...]`; no `simp_all`, `first`, `try`.
  Trap: outside `NativeCommands`'s import closure, do not run `fun_cases driveStep`; use `cases`,
  `simp only [driveStep]` and `split`.
- Audit each touched module with `#axiom_audit` at `[propext, Quot.sound]`.
- Commit on `seat/workers` by named paths. Never push. Never edit `docs/core/decisions.md`.
- If the goal is out of reach in the time, land the proved steps and say exactly what remains.

## The receipt

`docs/research/2026-10-13-seat-workers-receipt.md` (force-added), first the one thing to know
before merging, then base and head, changed files, commands and results, axiom output, open
obligations, and whether any evidence is bounded.
