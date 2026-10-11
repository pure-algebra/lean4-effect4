# Actual source registration bounds

The full admitted-history bound checks at the actual Workers and Atomic source sites.
The original broader placement goal remains open.
Apply the ControlWeights patch from `c46d2933` before importing these modules.

- Proof role: preservation.
- Evidence status: proved.
- Concept: scope-lifetime-finalization, R11.
- Consumers: `Workers.Assertions.registrations_step` and `Atomic.Cleanup.cleaned`.
- Base: `c46d2933`.
- Shared dependencies: CompileInduction from `cda8ec26`; Moves and Footprint from `7c69f880`.

## Changes

`SourceOpportunityCommands.command_debit` covers every actual command constructor.
The observer clause retains fail-fast interruption and the waiter's saved state.
The finish clause covers middleware, publication, observers and cleared stacks.
The command proof consumes the existing source ownership and ForkLedger invariants.

`SourceOpportunityHistory.budget_decision_lift` uses the existing machine decision lift.
It covers tasks, yields, interruption, middleware, clocks and actual reply preparation.
`history_budget` retains the combined recorded and live source budget over the original `Run.HistoryOf`.
It introduces no execution carrier or new scenario premise.

The generic bound requires the checked lexical fragment, clear finalizer children, clear loop children, sequential allocation and no authored race.
The actual source censuses discharge these restrictions for both Workers acquisitions and all six Atomic requests.
Workers retains every job count and compile budget.
Atomic retains every compile budget and actual admitted history.
The counting readers bound actual pushed acquisition frames and onExit frames by their consumed source reservations.

Structural Nat-list equality instances keep the counting proofs within the permitted axiom ceiling.
The first audit rejects the default equality shortcut because it reaches Classical.choice.
The repaired audit passes.

## Checks

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity` succeeds with 1090 targets.
The history module takes 3.1 seconds; its application reader takes 3.3 seconds.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceOpportunityHistoryAudit.lean` succeeds.
The audit checks 141 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.

## Integration

Replace the original Workers registration goal with `workers_registrations_once` applied after `Assertions.history_step`.
The Atomic reader supplies the actual six-path push bound without the broader placement goal.
Its inline classifier unfolds to `FinalizerRun.registeredAt` at the same request path.
The coordinator owns scenario proof edits and root imports.

## Open work

`FinalizerRun.once_placed_pushes_once` covers broader source syntax and raw reachable machines.
This restricted application endpoint does not prove that broader statement.
Atomic cleanup-log writes still need allocation identity and a finalizer-start debit.
Workers log writes need their acquired identity and the corresponding release-start debit.
Source length and source occurrence alone do not prove those value facts.
No progress, runtime comparison or host observation follows from this invariant.
