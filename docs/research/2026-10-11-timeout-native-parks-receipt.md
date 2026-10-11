# Timeout native park receipt

The original Timeout goals remain open.
This slice checks the actual external, sleep, yield, countdown and race registration consumers.
The ordinary evaluator cases and full command history still remain.

## Placement

Concept: host-session-protocol.
Requirement: R6.
Claim: `Test.Dogfood.Scenario.Timeout.stale_never_applies`, clause four.
Reach: actual native evaluator results under the stated source frame, active park and live exit hypotheses.
Evidence kind: universal Lean proofs.
Consumer: the complete native evaluator assertion, then the existing command and decision Lift laws.
Path: `Test/Dogfood/Proofs/HostTimeoutParkSteps.lean`.

`external_park_state` classifies the actual fresh body token and pending void registration.
It obtains no host value at registration.
`sleep_park_state` classifies the actual fresh unit token, timer waiter and sleep cancellation frame.
`yield_park_state` classifies the actual fresh unit token and its matching queued unit resume.

`countdown_state` checks the actual walk's immediate and parked branches.
`await_park_state` consumes that assertion at the actual await-all source head.
Its fresh arbitrary-data token retains the body continuation beneath the discarded countdown result.
The actual pending mode is exitsValue, and the actual observer refers to that same token.

`race_park_state` checks actual race registration without allocating another token.
It retains the earlier race body token while returning launch and registrationDone commands.
The previous slice checks body-token allocation at beginRace and the selected-body observer resume.

`dispatcher_enqueue` checks the actual priority insertion of old and new task assertions.
`configuration_modify` and `observer_fiber` retain the actual fiber fields during countdown observer attachment.
All assertions use the existing single token class list.
No runtime, source, admission or original theorem premise changes.

## Verification

Base: `4715d428`.
Head: the commit containing this receipt.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutParkSteps`.
Result: success, 1091 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Result: 1076 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.
`git diff --check` passes for the landed paths.

Changed files:

- `Test/Dogfood/Proofs/HostTimeoutParkSteps.lean`.
- `docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
- This receipt.

Coordinator dependency hashes remain recorded in `docs/research/2026-10-11-timeout-command-custody-receipt.md`.
The dependency copies remain outside this commit.
The unrelated RaceFirst edit and KernelRfl helper remain excluded.
The in-progress HostTimeoutLocalSteps module remains outside this landing.
No push runs.

This slice changes proofs only.
It changes no runtime, compiler, program or host reader.
The coordinator owns the outside implementation gates.
No outside implementation comparison runs in this slice.

## Remaining obligations

The complete ordinary evaluator assertion must retain every returned frame and store assertion.
RegistrationDone, launch, cancellation and countdown observer commands still need the complete command assertion.
The full command, task and decision closure must reach Run.Frame.HistoryOf at actual accepted prefixes.
The original success clause then combines root membership with HostAppliedObservation.applied_body_seen.
The approved retry goal and cleanup goal remain open.
These safety assertions establish neither progress nor completion of a live park or race.
They establish no exact counter or cleanup log correspondence.
