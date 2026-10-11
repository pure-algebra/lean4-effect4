# Timeout token and command custody receipt

The original Timeout goals remain open.
This slice checks the single token class assertion and its actual command consumers.
The full native evaluator and reached-history assembly remain required.

## Placement

Concept: host-session-protocol.
Requirement: R6.
Claim: `Test.Dogfood.Scenario.Timeout.stale_never_applies`, clause four.
Reach: the actual compiled Timeout source and native machine fields.
Body assertion: membership in a fixed list of applied successful reply values.
Evidence kind: universal Lean proofs over the stated inputs.
Consumer: the concrete command assertion, then the existing Lift command and decision laws.

`HostTimeoutState.successful_root` reads membership from the actual stored root exit.
Path: `Test/Dogfood/Proofs/HostTimeoutState.lean`.
The reached-history consumer still owes the complete assertion at every accepted prefix.

`HostTimeoutStateSteps.resume_state` checks the actual token-matched resume command.
Path: `Test/Dogfood/Proofs/HostTimeoutStateSteps.lean`.
Its source stack and queued reply share the same immutable token entry.
GuardState excludes an exited parked fiber.
The same module checks load, start, interrupts, publication, finish and exitDone.

`HostTimeoutRaceSteps.race_observer_state` retains the selected exit and cleanup body.
Path: `Test/Dogfood/Proofs/HostTimeoutRaceSteps.lean`.
`HostTimeoutRaceSteps.race_observer_commands` classifies the actual newly queued resume.
`HostTimeoutRaceSteps.begin_race_state` classifies the actual fresh race token and its entrants.

`HostTimeoutQueue.tail_transport` protects the pending tail using GuardQueue's unique command owners.
Path: `Test/Dogfood/Proofs/HostTimeoutQueue.lean`.
It uses the coordinator's existing StackLinks and StackLinksAway carriers.
It creates no new stack carrier or program representation.

## Single token correlation

The proof-only list records body, unit or arbitrary data at each existing machine token.
Its length equals the actual machine token supply.
Its extension retains every earlier token entry.
A parked current and its saved stack use the recorded class.
A queued resume uses that same class.
Native race allocation appends one body entry at the actual fresh token.

A conditional assertion about the current park alone loses the older race token's class.
Race registration leaves the host active before registrationDone parks it on that earlier token.
The one class list retains the correlation across this interval.
The list changes no runtime field, admission predicate or original goal premise.

CodeAt retains a fixed body list throughout its callbacks.
The final history assertion must quantify over lists containing the current applied reply prefix.
It must not widen CodeAt's callback quantification after a reply arrives.

The source admits only daemon race entrants, so stored children remain empty.
This fact excludes middleware's tracked-child exit program while allowing installation decisions.
Wake tasks and scope commands lie outside the concrete source assertion.

## Verification

Base: `a3e4a5407`.
Head: the commit containing this receipt.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutQueue`.
Result: success, 1090 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Result: 1034 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.
`git diff --check` passes for the landed paths.

Changed files:

- `Test/Dogfood/Proofs/HostTimeoutState.lean`.
- `Test/Dogfood/Proofs/HostTimeoutStateSteps.lean`.
- `Test/Dogfood/Proofs/HostTimeoutRaceSteps.lean`.
- `Test/Dogfood/Proofs/HostTimeoutQueue.lean`.
- `docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
- This receipt.

No runtime, source program, compiler or host reader changes.
The coordinator owns the outside implementation gates.
No outside implementation comparison runs in this proof slice.
No push runs.
The unrelated RaceFirst edit, KernelRfl helper and coordinator dependency copies remain excluded.
The in-progress HostTimeoutParkSteps module remains outside this landing.

## Remaining obligations

The actual evaluator still needs external, sleep, yield and countdown park class consumers.
The actual command assertion still needs registration, launch, cancellation and countdown observer consumers.
The complete command and decision closure must feed the actual reached-run ledger.
The original successful-body clause then combines that ledger with HostAppliedObservation.applied_body_seen.
The retry and cleanup goals retain their original approved statements and remain open.
These proofs establish neither progress nor completion of a live race.
They establish no exact reference count or cleanup log correspondence.

## Coordinator dependency copies

The coordinator authorizes byte-for-byte copies for local checking.
These paths and hashes identify the local dependencies excluded from the commit.

| Path | SHA-256 |
| --- | --- |
| `src/Effect4/Laws/Program/ReleaseCustody/CommandStacks.lean` | `7a24d5f6a40d2119cb8852f4266ef5a2eb89166185a489160297cc05ff3c230b` |
| `src/Effect4/Laws/Program/ReleaseCustody/Sequencing.lean` | `03dd16b7905a613be0e101313e219a9afc925ca4ad64ea5fbf932103d017f0b8` |
| `src/Effect4/Laws/Program/ReleaseCustody/FrameDebit.lean` | `9d20585af7e4ad651951074b6500dbf919aa89c6b529ba9d19d3f7f4936b8388` |
| `src/Effect4/Laws/Program/ReleaseCustody/CausePop.lean` | `a52d27671d01c1bd4c354b2c938ad0418b1fc2e1f58c6241c6d60b2c6490b4ca` |
| `src/Effect4/Laws/Program/ReleaseCustody/Pop.lean` | `2ed40290b0883d3cc59da7829243c99c2d5de32a310cffe6bd3b988f31920367` |
| `src/Effect4/Laws/Program/ReleaseCustody/Producers.lean` | `b610ea6d9372ef33ce8f378f04f3b94371dafca409d22d2b03755da7a86cf4a9` |
| `src/Effect4/Laws/Program/ReleaseCustody/Evaluation.lean` | `5f51af6b8a21bb066bec366e8a488ab6d97ada550759a0e36c5f6cca6d413f0c` |
| `src/Effect4/Laws/Program/ReleaseCustody/Control.lean` | `5256d506917bf22f2874358696883c52dbb34db94ac1695fc7e492fe5d881326` |
| `src/Effect4/Laws/Program/CompileInduction.lean` | `add02f14cd264646bbe8865c41b62e0e0daba7eff4a07ed85a34c42f8c7f0cd4` |
| `src/Effect4/Laws/Program/ReleaseCustody/Names.lean` | `2ddb9feb308fe7063e1b3d3604da6a65753302a24fafe8a0852ac348e5b45216` |
| `src/Effect4/Laws/Program/ReleaseCustody.lean` | `221fd778466a93c38d57e324b8001309572c0c19d0e1d57af81047a273d38752` |
| `src/Effect4/Laws/Program/ReleaseTrace.lean` | `7329fa5ac90ab8efefdaa93214678045245410e4e9e94a03f9cdd6d4bf5442bf` |
| `src/Effect4/Laws/Program/ControlSteps.lean` | `c3cb80b80a57662c12f338f9791d6d08cba981ad534655da13288cc4b5e1e311` |
| `src/Effect4/Laws/Machine/ControlSteps.lean` | `37fb63dfdcbd595ab217e98af742a6f933e2ccc447d522e6ff179f96d64902c8` |
| `src/Effect4/Laws/Machine/ControlWeights.lean` | `53c6117c7be7b4d7da5e0b610c8f86c08d37332ad0faa715a2b75cf6de88389a` |
| `src/Effect4/Laws/Program/ReleaseCustody/CommandStackSteps.lean` | `2b89e660bfccd9a198465fcb3788c8355b1cd7c4a99b6733e71f387dcb27647e` |
