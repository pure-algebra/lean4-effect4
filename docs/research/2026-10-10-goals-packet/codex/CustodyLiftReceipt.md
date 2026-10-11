# Custody lift extraction

The command obligation remains open. A checked control refutes its current unrestricted internal premise.
The application statements remain unchanged.

## Placement

Concept: scope-lifetime-finalization. Requirement: R11.
Consumer: `Workers.Assertions.releases_step` in `Test/Dogfood/Scenario/Workers/Assertions.lean`.
Scope: native command custody and admitted histories. No progress or host agreement follows.

## Change

Base: `26a36e4b1`.
Move the existing assertion and scheduler proofs into `src/Effect4/Laws/Program/ReleaseCustody/Lift.lean`.
Keep their declarations and statements unchanged.
Import this lower module from `Execution.lean`, alongside the checked native pop laws.
This removes the prospective import cycle between execution assembly and command proofs.

## Verification

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers.Assertions` passes: 1076 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CustodyLiftAudit.lean` passes.
The audit checks 343 declarations within `[propext, Quot.sound]`, with two assemblies modulo one planned goal.
The output is `CustodyLiftAudit.out` beside this receipt.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CustodyCommandControl.lean` passes.
Its `contract_refuted` theorem proves the missing correlation, using an arbitrary parked fiber and resume command.
That configuration satisfies `Ready` with zero registrations. The resume creates one unfunded callback credit.
It is not an admitted history. This control establishes no runtime defect.

## Next

Retain command ownership and token facts from `GuardState`, `GuardQueue` and `RegistrationQueue`.
Connect overwrite commands and parked replies to their actual saved frame positions.
Yield parking needs special care: it stores unit before parking, and its queued resume also returns unit.
A mere parked-stack capacity premise does not follow for arbitrary synthetic frames.
Replace the refuted internal command statement before using it to close any application claim.
The original scenario claims and the owner-approved timeout contract remain unchanged.

## Gates

This extraction changes no runtime or generated input. It reaches no additional behavior gate.
The previously recorded behavior pass remains the relevant external evidence.

## Checked repair of the proof boundary

Remove the refuted `command_custody` planned statement and its arbitrary-state `decision` assembly.
Place the remaining obligation at `Execution.history`, over actual admitted histories.
The original `Workers.Assertions.releases_step` statement stays unchanged.
It extends the actual history before reading custody at the next machine.
This is an internal proof repair, not a completed custody proof or an application amendment.

The narrow build passes with 1077 jobs.
`CustodyHistoryAudit.lean` audits the affected modules and their Workers consumer.
`CustodyHistoryAudit.out` records its exact result.
The retained counterexample still compiles after the repair.
All checked producer, stack, scope-store and scheduler-edit lemmas remain available.
The new command decomposition must prove saved-frame and resume correlation before the history endpoint closes.
