# Applied receipt observation

The exact applied-body observation reader is proved. The native returned-body invariant remains open.

## Placement

Concept: host-session-protocol. Requirement: R6.
Consumer: the fourth clause of `Timeout.stale_never_applies` in `Test/Dogfood/Scenario/Timeout.lean`.
Reach: every recorded fetch script, including raw rows, arbitrary command budgets, and incomplete commands.
This proof establishes no returned-value provenance, retry bound, finalizer progress, or host agreement.

## Change

Base: `60c95b062` with the source-root integration.
Add `Test/Dogfood/Proofs/HostAppliedObservation.lean`.
Its association ledger retains each actual binding record and each receipt's declared external row.
The existing key ledger supplies receipt uniqueness.
`stored_receipt` proves that the observed stored payload is that key's exact accepted receipt.
`body_fate` connects successful applied bodies to actual held calls.
`applied_body_seen` reads the fetch table and proves that the timeout observation contains the corresponding answered HTTP call.
The theorem imposes no restriction on the script's moves.

Narrow `HostJournal.lean` to import `Timeout.Model`, avoiding a cycle when the completed reader serves the timeout claim.
Register the new module in `Test/All.lean`.

## Checks

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostAppliedObservation` passes with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/HostAppliedObservationAudit.lean` passes.
The audit checks 39 declarations within `[propext, Quot.sound]`, with zero planned goals and zero dependent assemblies.
The exact output is `HostAppliedObservationAudit.out` beside this receipt.
`git diff --check` passes.

## Gates and remaining work

This proof-only change reaches no additional behavior gate.
The native value-flow proof must still show that each returned body belongs to the current applied-body prefix.
The retry and cleanup scenario obligations remain open.
