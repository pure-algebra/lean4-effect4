# Actual command custody receipt

The registration and release-start command clauses are proved.
Whole-run custody preservation remains open.

## Placement

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: helpers of `Workers.Assertions.releases_step`; that planned goal keeps its original statement.
Reach: actual native commands on an existing fiber with distinct IDs, unchanged pending suffix, and explicit yield-budget premises.
Limit: these clauses establish no whole-command preservation, source-use uniqueness, progress or external host behavior.
Unlock: release-start consumes concrete configuration credits; its Workers consumer needs no separate available-credit assumption.

## Changes

`ReleaseCustody.Control` counts scope entries, active code, remaining stack callbacks, queued resumes, and unlaunched race programs.
It includes pending resume commands at command boundaries.
The top scope-add callback reserves credit according to its actual response.
Lower callbacks retain their reservations.
`registration_loop_funded` adds the trace registration and its credit together.
`release_loop_funded` spends the actual active release credit when the trace records a release start.
`compile_credits` and `load_funded` cover every native source and compile fuel.
Workers consumes the clauses through its existing admitted history and Guard's distinct fiber IDs.
`close_seq_command` records the actual iterator transfer and unchanged release count.

## Evidence

Base: `b74ebab6f`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCustodyModel.lean` exits zero.
That audit measures 336 declarations within `[propext, Quot.sound]`, zero planned goals, and zero declarations modulo planned goals.
The selected finite one-job checks cover load, parked state, and interrupt fuel cuts 1, 8, 24, 64, and 1000.
Both source identities satisfy starts plus custody at most registrations at those cuts.
These finite checks do not establish preservation between arbitrary commands.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` exits zero.
Its audit measures 431 declarations, three planned goals, and two declarations modulo those goals.
The universal observation reader remains modulo `registrations_step`, `releases_step`, and `logs_step`.
The separate ReleaseCustody audit passes with no planned goals.

## Open work

Scope-add must transfer credits between the actual scope store and callback response.
Scope close must transfer the consumed entry into actual close-chain control.
Other actual commands must preserve the concrete projection under source-shape premises.
Arbitrary synthetic store-program names can hide foreign code; this projection does not admit them without a source-shape premise.
Distinct scope-entry keys remain a premise until their reachable-store law lands.
No machine behavior changes.
The coordinator defers behavior gates until the major structures land.
No push occurs.
