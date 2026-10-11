# Actual close-iterator custody receipt

The actual close iterator preserves the concrete credit bound.
Whole-run custody preservation remains open.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the close-iterator command clause of `Workers.Assertions.releases_step`.
Reach: an actual selected nonempty sequential close iterator, with its captured reasons and pending command suffix.
Limit: delivery and source-shaped continuation closure remain open.
Unlock: `Workers.Assertions.close_seq_custody_command` derives the release-debit assertion from the residual credit bound.

`close_seq_start` exposes the exact existing native iterator result.
`close_seq_command` now consumes that equation.
`close_seq_loop_funded` transfers the head credit into the selected finalizer and the tail credit into its pushed iterator frame.
The actual command emits no registration or release-start event.
No scope-key premise is needed for this command.

Base: `b74ebab6f`.
Previous head: `b2507e1a`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` exits zero.
The audit measures 511 declarations within `[propext, Quot.sound]`, three planned goals, and two declarations modulo those goals.
The original preservation goals remain unchanged.
The custody model check and ReleaseCustody audit both exit zero.
The selected one-job checks remain finite.
No machine behavior changes.
The coordinator defers behavior gates until the major structures land.
No push occurs.
