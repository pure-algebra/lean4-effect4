# Actual scope-add custody receipt

Both scope-add command clauses preserve the concrete credit bound.
Whole-run custody preservation remains open.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the scope-add command clause of `Workers.Assertions.releases_step`.
Reach: actual native loop commands with the selected scope-add callback, fiber, and pending command suffix.
Limit: open scope-add requires distinct scope-entry keys and a fresh finalizer key.
Unlock: `Workers.Assertions.scope_add_custody_command` consumes both open and closed cases and derives the release-debit assertion.

`scope_add_closed_loop_funded` retains credit in the actual closing-exit response.
`scope_add_open_loop_funded` transfers active credit into the actual keyed scope entry.
The open clause consumes `ControlWeights.replace_sum` through `scope_update_credits`.
The command changes no trace registrations or release starts.
The pending drain and deliver commands carry no release credit.

Base: `b74ebab6f`.
Previous head: `11931a22`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` exits zero.
The audit measures 441 declarations within `[propext, Quot.sound]`, three planned goals, and two declarations modulo those goals.
The original three preservation goals remain unchanged.
The custody model check exits zero and audits the law modules without planned goals.
Its retained one-job checks remain finite.
No machine behavior changes.
The coordinator defers behavior gates until the major structures land.
No push occurs.
