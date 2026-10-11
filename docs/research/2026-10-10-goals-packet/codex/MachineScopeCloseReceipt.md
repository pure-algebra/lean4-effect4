# Actual scope-close custody receipt

The actual scope-close command transfers entry credits into its returned program.
Whole-run custody preservation remains open.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the scope-close command clause of `Workers.Assertions.releases_step`.
Reach: the actual selected native action, scope entry, pending commands, and explicit yield-budget premises.
Limit: distinct scope-entry keys remain an explicit reachable-store premise.
Unlock: `Workers.Assertions.scope_close_custody_command` derives the release-debit assertion from the returned custody bound.

`scope_close_loop_funded` keeps the state-first scope close.
It covers empty, singleton, and multiple-finalizer close orders.
`fin_program_credits` checks every finalizer constructor against its foreign source identity.
`stack_credits_bounded` retains reservations below the returned close program.
The pending loop suffix remains present.

Base: `b74ebab6f`.
Previous head: `1aafd56e`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` exits zero.
The audit measures 505 declarations within `[propext, Quot.sound]`, three planned goals, and two declarations modulo those goals.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCustodyModel.lean` exits zero.
Its selected one-job checks remain finite; its law-module audit has no planned goals.
The original preservation goals remain unchanged.
No machine behavior changes.
The coordinator defers behavior gates until the major structures land.
No push occurs.
