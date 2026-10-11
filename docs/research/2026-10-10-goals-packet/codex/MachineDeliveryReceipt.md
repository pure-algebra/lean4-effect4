# Actual scope-add delivery receipt

The actual scope-add response delivery preserves the concrete credit bound.
Whole-run custody preservation remains open.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the scope-add delivery command clause of `Workers.Assertions.releases_step`.
Reach: the actual deliver command and selected success response beneath its own callback.
Limit: remaining command cases and source-shaped continuation closure remain open.
Unlock: `Workers.Assertions.after_add_custody_command` consumes the concrete credit transfer and derives the release-debit assertion.

`after_add_code_credits` covers unit, closing-exit, and malformed responses.
`after_add_start` pops the actual callback and preserves its lower stack.
`after_add_deliver_funded` transfers response credit into the returned program and retains lower reservations.
The actual native success path uses `exitScoped` with its existing empty table.
The callback is independent of that table; this slice changes no machine behavior.
The outer evaluator keeps the actual supplied row table.

Base: `b74ebab6f`.
Previous head: `0d4fd496`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1064 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` exits zero.
The audit measures 544 declarations within `[propext, Quot.sound]`, three planned goals, and two declarations modulo those goals.
The original preservation goals remain unchanged.
The custody model check exits zero and its law-module audit has no planned goals.
Its selected one-job checks remain finite.
The coordinator defers behavior gates until the major structures land.
No push occurs.
