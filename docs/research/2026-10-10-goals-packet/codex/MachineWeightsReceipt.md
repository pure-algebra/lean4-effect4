# Keyed replacement receipt

The equality requires distinct keys and an existing selected record.
It does not establish those premises.

## Placement

Concept: scope-lifetime-finalization, R11, at most once per registration.
Question: helper of `Workers.Assertions.releases_step` and its registration custody clause.
Reach: one keyed list replacement and a natural-number weight.
Limit: it establishes no invariant, source identity, progress or host behavior.
Unlock: `ReleaseCustody.Control.update_credits` transports credits through the actual fiber update.

## Evidence

Base: `b74ebab6f`.
Source: `Effect4.Machine.ControlWeights.replace_sum`, `src/Effect4/Laws/Machine/ControlWeights.lean`.
The narrow build of `Effect4.Laws.Program.ReleaseCustody.Control` passes and consumes this rule.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineWeights.lean` exits zero.
The audit measures 5 declarations, zero planned goals, and zero declarations modulo planned goals.
Its ceiling is `[propext, Quot.sound]`.
The command changes no machine behavior.
The coordinator defers behavior gates until the major structures land.
No push occurs.
