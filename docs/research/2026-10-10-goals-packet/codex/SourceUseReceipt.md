# Actual source-use probe

The actual Atomic and Workers constructor probes compile and pass the axiom audit.
They distinguish source occurrence from dynamic registration uniqueness.
No uniqueness theorem is proved by this probe.

- Concept: scope-lifetime-finalization, R11.
- Role: preservation.
- Consumers: the existing `FinalizerRun.once_placed_pushes_once` and `Workers.Assertions.registrations_step` obligations.
- Evidence: checked source headers, exact callback equations and a source-ownership control.
- Base: `349778407e218997f5a359e2b17b903fb1f46ea8`.

## Checked source facts

`Test.Dogfood.Scenario.SourceUse.atomic_header` in `Test/Dogfood/Scenario/SourceUse.lean` checks the first shop request's actual finalizer point.
It quantifies over every environment and positive compile budget.
The header retains the finalizer address `[1, 1, 1, 1, 0, 0, 0]`.
`atomic_push` applies the actual frame rule at that address.
The rule records the push, retains the original frame and executes its body.

`worker_header` in that file checks the first acquisition of the actual Workers crew at every job count.
`worker_acquire` retains its callback while running the acquisition child.
`worker_registration` gives the exact matching scope registration and response callback.
`worker_registered` shows that the successful response produces a success rather than another registration.
The equations quantify over every environment, context, scope and acquired value.

`atomic_duplicate_stack` shows that the existing source ownership predicate permits two copies of the same owned residual.
This control asserts no reachability and refutes no original history theorem.
It shows why source ownership alone cannot establish occurrence uniqueness.

## Required invariant

The existing machine fields need an unspent registration count together with the recorded registration count.
Their sum must be at most one for a once-placed source.
The count distinguishes active code from the future callbacks of saved frames.
A saved frame's copied body already executes elsewhere and must not be counted twice.
Atomic spends its opportunity at the finalizer frame push.
Workers spends its opportunity at the scope registration.
The subsequent response callback retains cleanup custody, without another registration opportunity.

Future source opportunities follow actual callback child addresses, rather than every enclosing point's address.
The count includes unlaunched race programs, queued resumptions, countdown callbacks and captured finalizer bodies.
The existing GuardState and GuardQueue retain parked and overwrite-command correlations with the target's full stack.
No new stored program or execution representation is required.
The coordinator authorizes strengthening the existing CodeAt producer correlation.

The original once-placement goal quantifies over all source, tables and reachable decisions.
The checked heap source fragment alone cannot discharge that universal goal.
Its excluded generators, layers, definition invocation and call heads require separate control-path reasoning.
No original scenario premise changes.

## Stage boundary

`Atomic.Store.shop_stages` additionally needs source-address assertions about captured values and cell aliases.
The existing SourceScope relation retains addresses and lexical lengths, without those values.
The actual window, account and cleanup handles, plus the saved admission answer, must follow their callback slots.
The existing Stage assignment can carry the request phases through the actual writer and interruption clauses.
Local decision coherence and deposit laws do not establish that full history transport.

## Checks

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceUse` passes; the final build measures 2.3 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceUseAudit.lean` passes.
- The audit reports 14 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
- `git diff --check` passes.
- No original scenario statement or planned goal changes.
