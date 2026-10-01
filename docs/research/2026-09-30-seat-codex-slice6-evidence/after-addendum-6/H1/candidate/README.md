# H1 row 133 — uncompiled candidate and adversarial controls

The normal terminal witness is addressed, but **do not land this candidate before checking
QueueDiscardWitness.lean**. A different active fiber can deliver into a typed scope-exit callback
for an absent scope. `prepareScopedExitR` produces `Outcome.stuck`; `settle` discards the whole
queue, including the root's pending finish. The root's stale code and absent exit are unchanged,
so the proposed current-code exemption disappears. This is a concrete uncompiled counterexample
draft, not a checked stop. No halted-machine exemption or runtime repair is included.

Authority: addendum 6 at ea5b28b5, row 133. Root owns the Lean lane and all repository writes.
Input: preserved final H1 candidate under after-addendum-4/H1/candidate, with its checked old
terminal witness. `source-map.json` pins live inputs, preserved inputs, candidate outputs,
matching line blocks, declarations and probe hashes.

## Exact candidate boundary

`TerminalFiber m commands id` means a finish for id occurs in commands, or a member fiber with
that id already has an exit. `TerminalPosition` uses that at root/fiber positions and is false
at hook positions. `SavedPosition` retains the old existential middle type, `StackAccepts`, and
`InterruptProvenance`; only `TypedProg` of the current slot is conditional on nonterminal status.
`statePreds` updates exactly `preds.SavedOk`. Every other generated data clause, especially
`preds.exit`, is unchanged. `QueueOk.payload` still checks every queued finish's actual exit.

`TypedState` gains a trailing `commands := []` argument. `StepPreserves` uses exactly cmd::rest
at input and the actual r.2 at output. Initialization, decisions and completed reachability retain
the empty queue interface. All 18 command proofs remain obligations, and M6 remains at 20.
The only new source theorem is `savedPosition_of_saved`. `pending_below` receives the explicit
queue and its proof continues to read the unchanged pending-data clause.

Four source files are complete as a draft overlay; source.patch contains only those four.
The two copied test files are **not ready for application**: their old-to-new conversion helper
needs a nonterminal premise, and the terminal control has not yet been inserted. Compile the
standalone controls first, before migrating those files or preparing an integration patch.

## Terminal-command audit

Source: Machine/Fibers.lean driveStep:1846–1990; settle:1805–1826;
Laws/Program/EvaluateR.lean prepareScopedExitR/prepareIterR:307–339.

- loop and deliver read current code. A finish in the same admitted queue excludes either on
  that same fiber by owners.Nodup. Both can produce a new finish through settle.finished.
- evaluate reads the entry flags and is inert for a finish-pending fiber because finish authority
  requires running=true. Published-exit fibers are inert at its first exit test.
- resume is inert on the same finish-pending or exited fiber because both are notParked.
- exitDone requires a published exit; SchedulerState.exited makes it incompatible with a queued
  finish's running=true. It clears stack/context/observers/children without reading current code.
- afterInterrupt and closeParAwait install new current code and retain/use the stack; their own
  owner excludes a same-host pending finish. raceCancel eventually emits afterInterrupt and has
  the same owner, so it is excluded too. Their existing CommandDeliveryOk conditions remain.
- registrationDone reads its direct current registration marker and owns the race host. The
  registration-tail condition plus owners.Nodup also excludes launch/enrollRace with a pending
  finish for that race host. RegistrationState remains a distinct finite code-site obligation.
- interruptTarget can record an interrupt on a finish-pending fiber but does not run its current
  code because that fiber is running; published fibers are ignored. Existing provenance remains
  required. trackChild and observer callbacks can change bookkeeping, not the current slot.
- finish publishes the carried exit, or middleware installs its interrupt-children/restore-exit
  program and schedules re-entry. The latter's code/stack connection remains an M5/M6 dependency;
  this candidate does not assert arbitrary leftover stacks are inert during middleware re-entry.
- Global queue discard is different from these owner arguments: a worker's stuck outcome drops
  another fiber's pending finish. The supplied probe isolates that exact failure route.

## Standalone controls

TerminalPositive.lean retains all fifteen checked theorem bodies against explicit historical
OldTypedState/OldStepPreserves definitions. Thirteen new theorem drafts cover the same input
under the amended state, actual deliver output and typed finish queue, the finite successful
step, and the subsequent published-exit saved-position boundary. All 28 have axiom prints.
It does not claim the general deliver obligation or all completed-state clauses are proved.

QueueDiscardWitness.lean constructs a two-fiber machine and complete input world/state/queue.
The root is exempt only because of its typed queued unit finish. The worker's callback has
ordinary current-code and frame typing. The queue has distinct owners. The intended rfl facts
show unknownScope(0), empty output queue, and an unchanged root. Fifteen theorem drafts have
axiom prints; no production or old theorem is assumed.

## Root's serial commands

Run from /Users/pooks/Dev/lean4-effect4-slice6, one process at a time, retaining logs and exit codes.
Use the four-path source.patch only after checking its live input hashes; preserve/restore as
with H1's previous probe if the new counterexample compiles.

```
git apply --check /private/tmp/h1-addendum6/source.patch
git apply /private/tmp/h1-addendum6/source.patch
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard.RegistrationQueue Effect4.Laws.Program.Typed.Assembly
LEAN_NUM_THREADS=1 lake env lean -M4096 -DwarningAsError=true /private/tmp/h1-addendum6/TerminalPositive.lean
LEAN_NUM_THREADS=1 lake env lean -M4096 -DwarningAsError=true /private/tmp/h1-addendum6/QueueDiscardWitness.lean
LEAN_NUM_THREADS=1 lake env lean -M4096 -DwarningAsError=true /private/tmp/h1-addendum6/Axioms.lean
```

A failed proof script is not a counterexample. If the final negation of the revised
StepPreserves compiles, record its exact statement/observations and apply original brief §6.
Do not make the amended statement true by adding a transition premise, reachability condition,
blanket halted-state exemption, or protocol/runtime repair without the corresponding ruling.

## Deferred register proposal

CE-017: every queued command is checked; CE-018: observer tokens are typed by the actual delivered
payload. Preserve their exact historical falsifiers and amended refusals from the earlier H1
candidate. CE-019: “a fiber is typed by its queued finish, not by its stale code slot”, SEEDED by
the old terminal witness and REPAIRED only when H1 actually lands. No register write/status
promotion is part of this draft. A checked new queue-discard witness requires its own recorded
scope ruling before any such H1 landing.
