# Complete command custody census

The complete assembly uses the existing `Machine.Lift.DecisionLift`.
The command obligation and outside-loop obligation remain planned.
The original `Workers.Assertions.releases_step` consumes this assembly without changing its statement.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: `ReleaseCustody.Execution.command_custody` and `outer_custody` serve the workers release-debit clause.
Reach: actual native commands, evaluator results, admitted host decisions, task snapshots and resumable fuel cuts.
Limit: the assembly remains conditional on both planned obligations.
Unlock: `ReleaseCustody.Execution.history` supplies concrete custody to the original release-debit consumer.

## Concrete assertion

`Ready` reads actual machine fields.
It includes the existing fork ledger allocation invariant.
Scope-entry keys are unique and below the actual name supply.
The existing `Stores.ScopeKeysFresh` bounds finalizer registration keys.
Pending resumes use exits, void, or the native saved-exit restore continuation.
Dispatcher resume code carries no foreign cleanup credit.
The funded inequality includes current code, saved callbacks, scope entries, race entrants and pending resume commands.

`Lift.I` is the funded inequality with its actual pending commands.
`Lift.O` states zero cleanup credit for the actual drained task snapshot.
`Lift.J` is `Ready`.
The outside-loop contract uses the real supplied table and the exact session admission predicate.
These predicates contain no second machine carrier or assumed release bound.

## Every command

The list comes from the arms of `Machine.driveStep` in `src/Effect4/Machine/Fibers.lean`.

| Command | Required transfer | Current evidence |
| --- | --- | --- |
| `evaluate` | Change running metadata and enqueue the loop | Metadata transfer remains open |
| `loop` | Interrupt top, operation count, forced yield, native evaluator, settlement | Registration, release start, scope-add, scope-close, iterator and stored-body clauses are checked |
| `deliver` | Evaluate without loop charging; settle the response | Actual scope-add delivery is checked |
| `resume` | Consume the pending answer credit; unpark and replace current code | General answer transfer remains open |
| `launch` | Transfer one race entrant to its fresh child | Fork and race sum transfer remains open |
| `enrollRace` | Attach or fire the actual race observer | Observer transfer remains open |
| `registrationDone` | Replace buffered race response or push its cancel frame | Race response transfer remains open |
| `interruptTarget` | Record the cause; preserve or discard active credits | Interruption transfer remains open |
| `afterInterrupt` | Replace current with zero-credit await code | Await response transfer remains open |
| `raceCancel` | Enqueue interrupts and the remaining walk | Command-suffix transfer remains open |
| `trackChild` | Change child and observer metadata | Metadata transfer remains open |
| `observe` | Fire one existing observer; transfer countdown response | Native pending shape excludes stored foreign callback credit; preservation remains open |
| `exitDone` | Clear the exited fiber | Clearing can discard credits; preservation remains open |
| `closeParAwait` | Push the close-done iterator and await code | Zero-credit administrative callback transfer remains open |
| `link` | Add an administrative finalizer using fresh names | Scope allocation and key preservation remain open |
| `finish` | Run the exit observer sequence before clearing | Observer fold and clearing remain open |
| `drainDue` | Move native zero-credit resumes to commands or dispatcher tasks | Store resume and dispatch transfer remain open |
| `wake` | Move the named timer batch to due work | Native zero-credit resume preservation remains open |

## Evaluator cuts

The source compile projection is checked for every native effect and point.
The stored-program interpretation projection is checked for every existing `ProgName` constructor.
Stored continuations reserve each success and failure arm separately.
The `withFiber` fallback reserves stored bodies and foreign finalizers before invoking `suspendBody`.
Scope close transfers entries to an empty, singleton, sequential, or parallel residual program.
The sequential iterator transfers its head to active code and retains the remaining order.
Stored mask transfer accounts for the actual restoring frame.
Remaining evaluator cases include general continuation pops, finalizer programs, native actions, async parks and loop callbacks.

## Forced-yield correction

The earlier stack sum counted a pending scope-add twice beneath an injected constant continuation.
The constant frame reserved the scope-add program.
The lower scope-add callback also reserved the same foreign finalizer.
The corrected stack projection follows the stored constant continuation before measuring lower response custody.
The response projection follows constant continuations too.
The minimal equation fixture retains the earlier sum and checks the corrected calculation.
This correction changes the assertion only; it changes no machine behavior.

## Outside the command loop

`DecisionLift` exposes dispatcher drain, task emission, task entry, yield verdict and interruption edits.
It also exposes middleware, clock responses and host-answer preparation followed by the first resume.
`outer_custody` states those exact existing fields, with `command_custody` as an explicit premise.
No observer ownership or source closure is silently assumed.
Native pending and dispatcher shape preservation remain part of the named obligations.
