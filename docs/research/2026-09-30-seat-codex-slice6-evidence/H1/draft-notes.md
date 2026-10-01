# H1 draft: queue conditions and observer gap

The source tree is unchanged. All files in this directory are uncompiled candidates. The
coordinator owns compilation after E and must decide the brief's stop rule if the observer
falsifier checks. Do not install a stronger queue condition silently to make that probe pass.

## Artifacts and installation boundary

- `GuardCore.candidate.diff`: exactly eight definition signatures in
  `src/Effect4/Laws/Program/Guard/Core.lean`. It generalizes `taskKeys`, `internalKeys`,
  `InternalKeysBelow`, `bucketKeys`, `fiberKeys`, `commandKeys`, `ActiveAt`, and
  `commandOwner` over code and, where needed, saved-frame and event types. Bodies and native
  callers are unchanged. `wakeKeys` is already generic and `observerKeys` reads no code.
  The machine fields are still the Effect4 stores/context/alphabets, as required by both
  native and reference instances. This does not generalize a code-inspecting function.
- `PendingBelow.candidate.lean`: `Effect4.Program.Typed.pending_below`, using the checked
  research proof without changing its statement. Install the theorem after `TypedState` in
  Assembly; omit the standalone import/namespace/axiom-print wrapper. It follows from
  generated `PendingOk` and `WorldValid.tokenBound` and requires no new invariant field.
- `ObserveGap.candidate.lean`: standalone after E. It contains the exact proposed H1 queue
  clauses as `ReviewedQueueOk`, a reference command authority, and a falsifier candidate.
  It parameterizes the resume code-site condition by `noRace : RProgram → Prop`. Since its
  input is `observe`, the counterexample does not depend on that parameter. This parameter
  is proof isolation, not a proposed final public signature.

For installation after the stop ruling, `InternalKeysBelowR` should be an abbreviation of
`Guard.InternalKeysBelow`, and the queue should call generalized `Guard.commandKeys`,
`Guard.commandOwner`, and `Guard.ActiveAt`. Keep the bound in `StepPreserves`' input and
output, separately from `TypedState`, as the amended statement requests. The output queue
must use the output machine: `QueueOk root w' result.1 result.2`. Queue keys include both
resume commands and the resume/countdown keys stored in observe commands; checking only
resume commands would lose the native guard's meaning.

`QueueOk root w m commands` has five fields: every `RCmdOk (preds root) w command`, authority,
unique command owners, reserved keys (below `m.nextToken` and disjoint from parked external
requests), and no forbidden command code sites. `QueueFresh` is the `below` part of reserved
keys; duplicating it as an additional field is unnecessary. No 18-command preservation proof
is part of this work.

## Settled reference-specific observations

Use `Sched.externalRequestR` and `Sched.requestOfR` from `ReasonsR.lean:18–27`; the latter
preserves the actual `fiber?` lookup, including duplicate-id behavior, and requires the exact
parked token. Do not duplicate or replace it with a scan over every fiber.

Use `raceRegistrationR`'s direct `.vis (.inr (.raceRegister raceId)) _` match for
`registrationDone` authority. `InterpR.lean:317` sets `parkOf` to `none`; the evaluator
consumes `raceRegister` directly at `EvaluateR.lean:265`. `registerRace` leaves this current
code in place and emits launch/registrationDone (`Machine/Fibers.lean:909–920`). Thus copying
the native parkOf equation would reject legitimate reference registration queues.

The reference authority otherwise mirrors `Guard/Core.lean:1161–1171`: active hosts for
loop/deliver/finish/afterInterrupt/closeParAwait/raceCancel; an existing race with active host
for launch/enrollRace; an exited fiber for exitDone. The native authority does not additionally
assert that a registration is marked registering, that an observer was registered, or that a
raceCancel's host equals the named race's host. Those conditions must not be invented as
though the native theorem already established them.

## RCodeSites is held pending an exact traversal contract

The immediate race-registration match above is settled; a recursive reference code-site
scan is not. Native `raceSites` (`Guard/RaceSites.lean:25–35`) descends static wrappers and the
stored second body of onSuccessConst, but not a named dynamic continuation. RProgram instead
has function-valued continuations. A blanket universal quantifier over their domain would
inspect answers the evaluator never uses:

- `unguard` and `finishFinalizer` deliver their payload and ignore `next`.
- `raceRegister` ignores `next`; `frontier` retains the current term and never answers.
- `sync value` calls only `next value`; suspend/foreignRelease/closeWalk call only `next unit`.
- `guard_` enters `next none`, and its saved arm is selected only when `hasExitArm` holds.
- construction is instantiated at actual completed exits by `prepareR`; its eager guard
  traversal does not run the saved callback before the callback is invoked.

A head-only scan is also insufficient to claim the native static-wrapper meaning, because
construction and guard bodies can reveal a pre-existing race registration. There is no
approved answer-domain classifier or exact native/reference race-site relation in the
current sources. Do not silently choose a universal scan or a head-only scan. The observer
probe needs neither and is quantified over every eventual scan.

## Every command constructor

The generated payload source rows are `Typed/Sources.lean:63–65`. They add content checks
only for finish, resume, and observe. For the other commands `RCmdOk` supplies no new typing
link. The following records the native-mirror exclusions, not a claim that they suffice for
all eighteen preservation theorems.

| Command | Excluded by the proposed clauses | Remaining uncertainty |
| --- | --- | --- |
| evaluate | No added authority; machine itself ignores missing, exited, running or parked fibers | Starting a real idle fiber must obtain all new queue facts from typed state and evaluator laws |
| loop | Missing/non-running/parked host; duplicate active owner | The typed-state clauses do not by themselves establish the native full GuardState code/ownership invariant |
| deliver | Same active-host and owner exclusions as loop | Saved callbacks require a justified code-site rule |
| finish | Wrong exit at a declared fiber type; inactive host; duplicate owner | This closes the recorded unit-versus-42 payload hole; subsequent observer queues still need observer typing |
| resume | Code wrong for an existing token declaration; token at/above nextToken; external reserved key; forbidden race site | ResumeOk is conditional on declaration; stale keys can remain inert. Do not replace this with an unconditional existence requirement |
| launch | Missing race or inactive race host | RaceOk currently states token declaration, not typing of every queued entrant program |
| enrollRace | Missing race or inactive race host | The generated race observer can later carry a child exit to the host token; that type link is not a source-row payload check |
| registrationDone | Missing race/host, inactive host, or current code not the named race registration; duplicate owner | Buffered race-result type and stored race-token ownership remain state obligations |
| interruptTarget | No new authority or key/owner condition | Its guarded machine behavior and preservation of cause/frame facts must be proved later |
| afterInterrupt | Inactive host; duplicate owner; `.race` ParkKind (explicit command-site exclusion) | Join/awaitAll target results and host continuation typing remain obligations |
| raceCancel | Inactive host; duplicate owner | Exact native authority does not correlate the supplied host with the race; cleanup continuation typing remains open |
| trackChild | No new authority; no carried payload/key/site | Existing machine guards determine inert cases; child/parent declaration and observer effects need proof |
| observe | Exit wrong for source fiber's declared type; observer resume/countdown token out of range or externally reserved | The source exit is not connected to the recipient's token type. ObserveGap is the concrete candidate falsifier |
| exitDone | Missing or not-yet-exited source fiber | Clearing the saved stack/context must still meet typed-state clauses |
| closeParAwait | Inactive host; duplicate owner | Created iterator frame and eventual await-list answer need typed hook evidence |
| link | No new authority/key/owner condition | Dynamic finalizer registration and target interruption need later proof |
| drainDue | No carried command key/site | InternalKeysBelow bounds emitted keys, but it does not alone prove those keys disjoint from external requests or that every owed code has no race site |
| wake | No carried command key/site | Moving stored waiters into due work relies on the same missing state links as drainDue |

## Observer candidate and smallest owner decision

The witness keeps a loaded `succeed(unit)` fiber and raises `nextToken` to 1. Its world adds
only the historical declaration `(root, 0) ↦ unit`. Nothing is parked or pending. It queues
`observe root (success unit) (resumeAwait root 0 awaitValue)`.

The input exit fits the source's unit type. Its key is below 1 and is not externally reserved;
there is no owner and no code field to scan. `fireObserver` always emits a resume whose value
is the reified successful exit. That value is an exit encoding, not unit. The historical token
declaration cannot be changed by `World.leHost`, so no later world can type the output resume.
The machine need not be reachable: the statement quantifies over every typed input state.

If Lean confirms the probe, H1 requires an owner ruling about observer-to-token typing before
claiming the statement repaired. At least the resumeAwait mode/result must fit the recipient's
Θ declaration. Requiring only that an observe command names a stored observer would not by
itself establish this: the current generated typed-state predicate does not type that observer
against its recipient. Countdown and race callbacks need their corresponding result linkage.
No such extra condition has been added in these drafts.
