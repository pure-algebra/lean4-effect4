# H1 candidate for root

The one thing to know: **this is an uncompiled candidate prepared outside the repository.** It does not prove any of the eighteen command-preservation obligations. Root owns the one-at-a-time Lean lane, integration, trust checks, register status, receipt and commit.

Prepared against the live slice6 worktree at `e5cc184ba820ab4ea79b38fd32820421514812b9`. `python3 prepare.py`, Python syntax compilation and `git apply --check implementation.patch` succeeded. No repository file was written by this seat. No lake, make, generator or commit was run.

Authority: `/private/tmp/h1-implementation-guidance.md`, addendum 2 H1 freshness/control clauses, addendum 3 H1 all-command payload/guard/controls clauses, and addendum 4 H1 observer ruling. H2 and D1-D6 remain held.

## Files and integration

`implementation.patch` touches six exact paths:

- `src/Effect4/Laws/Program/Guard/Core.lean`: generalize nine code-independent helpers over Code/Saved/Event; native meanings unchanged.
- `src/Effect4/Laws/Program/Guard/RegistrationQueue.lean`: generalize RegistrationTail and RegistrationQueue over the code carrier.
- `src/Effect4/Laws/Program/Typed/Scheduler.lean`: finite scheduler, observer, countdown and race predicates; direct registration ownership/result-to-stack correlation; finite administrative-command delivery clauses; exact resumeAwait delivery facts; loaded-state guard facts.
- `src/Effect4/Laws/Program/Typed/Assembly.lean`: RaceOk uses the single RacePayload owner; stronger TypedState/QueueOk; pending_below; StepPreserves checks result queue against result machine.
- `Test/Counterexamples/Machine/Semantics/ValueMembership.lean`: extend the existing positive loaded-state builder with the new empty-state guard/observer/registration facts and an explicit no-direct-marker premise, discharged by reduction at the existing ref/get controls.
- `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`: H1 loaded pure/sleep controls (including the original budget 80), historical finish and observer falsifiers, the exact early-queue and dispatcher falsifiers with their initialization premise discharged, their new refusals, and both actual delivery-mode greens.

The exact new-module route is `src/Effect4/Laws.lean:120` -> `Typed/Assembly.lean` -> its new `import Effect4.Laws.Program.Typed.Scheduler`. `Test/All.lean:40-41` already imports M6Capstone and ValueMembership. Therefore no root import or Test/All addition is required. Guard.Core and ReasonsR do not import Assembly, so this introduces no evident import cycle. `prepare.py` rereads the live tree and uses single-match assertions, so root can regenerate after C/F/G without copying stale unrelated edits. The new Scheduler source and test fragments remain the prepared input files under this directory. The script only writes here.

Suggested application after root review: regenerate, `git apply --check`, then apply the patch. Do not copy the entire Guard/Core or Assembly candidate if either has changed since regeneration. No register/receipt modification is included before verification.

## Deliberate statement choices

Internal-key bounds and request disjointness sit in SchedulerState, a conjunct of TypedState. This is explicitly permitted by addendum 2 and keeps StepPreserves quantified over every queue satisfying its queue fact. Queue freshness and disjointness are separate queue facts, checked at the actual input/output machine.

PendingOk still loses the enclosing fiber id, so ObserverState.pendingOwner supplies that identity correlation. `pending_below` itself needs only the original PendingOk declaration plus WorldValid.tokenBound, exactly as the accepted probe established.

Observer registration uses StoredObserverOk; consumption uses ObserverCommandOk. Both use the same delivered type function for resumeAwait. The local theorem connects the **actual** interpR.exitValue program, including the reified Exit value in awaitValue mode, to its declared token type. Source exit typing remains the generated RCmdOk responsibility too.

CountdownAt follows actual waiter and pending lookup. It uses one shared pair of aggregate columns for buffered exits, remaining declared fibers, the incoming exit/source, and the eventual resume mode. It does not misclassify every `.void` pending record as a countdown; the predicate is attached to an actual countdown observer. Missing lookups are inert.

RacePayload is the only owner of buffered race typing. It covers failures, winner, accepted, cleanup result, live child columns and the finite list of unlaunched programs. Queue observe/callback and enrollRace refer to the same token/result witness. Enrollment is separate because an already-exited entrant can fire the callback immediately.

The other observer arms untrackChild, dropScopeFinalizer and callback carry no token result; their ordinary machine guard behavior remains. callback still records its exit as a log event.

## Explicit remaining obligations

- **H1-RCODE-SITES:** no exact recursive RProgram race-site scan has been specified. SchedulerState lacks the native frameCodes/internalCodes analogues and QueueOk lacks a recursive resume-code scan. This is named in source, not represented as True or as a head-only or universal-continuation approximation. The direct forbidden afterInterrupt/race form is exact and included.
- **M5 observer registration:** prove source certification installs the token and observer correlation stated here. Existing fiberPost for awaitValue still asks for the target's answer value rather than the encoded Exit; this pre-existing protocol mismatch is named debt and is not silently changed here.
- **M5 countdown/race hooks:** prove exact countdownPark.resumePrim and the cleanup branch of denoteRaceSettle from the finite payload facts. The candidate does not fake these by requiring the entire transition result to be typed.
- **M6:** all eighteen commands, direct decisions and the capstone remain proof obligations. The eighteen names and the total M6 ceiling 20 are unchanged.
- **H2:** no shape-defect exclusion is added, and the capstone disclaimer remains.

No new checked contract counterexample was established by this seat. The known awaitValue protocol debt is not claimed to refute the new observer-delivery lemma. Elaboration and axiom trust remain unverified because this seat was expressly denied the Lean lane.

## Per-command exclusion matrix

Every row remains a proof obligation; these are predicate exclusions, not preservation proofs.

| Command | Settled exclusion in this candidate | Remaining proof/code debt |
| --- | --- | --- |
| evaluate | no added authority; actual machine guards decide inert missing/exited/running/parked cases | establish generated queue and observer facts from certified evaluation |
| loop | inactive/missing/parked owner; duplicate owner | typed evaluator output; reference code-site ownership; direct registration token-to-stack correlation is now included |
| deliver | inactive/missing/parked owner; duplicate owner | saved callback code and delivery typing; reference code sites |
| finish | wrong exit at the source fiber's declared type; inactive host; duplicate owner | establish each emitted observer payload from stored correlation |
| resume | ill-typed code for a declared token; key at/above nextToken; external reserved key | exact recursive code-site rule remains open; stale inert keys need not acquire declarations |
| launch | missing race or inactive race host; RacePayload types stored programs | spawn/source/world extension and finite program dequeue |
| enrollRace | missing race or inactive race host; child's exit columns must fit the race result | immediate exited-child callback and world/state transport |
| registrationDone | missing race/host, inactive host, wrong direct raceRegister operation; duplicate owner | buffered settle/cleanup hook typing; RegistrationState now ties the same token result to the host stack |
| interruptTarget | no added authority | actual guarded interruption and cause/frame transport |
| afterInterrupt | inactive host, duplicate owner, direct `.race` kind | finite target declarations and actual reply columns are now required by CommandDeliveryOk; hook certification remains M5 |
| raceCancel | inactive host and duplicate owner, matching native authority | StackReply pureunit and finite visited/remaining declarations now exclude the bad nat-stack instance; recursive queue proof remains open |
| trackChild | no carried payload/key/site | tracking observer registration and state transport |
| observe | wrong source exit; key out of bounds/reserved; wrong delivered token type; ill-typed countdown/race buffers and input | hook/payload transport; countdown/race continuation facts |
| exitDone | missing/unexited source | cleared stack/context state transport |
| closeParAwait | inactive host; duplicate owner | finite target columns, named iterator protocol and its unit/error StackReply are explicit; their registration proof remains open |
| link | no added authority | finalizer registration and interruption state transport |
| drainDue | no carried command key/site | stored keys bounded/disjoint by SchedulerState; stored completion output code typing and code sites |
| wake | no carried command key/site | wake-table/due movement and later output-code typing |

## Verification for root

Only after applying in the authorized H1 phase, narrow builds should include Guard.Core and its changed direct dependents; Typed.Scheduler and Typed.Assembly; and the two changed battery files. No broad sweep is implied. Root should inspect dependency impact from generalized helper signatures, especially existing native guard proofs.

M6Capstone prints axioms for the new proof-bearing controls. Also request `#print axioms` for production `pending_below`, `reifyExitVal_fits`, `observerDeliveredExit_fits`, `observer_exitValue_typed`, `observerCommand_resume_typed`, `requestOfR_load_none`, `schedulerState_load`, `observerState_load` in root's retained H1 probe, and keep the exact output. Run the planned `make check-cases`, but do not claim it checks the new Observer/RCmd matches: the current case policy does not list those families and the profile imports only Effect4, not Laws. See validation.md for the exact coverage limit. `Axioms.lean` beside this README contains the exact production axiom-print commands and three obligation-shape checks; root can copy it into the retained H1 evidence path and run `lake env lean -DwarningAsError=true <that-path>`. Test rendering expressions stay under #guard.

Current static checks completed by this seat:

```
python3 /private/tmp/h1-candidate/prepare.py
python3 -m py_compile /private/tmp/h1-candidate/prepare.py
# cwd=/Users/pooks/Dev/lean4-effect4-slice6
git apply --check /private/tmp/h1-candidate/implementation.patch
git apply --stat /private/tmp/h1-candidate/implementation.patch
```

All exited 0. These establish generation/applicability, not Lean elaboration or theorem truth.

## Register wording after successful verification

Update E4-SCHED-CE-016 to REPAIRED, citing the early queue refusal, internal-key bound, and loaded sleep green. Preserve that its former false statement is historical and that general M5/M6 proofs remain open.

Add E4-SCHED-CE-017, “M6's queue fact types every queued command”, REPAIRED, citing H1.step_finish_false/proposed_step_finish_false and bad_finish_rejected; the repair is every-command RCmdOk plus guard conditions.

Add E4-SCHED-CE-018, “a token is typed by what its observer delivers”, SEEDED by the retained ObserveGap candidate and REPAIRED here, citing OldObserve.proposed_step_observe_false and H1.bad_observe_rejected. The exact delivered type is mode-dependent and connected to the actual interpreter hook. Do not call the eighteen transitions proved.

The delivery lemma now explicitly cases on observer mode before applying TypedProg.pure, avoiding a potentially stuck unification through interpR.exitValue with variable mode.

Final candidate includes the original early-queue and dispatcher machine witnesses at budget 80. The old conditional proofs read local ReviewedTypedState/ReviewedQueueOk/ReviewedStepPreserves; `EarlyStep.old_steps_false` and `EarlyDecision.old_fire_false` use the actual loaded sleep green to discharge initialization. Their corresponding repaired queue/state exclusions use the shared guard key list. These are falsifiers of retired statements, not proofs of the new transitions.

`prepare.py` is the reusable regeneration script. `prepare-early.py` is retained only as the one-time generation receipt; do not rerun it (the prepared fragments already include its changes).

Pinned-library correction: schedulerState_load uses the existing Guard.guardState_load singleton proof (`List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩`); `List.nodup_singleton` does not exist in the pinned Lean version.

## Subsequent finite amendments from independent review

The direct registration state clause and RegistrationQueue tail discipline are integrated. New CommandDeliveryOk clauses cover afterInterrupt, raceCancel and closeParAwait: concrete target declarations and produced result columns must meet the actual host stack. For closeParAwait the iterator input and output share the aggregate error column, as the existing IteratorProtocol requires. It does not use a pure input to forbid failure-bearing finalizers. No runtime, SavedOk or existing protocol definition is changed.

The new registration controls reject unit Γ against nat Θ on an empty stack for both buffered and unbuffered race states, and admit a matching nat/nat correlation. Three administrative-command controls reject the nat-stack/unit-answer mismatch; the matching empty awaitAll on unit has a positive control. All are uncompiled.

**Pending independent probe:** the reviewer suspects a pre-existing SavedOk terminal-frame mismatch that may refute the final H1 step_loop statement even with all these clauses. Root owns the exact Lean probe before landing. Do not broaden this candidate into runtime/SavedOk repair. If the checked witness refutes the newly requested statement, root applies the brief's stop rule. The deferred register patch remains unapplied.
