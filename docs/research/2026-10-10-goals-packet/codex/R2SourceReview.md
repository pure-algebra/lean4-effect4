# Read-only R2 order review

No semantic defect appears within the reviewed source and retained cuts.
This review changes no source and starts no Lake process in the root worktree.
It does not replace the coordinator's whole Laws build or behavior sweep.

## Scope

The review reads the primary machine-models audit through its newest 13:45 section.
It compares the current dirty integration sources with the approved R2 message plan.
The integration base is `b4dcef4f12c7ae6eeda97c6c9937596bdc42b61f`.

The reviewed declarations are:

- `interruptCause`, `interruptWithCause`, `applyFiberEdit`, `applyFiberEdits`, `countdownParkEdits`, and `linkScopeEdits` in `src/Effect4/Machine/Fibers.lean`;
- `evaluatePrim.interruptAs`, `evaluatePrim.withFiber`, and the matching `FiberAction` producers in that file;
- `fireObserver`, `iteration`, `settle`, `settleOutcome`, and the affected `driveStep` arms in that file;
- `enterScoped`, `exitScoped`, and `evaluateNative` in `src/Effect4/Program/Compile.lean`;
- `fiberWord`, `fiberWords`, and their path connectors in `src/Effect4/Laws/Machine/Edits.lean`;
- `linkWord`, `eagerLinkWord`, `installedWord`, `settleWord`, and their equations in `src/Effect4/Laws/Machine/EditWords.lean`;
- `observerTailWord`, `observer_producer_path`, and its adapters in `src/Effect4/Laws/Machine/EditObserverWords.lean`;
- the seven retained cuts in `Test/Machine/EditMessages.lean` and the repaired CE046 control.

## Order and payload checks

`settle` writes the local fiber before applying its message word.
It reads the current owner after those messages and passes that owner to `settleOutcome`.
The parked outcome therefore reads the updated deferred interruption flag.
Generated interruption commands precede the original nested commands, which precede the remaining command list.
The nonempty-message missing-owner branch halts explicitly and drops the command list.
The empty-message branch retains the previous disposition directly.

`interruptCause` constructs a fresh cause delta.
`applyFiberEdit` reads the current addressed target before `interruptWithCause` combines that delta with its recorded cause.
No message carries an old replacement record.
Message application adds no trace event.
The producer retains the corresponding interruptRecorded event.
`applyFiberEdits` applies messages and accumulates generated commands in list order.

The native and generic join, scope-link, interruption, and observer-removal producers retain matching message payloads.
Scope registration, token allocation, and diagnostic events remain eager in their canonical plans.
The eager helper views apply those same messages immediately.
Native iteration producers retain them for settlement.
`Program.Compile` scoped entry and exit still construct empty message words or delegate to the primitive evaluator.
The term evaluator's record updates retain the iteration's existing message field.

The countdown observer reads its current waiter after fail-fast interruptions.
It checks the current pending guard before updating countdown metadata.
Its update retains the current frame, dispatcher, parked state, and other record fields.
The observation of the next target applies after that waiter update.
If interruption removes the pending guard, no canceled guard or countdown observer is recreated.
The original pending record supplies the continuation only after its matching current guard is found.
The intervening interruption changes no retained guard's continuation fields.

`settleWord` records the same installation, messages, owner lookup, and disposition order.
`fiberWords` resolves each addressed message at its actual prefix state.
`observerTailWord` records the countdown's same current waiter lookup and conditional observer append.
The shared producer path retains actual lookup facts rather than validating fixed replacements at arbitrary states.

## Premises retained correctly

`settle_edits_found` in `src/Effect4/Laws/Machine/Clauses.lean` requires the actual owner lookup after installation and messages.
The old raw answered and finished equations require an empty message word.
Those internal amendments match the changed Iter domain; no original scenario conclusion changes.
The word equations about machine results do not claim command equality by themselves.
Generated-command cost and predicate transport remain separate outputs of `observer_producer_path`.
Its update hook retains frame, dispatcher, and parked equality against the current found record.
Its countdown command hook retains the original found pending record and the actual observer kind.
These are sufficient local premises for its existing custody and queue consumers.

## Retained tests and evidence limits

The seven cuts cover self join, self countdown, open and closed self scope links, self interruption, token removal, and countdown self-registration.
The additional controls cover fail-fast guard removal, missing owner, cause accumulation, message order, and ordinary other-target join.
The too-late interruption control distinguishes the approved pre-disposition order from a post-disposition application.
CE046 expects an interrupted child and log zero at budget 20000.
The other-child interruption control retains its original successful observation.

The current root runtime and regression files match the previously checked agent copies exactly:

| Source | SHA256 |
| --- | --- |
| Machine/Fibers.lean | `257ab0dbd37b97a70c194ab2c1b38b8c526377d3cbda1e025c6740e5975975f0` |
| Program/Compile.lean | `402b81747790f1e452b96af14c41ec307495efa3750339ede6a0e850e0a84708` |
| Test/Machine/EditMessages.lean | `c2c4fa6f15b5dd86a8f251a3e018ec3932adc72acd284d2229eac817313384f6` |
| CE046 SelfInterrupt.lean | `04d8b724c4f9a329d96615379a6ea571523eb6057ebf799be2a0ac61c916d977` |

The prior receipt retains successful warning-as-error runs for both regression sources.
The API build log reports 151 successful jobs.
The retained test audit reports 48 declarations within `[propext, Quot.sound]`, zero modulo goals, and zero planned goals.
The two direct regression logs are empty, as successful checks produce no diagnostics.
These are prior finite evidence and byte comparisons, not a new runtime run.
Earlier failed diagnostic logs remain historical and do not establish the current build status.

The review finds no missing premise or behavior-order drift in the listed declarations.
Universal outside-runtime agreement, full graph acceptance, generated-output freshness, and the behavior sweep remain outside this review.
