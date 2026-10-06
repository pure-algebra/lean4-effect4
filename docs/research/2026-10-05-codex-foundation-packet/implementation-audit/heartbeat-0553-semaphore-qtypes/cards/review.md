# Semaphore card and retained probe review

Status: source review and retained finite host evidence.
Frozen main: `21b9722976b0339db1c58973015af06f0697e126`.
Card revision: `8c61250f`.
No model or profile is ratified by this review.

One new actionable clarification follows from the coordinator's new P3 probe.
Grant-at-wake differs from the native walk even without an explicit yield or interruption.
The current table describes those two cases as its differences.
It also needs the effects of the resumed caller's continuation.

## The witness

P3 uses a total of two permits.
H holds both.
B waits for one permit, then immediately takes one again.
C waits for one permit behind B.
H releases two.

The retained rc.112 and 4.0.1 outputs both record:

```text
before: permits 2, taken 2, waiters 2
B took 1
B took 1 again
after: permits 2, taken 2, waiters 1
```

B contains no explicit yield between its takes.
The raw takes retain permits after the fiber ends.
C remains parked while B holds both permits.

The proposed atomic grant pass selects B and C before either caller continues.
It commits one permit to each.
B's second take then has no free permit to acquire.
Thus the request-commit observation differs within the proposed first profile.
No negative count, over-release, resize or releaseAll is needed.

The pin's source explains the result.
`waitForPermits` removes the observer and invokes `resume`.
`callbackOptions` invokes `FiberImpl.evaluate` for a parked callback.
That evaluator runs the caller continuation until a yield, park or exit.
It does not return immediately after the retry acquires its permits.

P4 supports this boundary too.
A resumed protected body and its release hook finish before the wake resumes its next visit.
Its final count alone does not distinguish the two policies.
P3 supplies the direct observable distinction.

## Smallest card correction

In section 10, replace “the pin's path with no yield, as one step” by a separate atomic-grant policy.
Name caller reentry and release before the next visit among its differences.
The first-profile surface currently permits these callers.

If a restricted agreement claim is desired, state its caller restriction explicitly.
A no-yield premise alone is insufficient.
A sufficient restriction would also control subsequent semaphore operations and cleanup before the wake continues.
Such a restriction remains a proposal, not a proved condition here.

The live-scan alternative needs the same boundary clarified.
A hand-over that waits only for the acquisition attempt is too short.
It must represent the reached continuation's execution cut, or state the corresponding caller restriction.
This uses the existing continuation/budget question; it does not demand a second interpreter.

Placement remains the card's proposed `semaphore-expansion-agrees` under `translation-simulation`, R10.
Its consumer is the Semaphore public expansion and its agreement profile.
Its observation includes request identities and permit commits, as section 6 already requires.
Hypotheses must specify the chosen wake policy, admitted callers, interruption and work budget.
The immediate prerequisite is the recorded profile choice before freezing a model.
Nothing here states fairness, general progress, runtime unsafety or an upstream bug.

The smallest falsifier is already retained: P3, with P1 and P2 as positive controls.
No new compiler or host probe is needed to report this distinction.
If grant remains the choice, retain P3 as a named expected policy difference.

## Previous corrections are present

- The card states that wake visitation reads live state after an inline resumed continuation.
- Protected activation identity appears in the observation.
- Permit commit, body entry/exit, release commit and cleanup completion remain distinct.
- Pending release debt stays observable until cleanup completes.
- A frontier is neither completed cleanup nor typed failure.
- Protected bodies use the ordinary builder; they do not wait for retained code values.

These findings are resolved at design level and should not be repeated as defects.
The new correction above is narrower: the reached continuation is longer than one retry.

## What the probes establish

`semaphore-wake.ts` runs eight cases against each package named by `EFFECT_DIR`.
The retained tool results report exit zero for rc.112, 4.0.1 and 3.22.2.
The two Effect 4 output objects match exactly after removing their version field.
The package metadata and installed Semaphore sources match the declared versions and vendored source.
The two vendored Semaphore files differ only in releaseAll documentation.

P1 exercises the no-yield acquisition path.
P2 exercises the later smaller request.
P3 exercises caller reentry.
P4 exercises protected body completion inside visitation.
P5, P6 and part of P8 exercise excluded numeric or releaseAll behavior.
P7 exercises interruption while parked.
P8 also exercises protected-body interruption.

The source replaces the free getter with the same subtraction plus logging.
These are instrumented finite observations, not an unmodified-runtime simulation theorem.
Sixteen yields are a bounded settling schedule, not a fairness premise.
The outputs include their actual before states, so the retained P1–P4 registration preconditions can be inspected.
The probe does not force the card's alternate path where B yields before its retry.
It does not establish all incoming-mask or post-resume cancellation cases.
The exact probe calls are retained; these calls do not record the Bun version.
No compiler check is recorded by these runtime calls.

The Effect 3 comparison establishes no agreement profile.
Its P1 observer identity already differs, and its free-read traces differ.
Its similar public answers do not equate callback, scheduling or cancellation semantics.
The project remains pinned to rc.112, with 4.0.1 considered separately.

## Pool and Cache

No Pool or Cache card exists in the reviewed module-card directory.
STATE records that fact correctly.
Their preparation is not an incomplete implementation defect.
The shared procedure still distinguishes lease return from destruction and stale Cache cleanup from replacement entries.
No new Pool or Cache finding is submitted by this check.

## Evidence and limits

`source-hashes.json` records nine committed source files and five local evidence artifacts.
The four probe files are local coordinator evidence, not tracked files at the frozen commit.
`installed-identities.json` records the three package metadata identities and the two matching Semaphore source hashes.
`retained-validation.json` verifies 22 facts by parsing the saved outputs.
All comparisons pass.

No monitor runtime, Lean, compiler, generator, build, install or repository edit occurs.
No advisory is sent to Claude by this subagent.
The parent owns delivery and later repair checks.
