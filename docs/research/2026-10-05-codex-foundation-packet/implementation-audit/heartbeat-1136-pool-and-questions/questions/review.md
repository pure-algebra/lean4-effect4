# MASK census and Pool brief: recommendations

Snapshot: `2ee2aa91ef0edfacf4a2ab30f537b2fccf3b6620`. The checkout is clean at the reviewed cut.
Role: advisory review. Evidence: source reading, retained seat results, and one finite Python model.
Scope: the proposed MASK census row and the undispatched Pool brief. No repository file changes.

## Recommendation on the census

Approve the addition of `interrupt.uninterruptible-mask` with coverage `partial`.
The denied edit needs the owner's disposition. This review does not bypass it.
The addition records known evidence and missing proof; it need not wait for the new mask run invariant.

The proposal is item 2 of section 10 in `docs/research/2026-10-05-seat-MASK-receipt.md`.
`docs/RUNTIME-COVERAGE.md` owns the meaning of coverage. Partial rows explicitly list each missing clause.
Neither a finite control nor a model invariant makes the full source behavior green.

The source is `uninterruptibleMask` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
Its unique anchor is `export const uninterruptibleMask = <A, E, R>(`; offsets are 0 and 12.
The exact span digest is `276d40c762a093ac1d675da7e1a2b6146abc697e589bef4bebf10348c19b3691`.
`mask-span.json` retains the span, source digest and uniqueness check. No generator ran.

Keep the complete proposed behavior summary:

> An already masked fiber gives its body identity as restore. Otherwise it clears interruptibility, pushes the restoring frame, and supplies interruptible.

The existing evidence supports these parts:

| Existing theorem | What its statement establishes |
| --- | --- |
| `Effect4.Machine.withFiber_getInterruptible`, `src/Effect4/Laws/Program/Typed/Mask.lean` | The particular mask whose body returns restore masks the fiber and answers its saved state. |
| `Effect4.FrameFiber.uninterruptible_already_masked`, `src/Effect4/Machine/Frames.lean` | An already masked frame stays unchanged at this entry. |
| `Effect4.FrameFiber.uninterruptible_masks`, same file | An interruptible frame becomes masked and receives the restoring frame. |
| `Effect4.Program.Typed.compileEff_restore_false`, `src/Effect4/Laws/Program/Typed/Mask.lean` | A successfully evaluated false saved token compiles directly to the body, at positive compile budget. |
| `Effect4.Program.Typed.compileEff_restore_true`, same file | A successfully evaluated true saved token compiles to the restore site's with-fiber action, at positive compile budget. |

The row comment should retain two missing connections:

- No theorem relates an arbitrary compiled derived mask body to native `uninterruptibleMask` on a stated target observation.
- No run theorem establishes completed-region restoration for arbitrary nested bodies; the current law establishes entry and saved-frame boundaries.

The derived entry has extra checkpoints. Therefore equal flags at selected boundaries do not establish equal runs or equal interruption timing.
The existing `MaskRestoration` documentation already states that limit. Leave it intact.
The new mask pop proof can later advance its named obligation without automatically promoting this census row.

Implementation is the documented census procedure: generator row and expected counts, generated projection, and the `RuntimeCoverage` join.
The documented initial row has absent coverage before witnesses are attached. The proposed final coverage is partial, with existing witnesses.
The intended witness docstrings must name the census ID, as AGENTS requires.
The ordinary census gate supplies the measured report; this review reports no new coverage count.
`scope.acquire-release` already uses the frame entry lemmas. Reusing them here adds no second proof or stronger statement.

The MASK receipt retains successful builds through `1c70029c`, axiom results, S7 controls and finite truth runs.
Those are the seat's retained results. This review reruns none of them and makes no current compilation claim.

## Pool: settled choices and two brief clarifications

Rows 267–269 settle eager acquisition, `use`, exclusions, waiting close and front insertion on return.
Rows 270–272 settle the corresponding Cache choices. None needs another owner answer.
The Pool brief is written but not dispatched. Its representation choices belong in the seat's design note.
Its public operations, waiting close and finalizer runs are explicitly outside this cell-and-step slice.

### 1. Replace the candidate state invariant with an enrolment rule

Part 3 asks for no waiter beside an idle item in an open pool, then says to explain if it fails.
It fails at the intended cut between a return and its posted helper.
H returns item 1 while A and B wait. The item becomes idle; A and B remain enrolled until the helper runs.
The item partition remains valid.

This is already visible in PP4's retained output on both versions:
`after H's return and before the task: 2 waiting`.
The source path is `releaseItem` followed by posted `wakeWaiters` in `vendor/effect-4.0.1/src/Pool.ts`.

Smallest correction: allow that state and require lease-or-enrol to append a waiter only when the pool is open and has no idle item.
Keep the item/lease partition, unique identities and return ownership as state invariants.
Do not add a fairness or no-overtaking premise: the card explicitly leaves fairness unclaimed.
The brief already makes this proposed invariant conditional, so this clarification changes no frozen statement.

Proposed property, not a Lean theorem:

`newlyEnrolled(before, after, id) -> not before.closing and before.available = []`.

Placement: the existing proposed Pool profile closure, `store-typing`, R4.
Consumer: the lease-or-enrol model, its term agreement under `pool-expansion-agrees`, R10, then the public waiting wrapper.
Hypotheses: valid item partition and identities; first profile; one atomic lease-or-enrol transition.
Observation: enrollment and the stored cell, separate from a later helper selection.
Exclusions: liveness, fairness, completed cleanup and target agreement.
Prerequisite: the design note states the step and reply precisely.

`model-controls.py` transcribes only this finite transition. Eight assertions pass, including a no-waiter positive control.
It refutes the candidate invariant while preserving the item partition. It is neither a Lean proof nor a host run.

### 2. Label PP5's domain before using it as acceptance

The original PP5 probe gives borrowers the pool while its first acquisition waits.
Opening that acquisition releases a wake that can select multiple waiters.
Row 267 instead makes every acquisition finish before the pool is returned to callers.
First-profile returns post count 1. Close posts all waiters only after refusing new leases.
Thus the original PP5 schedule is not a reachable public first-profile run.

Keep it as a low-level counted-selection and inline-resume control with explicit state and helper-count premises.
Also keep a reachable make-complete, lease, return and retry case for the public first profile.
Do not change eager make merely to reproduce the original host setup.
No failed implementation or incorrect retained host result is claimed.

Placement: `reactive-scheduling`, R12, the proposed `pool-wake-selection`; connected step agreement remains R10.
Consumer: the future helper law, then the public expansion law.
Observation: selected identities and notifications, distinguished from lease commits in resumed borrowers.
Hypotheses: one fixed helper selection at execution time, ordered callbacks, explicit count, and the admitted state domain.
Exclusions: public reachability of arbitrary counts/states, fairness and whole-run completion.
Prerequisite: the packet separates the low-level control from public-profile acceptance.

## Review boundary

Nineteen frozen source and evidence files are hashed in `sources.json`; every working file matched the frozen commit.
No Lean, compiler, generator, host runtime, installation or repository mutation occurred.
No seat was dispatched, and no message was sent to Claude.
