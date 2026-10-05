# Waiting design W: the detached signal and its work boundary

Accept candidate B as the proposed Queue delivery, subject to the corrections below.
The existing machine supports its stated dispatcher and helper lifetime.
F7 does not yet bound the selected delivery, and F6 changes the unit of posting.

Status: source review, with retained finite output checked.
Reviewed commit: `27ea7cb246191ccdec20ca4819446b2546084118`.
The final source check also reads the note's update at `261b4a8e4508f7ba8e677ed1e1e5e0aff4c5dcca`.
Reviewed note: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-05-claude-lead/waiting-design.md`.
No repository file changes, build, generator, installation, or new Effect run occurs.
The reader compares the two retained composite outputs as JSON, after removing their version fields.
They agree on every recorded observation.

## What is supported

F3's helper is allocated by `spawn` before the signalling fiber can exit.
`start` posts `Task.start child` on that signalling fiber's dispatcher.
The daemon path in `withFiber` does not add `Cmd.trackChild`.
`RunFiber.cleared` retains the dispatcher after clearing the owner's frame, children, observers, and context.
`fireState` drains that dispatcher without testing the owner's exit.
`taskCmds` evaluates the helper, whose own exit and park state determine whether it runs.
These declarations are in `/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean`.

Thus this proposal does not need to fork from an already exited owner.
Its live signaller allocates the helper and posts its start before exiting.
The existing exit guard checks the helper at dispatch, not the old signaller.
This resolves the earlier owner-exit watchpoint for the actual F3 form.
The retained detached-helper control already supplies finite rc.112 evidence for the same lifetime distinction.
Its files remain under `/private/tmp/codex-effect4-overnight-monitor/2026-10-05-deferred-latch-probes/runtime/`.

The daemon fork template already prints `Effect.forkDetach` in `src/Effect4/Codegen/Templates.lean`.
`printForkOptions` in `src/Effect4/Codegen/PrintLeaf.lean` prints the selected start and mask options.
These are source support for reuse, not the Queue's expansion theorem.

## Findings and smallest corrections

### 1. F3 and F7: bound posting separately from the work caused by resolution

F3 infers bounded delivery from one fork per signal.
That bounds posting work, subject to its surrounding continuations.
It does not bound the helper's delivery using only that count.

`DeferredStore.complete` creates inline owed resumes in `src/Effect4/Machine/Stores.lean`.
`evaluatePrim`, `drainOwed`, `settle`, and `driveStep` in `src/Effect4/Machine/Fibers.lean` run those receivers before the helper continues.
The receiver can finish `take` and enter its client's continuation in the same command drain.
The current driver has no Queue-return boundary that stops this execution.
A typed receiver can have a long continuation, further inline completions, or a loop.
Typing alone does not bound that work.

The later note says the synchronous helper body cannot park, so no posted work remains unfinished.
Its body contains no explicit await, but that does not settle the embedded command drain.
The exact native route is `Task.start`, `taskCmds`, `Cmd.evaluate`, `Cmd.loop`, then `evaluateNative` and `evaluatePrim`.
`evaluateNative` and `evaluatorFor` are in `src/Effect4/Program/Compile.lean`.
The sync answer queues `Cmd.drainDue` before the helper's `Cmd.deliver`.
`drainOwed` inserts the receiver's `Cmd.resume`; that inserts `Cmd.evaluate receiver` ahead of the helper's continuation.
All these commands spend the same `driveState` budget for that task.
Therefore receiver work can exhaust the task budget even though the helper contains no blocking operation.
Automatic yield remains another possible park: `injectYield` checks scheduler settings before evaluation, independently of the helper's mask.

**Correction:** call F7's displayed count a bound on Queue posting and wrapper work, not selected delivery.
For `embedded-budget-sufficient`, include the reached receiver continuations, cleanup, and pending commands in the premises and bound.
If the first profile restricts those continuations, state that restriction explicitly.
Otherwise retain the wider driver suspension before promising resumable delivery.
This changes the theorem's premises or remaining work, not candidate B's program syntax.

**Acceptance:** hold queue state and signal count fixed while increasing a profile-supported receiver continuation's work.
The claimed sufficient budget must cover the resulting drain, or the profile must refuse the longer client.
Use the empty continuation as the positive control.
This is a proposed falsifier, not a newly executed probe.

### 2. F3's open ending and F7: distinguish an unstarted helper from a cut inside dispatch

F3 leaves observation of a run ending with a posted helper open.
An intact pending dispatcher entry is only one frontier.
At dispatch entry, `fireState` removes the entire snapshot from the dispatcher.
`fireStep` retains the machine and a settled flag; it discards the remaining `driveState` commands.
Later tasks in that snapshot are skipped after an unsettled task.
Those declarations are in `src/Effect4/Machine/Fibers.lean`.

A source-derived control is a dispatcher containing two helper starts and a zero command budget.
The snapshot is removed, the first start leaves commands, and neither helper runs.
The returned machine alone no longer contains their queued starts.
This is the already-recorded driver boundary applied to F3's actual notification owners.
It is not a new claim that the daemon itself loses its code or that full suspension must land first.

**Correction:** state both frontiers in W's observation and budget contract.
Before dispatch, record the helper and its queued start as outstanding notification work.
Inside dispatch, exclude a cut using the proved sufficient-budget premise of row 226.
Do not call another `fire` on the projected machine a resumption.
A selected request cannot disappear from the notification invariant merely because its helper body is allocated.

**Acceptance:** retain the zero-budget source case as an excluded input until a suspension exists.
Test one sufficient dispatch budget with the same two helpers as its positive control.
The first Queue proof must identify where each notification lives before helper allocation, after posting, and after receiver acceptance.

### 3. F6 disagrees with F3 and with the probe about what gets posted

F3 posts one helper per hint.
The probe's `post` function does the same through `Effect.forEach`.
F6 instead says one helper resolves every hint in order.
Those are different scheduling units, with different yield and completion boundaries.

**Correction:** keep F6 at one helper per hint for the first Queue, matching F3 and the evidence.
If a later transaction posts a whole notification list, describe that as its separate producer contract.
Do not use the existing probe as evidence for that grouped body.
The current composite emits at most one hint, so this is a future consistency issue, not a failed first-Queue case.

F6 also needs a narrower inference from deferred start.
It prevents a receiver from running synchronously inside the individual fork operation.
It does not prove that all notification forks finish before any receiver runs.
`injectYield` can yield between forks even while the producer is uninterruptible.
It checks `preventYield`, not the interruption mask, in `src/Effect4/Machine/Fibers.lean`.
Therefore the transaction's row-223 bookkeeping property still needs its own boundary argument.
The Queue's single `Ref.modify` atomicity can be accepted without claiming that later transaction property.

### 4. F2's evidence does not cover the first positive-capacity suspend path

`composite-queue.ts` admits `unbounded`, `sliding`, and `dropping` strategies.
Its `State` contains messages and takers, with no pending offerers.
Its `wake` returns at most one hint.
The retained outputs support the listed finite rows, including the cancellation-after-signal comparison.
They do not test suspended offers or F7's several-signal case.

**Correction:** retain the existing results and state this boundary beside F2.
Add the first suspend-path control with the first Queue implementation.
Fill a capacity-one queue, park an offerer, and take the old message.
Cancel the offerer before its posted hint runs.
Check that its new message is absent, the old message is consumed once, and a later offer can progress.
Use the uncancelled offerer as the positive control.
Also let the signalling taker exit before dispatch, reusing the supported lifetime contract above.
No rerun of unchanged P5 to P7 is required.

## Placement of the corrections

These refine existing obligations from `foundation-contracts.md`; they introduce no new proof destination.

| Obligation | Concept and consumer | Required premises and observation | Exclusion and immediate prerequisite |
| --- | --- | --- | --- |
| `embedded-budget-sufficient` | `reactive-scheduling`, R12; Queue segments and selected delivery | Existing machine, admitted continuations, cleanup and pending work; no unfinished command or dropped task at the accepted boundary | Not arbitrary typed clients or host wall time; F7 must name its exact endpoint and continuation premises |
| `waiting-request-obligation-preserved` | `reactive-scheduling`, R11 serving R10/R12; F5 wrapper | A logical request, its hint, helper, queued start, and accepted receiver token; follow outstanding work through every transfer | Not eventual service without fair decisions and work bounds; define observations for unstarted helpers and excluded dispatch cuts |
| `posted-wake-profile-agrees` | `translation-simulation`, R10; F3 and the first Queue expansion | The signed dispatcher/helper profile, one helper per hint, typed capture, fixed compatible decisions; compare the selected client observation | Not a grouped transaction notification body or native Queue equality; make F3 and F6 consistent |

The current fork clauses supply local machine behavior and typing ingredients.
They do not by themselves prove these composed wrapper statements.

## Acceptance recommendation

Approve F3's reuse of the existing detached fork for the named first Queue profile.
Record the corrected work-bound scope and the one-helper-per-hint choice before dispatching its proof work.
Keep finite output, source support, open proof obligations, and signed profile differences separate.
This receipt does not revisit the maker/signaller or helper-identity choices already presented for sign-off.
The mask proposal is outside this focused delivery review.
