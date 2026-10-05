# Second mask note: runtime and law review

Correct F7's first two laws before accepting their statements. They are false for the stated reach of any typed program.
The getter design itself survives this review. Keep its temporary mask and pending-interruption test explicit.

Proof role: proposed-law review and finite target controls.
Evidence status: source inspection and bounded runtime probes; no Lean execution or proof.
Scope: `mask-second-note.md` at `c3263529a0edeb35c9aa89c10cf62ba9978b9c4d`, F3, F6 and F7.
Runtime versions: installed Effect `4.0.0-rc.112` and `4.0.1`, compiled `dist/index.js`, Bun `1.4.2`.

## 1. F7 needs boundary laws, not uniform flags throughout a body

These ordinary-runtime controls pass on both builds, for both the native mask and the proposed printed expansion:

| Body | Observed flag |
| --- | --- |
| Ordinary mask body | false |
| Explicit `interruptible` inside that body, outside every restore | true |
| Ordinary restore from an interruptible caller | true |
| Explicit `uninterruptible` inside that restore | false |
| Restore under an already-masked incoming caller | false |

The second row refutes F7 statement 1 as written.
The fourth row refutes statement 2 as written.
Existing typed mask constructors permit these nested regions; ordinary typing supplies no exclusion for them.
The flag reader uses public `withFiber` with a runtime-field diagnostic; no custom scheduler runs these controls.

Replace the laws with these boundaries:

- When the derived form enters its main body, its own wrapper makes the flag false.
- A true saved value applies the existing `interruptible` wrapper; a false saved value applies identity to the current execution state.
- Nested operations follow their own mask semantics. They may temporarily change the flag again.
- Each wrapper restores its surrounding state through its existing frame on exit; a pending cause can replace the result when restoration enables interruption.

Place these corrections in the existing `saved-mask-restoration` obligation, concept `scope-lifetime-finalization`, R11.
The waiting wrapper and protected-permit operation consume it.
Premises: an admitted saved value, correct lexical capture, and the existing well-typed frame relation.
Observe wrapper entry, nested execution, wrapper exit, pending cause, and caller continuation separately.
Exclude uniform flags across arbitrary nested regions, progress, Queue safety, and native-mask agreement.
Immediate prerequisite: replace F7's statements before the slice registers their goals.

## 2. The getter's restoring pop is observable under pending cancellation

F3's proposed getter is more than a flag read: it enters a temporary mask and returns through its restoring frame.
This matches its selected public spelling, `uninterruptibleMask(restore => succeed(restore))`.
Do not fuse away the success step or bypass the restoring frame.

Separate manual-scheduler controls force a yield at named checkpoints, then run public `Fiber.interrupt` from another fiber.
The scheduler's `shouldYield` records the operation counter and flag and returns true at one selected checkpoint.
It never changes the flag or injects a cause itself.

| Cut and cancellation | Body executes? | Result |
| --- | --- | --- |
| Printed getter, masked before its success/pop | no | interrupted at the getter pop |
| Same cut, no cancellation | yes | success |
| Native mask, masked before its body | yes | interrupted after the body |
| Same cut, no cancellation | yes | success |
| Printed form, interruptible gap before its main mask | no | interrupted |
| Same gap, no cancellation | yes | success |
| Printed getter under an already-masked caller, with pending cancellation | yes | interrupted at the outer mask's exit |
| Same masked-caller cut, no cancellation | yes | success |

Both builds produce these results.
The native and printed pre-body cuts are explicitly different checkpoints, not a same-decision-tape equivalence test.
These controls establish the proposed target's extra interruption opportunities, not an implementation bug.
F6 should describe both the pending-cause test at the getter pop and the following interruptible gap.
Calling them equivalent to interruption before the form needs a named public observation; it is not literal trace equality.

The existing source supports F3's two-stage sketch.
`WithFiberAction` evaluation's local `answer` in `src/Effect4/Machine/Fibers.lean` installs a success for a later iteration.
`FrameFiber.uninterruptible` and `Prim.ensure` in `src/Effect4/Machine/Frames.lean` install and process the restoring frame.
`uninterruptibleMask`, `setInterruptible`, and `FiberImpl.getCont` in both vendored runtimes give the corresponding target behavior.
The actual new machine action remains unimplemented, so its agreement remains an open obligation.

## 3. Keep the narrow five-step result; distinguish counters from loop checkpoints

The instrumented no-yield runs record each `shouldYield` call, which each inspected run loop makes once per loop checkpoint.
No task is scheduled in these count controls.

| Program | rc.112 checkpoints / final counter | 4.0.1 checkpoints / final counter |
| --- | --- | --- |
| Native mask around `succeed` | 2 / 2 | 2 / 2 |
| Printed expansion around `succeed` | 5 / 5 | 5 / 5 |
| Outer mask plus native mask | 3 / 3 | 3 / 3 |
| Outer mask plus printed expansion | 6 / 6 | 6 / 6 |
| Native mask around a mapped success | 4 / 4 | 3 / 4 |
| Printed expansion around a mapped success | 7 / 7 | 6 / 7 |

The literal-body five-checkpoint claim has direct finite support on both builds.
Subtracting the outer mask's one checkpoint also preserves that result for an already-masked caller.
However, F6 must call S8's measurements operation-counter differences, not generally loop iterations.
In 4.0.1, `FiberImpl.succeedWith` increments `currentOpCount` while passing success through continuations.
It need not return to the run loop or invoke `shouldYield` at that increment.

The mapped body illustrates this measurement distinction in the host API.
It does not independently refute a particular canonical printed body's machine relation.
Nor does the successful five-checkpoint case establish the proposed machine clauses or arbitrary-body budget agreement.
Name the target release, admitted body, surrounding continuation, and yield observation in that relation.
The new action/node's local clauses can reuse the existing rc.112 machine; the 4.0.1 audit remains relevant to any broader target claim.

## Receipt and limits

`probe.mjs` runs ten ordinary-runtime flag cases, six instrumented count cases, and eight forced-yield cancellation cases per version.
Both commands exit zero with assertions enabled.
Every cancellation case has a no-cancellation control, and every case drains at most fifty scheduled tasks.
`rc112.json` and `v401.json` retain all flags, checkpoints, causes, events, runtime versions, and source/dist hashes.
`receipt.json` records the exact commands, parsed verification, and input/output hashes.

The original mask-probe outputs were read, not overwritten or rerun.
No build, install, generator, Lean execution, active-repository write, UI action, or external message ran.
No test claims fairness, all schedules, completed machine implementation, or unrestricted native-mask agreement.
