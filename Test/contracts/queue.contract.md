# Abstract Queue transition contract

Status: integrated on 2026-10-05. Codex prepared the packet, and the coordinator built it.
The model's base is `da41297b95f21b7cfef08b4cb54edf5bf7d8c8b1`.
This packet freezes the corrected abstract model for Queue proof preparation.
It authorizes no additional runtime behaviour.

| Part | Evidence on 2026-10-05 |
| --- | --- |
| `Test/Program/QueueModel.lean` | tested: it builds under the battery's options |
| `Test/Program/QueueContract.lean` | tested: its guard checks hold |
| `acceptLoop_length_le` in `Test/Program/QueueCapacity.lean` | proved, at `[propext, Quot.sound]` |
| `positive_suspend_step_capacity` in the same file | proved, at `[propext, Quot.sound]`; its plan status is `proved` |

## Authority and owned surface

Decisions rows 219–222, 230, 235 and 238–243 own the selected Queue contract.
Row 251 orders the public implementation after FOLD, T5 and the mask.
The corrected research contract remains the detailed API specification:
`docs/research/2026-10-05-claude-lead/queue-contract/queue-contract.md`.

`QueueContract` in `Test/Program/QueueModel.lean` is the abstract transition model.
Its definition bodies come unchanged from the research model at this packet's base.
The extraction retains their exact bytes and hashes.
It adds no program representation or production Queue.

`Test/Program/QueueContract.lean` retains the small named controls.
The separate `QueueLargeControls.lean` retains both million-element controls and the bounded exploration.
It sits beside the research model, in `docs/research/2026-10-05-claude-lead/queue-contract/`.
That file is not an ordinary Test import.

## State and operations

The state contains the message buffer, optional capacity, strategy and terminal phase.
It also contains ordered waiting takers and offers, plus peekers and end awaiters.
An operation returns the changed state, its reply and the signals it emits.
No model operation delivers a signal.

| Rule | Abstract definition |
| --- | --- |
| No bound is represented by `none`, never a numeric sentinel | `room`, `fit` |
| A consuming request passes no earlier taker | `earlier`, `take`, `poll`, `clear` |
| Consumption occurs in the receiver's step | `pull`, `take`, `poll`, `clear` |
| Pending offers enter in arrival order | `acceptLoop`, `accept`, `afterConsume` |
| An offer signal carries its decided answer | `answerOf`, `acceptLoop`, `shutdown` |
| Closing drains before done; shutdown discards retained messages | `settle`, `close`, `shutdown` |
| Withdrawal removes only the pending request or offer suffix | `withdrawTake`, `withdrawOffer` |
| Every removed terminal request has an emitted signal | `accounted`; exact terminal controls |

The native reference is `vendor/effect-4.0.1/src/Queue.ts`.
The names `canTake`, `releaseCapacity` and `takeAllUnsafe` supply the compared batch and room behaviours.
`offer`, `offerAll`, `take`, `poll`, `clear`, `failCauseUnsafe` and `shutdownUnsafe` are the compared public-operation paths.
`end` connects normal end with `core.Done()`.
The counterpart source is retained in `vendor/effect-4.0.0-rc.112/src/Queue.ts`.
The model is the ruled contract, not a claim that every native operation agrees.

## First profile and frame

The first public path uses a positive capacity and the suspend strategy.
It performs each state transition through one `Ref.modify` with a pure binder term.
It posts one detached helper for each signal occurrence.
The wrapper, request identities, hint renewal and saved mask are outside this abstract model.

The capacity and strategy stay fixed through each abstract step.
The model represents messages and failure payloads by natural numbers.
An implementation at another payload type owes an encoding and an explicit state relation.

General request-order and ownership proofs require fresh request identities and immutable bounds within a request.
The wrapper must establish those premises.
The capacity helper itself requires neither identity freshness nor a scheduler.

## Proof placement and first obligation

| Field | Statement |
| --- | --- |
| Concept | `reactive-scheduling`: preservation of an explicit state invariant |
| Registry claim | A helper of R10's proposed `queue-expansion-agrees`, on its abstract-client side |
| Immediate consumer | `positive_suspend_step_capacity`, followed by the later Queue term-to-model refinement |
| Helper proposition | `(acceptLoop (some r) ms os).1.length ≤ ms.length + r` |
| Step proposition | Positive fixed capacity, suspend strategy and a bounded initial buffer imply unchanged configuration and a bounded final buffer |
| Observation | Buffer length and the capacity/strategy fields after one fault-free abstract step |
| Decrease | Structural recursion over the pending-offer list |
| Frame | No world, store, fiber, host object, task or service context is represented |
| Prerequisite | Freeze the exact model and place the goal before proving the helper |
| Exclusions | No signal delivery, liveness, FIFO progress, typed store preservation, target execution or native Queue agreement |

`Test/Program/QueueCapacity.lean` holds the step proposition with its placement.
It was a placed `proof_goal`, and the coordinator proved it on 2026-10-05.
Its steps are the helper and one lemma for each operation of the model.
The helper is proved there. The coordinator rewrote its proof: Codex's draft did not compile.
The draft is kept beside Codex's packet, as `QueueCapacity.lean.candidate`.

The step's proof does not use the premise of a positive capacity.
The statement holds at capacity zero too, and it stays as this packet froze it.
A proposal to drop the premise waits for review.

The file pins the full statement, the `#plan_status` output and the exact axiom output.
They use the existing semantic ceiling and the actual proof dependencies.
Do not count placement metadata as a proved dependency.

## Controls and falsifiers

The retained named controls pin strict order, consumption, closing, cancellation and decided offer answers.
They also cover zero bounds, nonblocking operations, batches, terminal signals and the ruled zero-capacity profile.
The fixed operation lists and depth-five exploration remain finite evidence.

The exploration has two deliberate mutations.
Suppressing closing signals breaks `quiet`.
Suppressing shutdown signals leaves the state invariants true and breaks `accounted`.
Their exact source bodies remain in the retained large-control file.

The capacity proof's future acceptance includes an empty offer list and zero remaining room.
It also includes partial acceptance, several fully accepted offers, and a full-buffer positive control.
A variant that appends despite zero room must fail the capacity check.
These Lean acceptance controls are in `Test/Program/QueueCapacity.lean`, one input each.
The step's statement has five more there: three steps that keep the bound, and two red controls.
One red control starts above the bound. The other runs `sliding` at capacity zero.
An independent Python mirror covers six named cases and 3,744 grid cases, and rejects the deliberate append mutation.
It does not establish source agreement or a Lean proof.
The mirror and the extraction validator are kept in
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/open-questions-review/queue/package/`.

The extraction validator has separate controls.
It accepts the exact split, rejects a changed model body and rejects a missing control file.
Those results verify provenance only.

## Remaining connectors

1. Relate the typed cell encoding and actual binder term to this abstract state transition.
2. Reuse `termMaps_of_typed` and `syncRow_typed` for the one atomic update.
3. Prove registration, notification ownership, hint renewal and withdrawal over the actual wrapper.
4. Keep accepted offers committed when interruption wins before the caller receives the answer.
5. Relate every posted signal to its receiver, including terminal signals after request removal.
6. Supply an embedded budget covering reached receiver continuations, or state the admitted-client restriction.
7. Check and relate the actual emitted expansion after T5 and the mask land.

These connectors remain open.
Neither `quiet` nor `accounted` proves them.
The packet does not change the repository pin or reopen the signed native differences.
