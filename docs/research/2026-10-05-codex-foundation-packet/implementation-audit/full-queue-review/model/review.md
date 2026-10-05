# Queue transition model review

Keep the three authorized policy choices.
Repair the artificial one-million limit before promoting this model as the whole Queue contract.
The source currently contradicts its unbounded configuration and its `clear` description on reachable inputs.

Evidence status: 15 Python assertions pass under Python 3.13.14.
The probe mirrors only the named transition fragments; no theorem relates the Python mirror to Lean.
The reviewed model commit is `a3954d03f2787b856e4f13c6eb63573cac885e34`.
The final recheck reaches `e7bdbba8f0cd4cffe62d5438334ab3767ca55d61`; the model and retained output are unchanged.
The contract note now records the owner rulings in decisions rows 240 to 243.
No Lean invocation, build, generator, installation, or repository edit occurs.

## Required model correction

`room` maps absent capacity to `1000000`.
`offerAll` uses that value to decide how much an unbounded queue accepts.
`clear` independently passes `1000000` to `pull`.
Neither the stated domain nor `formed` limits a list's length.

| Reachable trace from an empty unbounded queue | Observed result | Contract conflict |
| --- | --- | --- |
| `offerAll` with `List.range 1000001` | Buffers 1,000,000 values; keeps one pending; answers wait | An unbounded batch blocks; `tidy` is false because `room` remains 1,000,000 |
| `offerAll` with `List.range 1000000`; ordinary offer of 1,000,000; `clear` | Returns 1,000,000 values; leaves the final value buffered | `clear` does not drain every buffered message |

The first trace needs one transition.
The second reaches its input through two immediately accepted offers.
The positive controls use exactly 1,000,000 values; the batch succeeds and `clear` empties that buffer.
The probes retain full input formulas and summarized outputs, without storing a million-value JSON array.

Smallest correction: handle absent capacity explicitly when accepting offers, and clear the buffer's actual length.
Do not silently restrict the Queue's public domain to make the sentinel valid.
The same absent-capacity correction applies to `dropping` batches, whose code also calls `room`.

Declarations: `room`, `formed`, `offerAll`, `clear`, `pull`, and `tidy` in `QueueContract.lean`.

## Terminal search boundary

The actual `shutdown` answers pending takers, peekers, offerers, and awaiters.
No missing terminal signal is verified in that function.
However, `within`, `tidy`, and `quiet` cannot detect deleted terminal signals after the request lists are cleared.

A reachable prefix is: empty queue; `take 1 1 1`; `peek 5`; `awaitQ 7`; `shutdown`.
The actual output names taker 1 and peeker 5 with `again`, and awaiter 7 with the interrupt end.
The positive control checks all three signals.
A deliberate mutant returns the same final state with no signals; all three search predicates still pass.
This is a coverage limitation, not evidence that the unmodified model loses a notification.

Before freezing the packet, add exact-output terminal controls covering all request classes, including cancellation that empties a closing rendezvous queue.
Pair them with a terminal signal-deletion control.
Keep notification ownership and delivery as separate wrapper obligations.

Declarations: `shutdown`, `settle`, `withdrawOffer`, `within`, `tidy`, `quiet`, and `bump` in `QueueContract.lean`.

## Small documentation correction

At capacity zero, `offer 100 10` stays pending with an empty buffer.
`clear` then receives `[10]`, removes that offer, and signals `offered true`.
The empty-queue positive control returns `[]`.
This agrees with installed 4.0.1's `clear` and `takeAllUnsafe`; it is not an additional native divergence.
F2 and F3 should describe this one-message rendezvous branch instead of describing only buffered messages.
Strict no-bypass still applies when a taker waits.

Declarations: `clear`, `pull`, and `front` in `QueueContract.lean`.
Native declarations: `clear` and `takeAllUnsafe` in the installed 4.0.1 `src/Queue.ts`.

## Retained exploration scope

The source contains 32 `#guard` commands: 28 before exploration, three configuration checks, and one red control.
The retained output contains eight successful entries, each reporting 177,156.
That count equals all prefixes through depth five over the eleven listed commands.
The commands fix request identities, values, and bounds; they do not range over all inputs.
The exploration excludes `awaitQ`, peeker withdrawal, awaiter withdrawal, and failed or interrupted close reasons.
Direct controls cover some excluded operations and reasons.
The original red control detects a closing queue that omits ready-taker hints.
It does not establish the terminal notification property above.

No retained exploration is rerun here.
`receipt.json` pins its source and output; `probe.py` and `results.json` retain the independent finite checks.
The three policy choices need no further approval from this review.
