# Pool: initial design and proof scouting

Role: advisory source review. Evidence: committed source and retained seat activity and build output.
Main snapshot: `3a2616f1b01a8fcfb22caf993a425f9306f4cc8a`.
Seat snapshot: `c957bfab708d6b1b924356c6c28ca2769f66cb99`, branch `seat/pool`, clean.

## Current result

POOL was dispatched at 12:34:23 UTC. The dispatch names the former REFS worktree and the corrected brief.
It repeats both Pool corrections: allow idle items beside enrolled waiters, and separate PP5's two domains.
The public transcript shows the seat reading the brief, card, shared laws, prior reviews and wake implementation.
No Pool design note, scenario battery, contract, model or cell exists at this snapshot.
There is therefore no new Pool implementation or design choice to judge yet.

The saved `base-build.log` ends with `Build completed successfully (990 jobs).` and `exit=0`.
The command is the seat's slot-managed default build at the unchanged base.
This is baseline evidence, not acceptance of Pool. The monitor ran no build.

Rows 267–269 still govern eager acquisition, protected use, waiting close and front insertion on return.
The brief and card include the `e7034464` corrections. No previous finding needs repeating.
MASKPOP remains written and undispatched in the current tracked STATE.
Main's active PUB/truth/Makefile changes are outside this review.

## One optional next proof route

After the initial machine cases pass and the seat fixes the model and reply shape, start with counted selection.
This is the brief's atomic model step: remove one selected prefix, then return those selected records for later ordered notification.
It is not a theorem about native Pool's callback traversal or the helper's whole execution.

Let `W` be the current waiter list and `n` the requested count.
Use `selected = W.take n` and `remaining = W.drop n`.
The cell changes only its waiter field. The step returns the selected records, including their current hints.
No fold is required for this selection itself.

The existing pieces already cover its mechanical proof:

| Existing owner | Reuse |
| --- | --- |
| `src/Effect4/Laws/Modules/Reading.lean` | `reads_field`, `reads_take`, `reads_drop`, `reads_recordSet`, and `reads_pair` |
| `src/Effect4/Laws/Modules/Checking.lean` | `types_field`, `types_take`, `types_drop`, `types_recordSet`, and `types_pair` |
| `src/Effect4/Laws/Modules/Table.lean` | The existing model-identity to handle/current-hint table, unchanged by selection |
| Lean 4.33.1 `Init/Data/List/TakeDrop.lean` | `List.map_take`, `List.map_drop`, and `List.take_append_drop` |
| `src/Effect4/Laws/Modules/Store.lean` | `step_updates` for one atomic update; `step_keeps_cell` for its separate membership result |

`List.map_take` and `List.map_drop` connect selection before encoding with selection after encoding.
These names were checked in the installed compiler source; no compiler ran.
The standard list laws avoid adding another list induction or Pool-specific list library.

Proposed statement shape, not compiled:

`Reads selectionStep env path vals
  (pair (encodeWaiters tb (W.take n))
        (cellVal tb { s with waiters := W.drop n }))`.

The concrete source arguments and field equations follow the seat's design; no implementation is prescribed here.

- **Placement:** `translation-simulation`, R10, one step of the proposed `pool-expansion-agrees`.
- **Required property:** the atomic term agrees with the model's selected records and next cell.
- **Consumer:** the later wake helper and public expansion law. Prefix order feeds proposed `pool-wake-selection`, R12.
- **Premises:** source terms read the current cell and a natural count; canonical cell encoding; fixed table for this step.
- **Typing premises:** the native atom table and typed inputs, using the existing `TypesEach` rules.
- **Observation:** the exact selected records and stored value, with every other field framed.
- **No unnecessary premise:** prefix selection compares no identity, so its reading proof needs no table injectivity or fold-capture hypothesis.
- **Separate obligations:** withdrawal and identity tests still require their own table/capture premises. Do not remove them there.
- **Exclusions:** delivery, cancellation, native callback agreement, general public reachability, fairness, cleanup completion and liveness.
- **Immediate prerequisite:** part 1's cases pass; the design note fixes selection's state and reply shape; the planned goal receives its placement.

Keep the domains from the corrected brief. An open public return posts count 1; close posts all only after refusing leases.
The count-2 PP5 fixture has explicit constructed-state and helper-count premises.
A local take/drop proof on arbitrary counts does not turn that fixture into a reachable public schedule.

Possible later controls, all unrun here: count 0, count 1, count beyond the list length, and duplicate resource values with distinct waiter identities.
A changed removal count or reversed selected order must fail the exact reply-and-state observation while remaining typed.
The returned hint records come from this selection. Their later delivery must not silently reread a renewed table entry.
That delivery connection belongs to the helper law outside the current atomic step.

## Delivery and evidence

This is optional guidance for the coordinator to hold until the design exists. No new defect or urgent advisory was found.
The UI is unavailable to the parent this check; no delivery is claimed.
The packet keeps fifteen source hashes, the exact dispatch, recent public tool activity and the saved baseline log.
Fourteen repository files match their frozen commits; the remaining source is the installed standard-library file.
No repository edit, Lean check, compiler, runtime, generator, installation, seat dispatch or Claude message occurred.
