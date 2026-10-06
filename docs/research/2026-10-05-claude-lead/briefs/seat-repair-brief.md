# 2026-10-06 brief for seat REPAIR: two small repairs of proofs

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names, which holds seat BRACKET's merge. Both parts are candidates that two receipts left
(decisions row 279, point 5, and row 278, point 5). They are part of the close-out set that
the owner named on 2026-10-06 (row 277). Neither part changes a statement that a consumer
reads.

## Part A. The Queue's typing through the shared rule

Seat SEMW typed the waiting wrapper once, for every module's part: `waitRetryAt_answers`,
`waitRetry_answers` and `protectedBy_has` over `Waiter.Typed`
(`src/Effect4/Laws/Modules/Waiting.lean`). Semaphore's operations use them. The Queue's two
typing proofs were written before, and each unfolds the wrapper by hand: `take_types` and
`offer_types` (`src/Effect4/Laws/Modules/Queue/Ops.lean`).

1. **State `waitAnswer_answers`**, the rule of the wrapper's second form (`waitAnswer`,
   `src/Effect4/Modules/Waiting.lean`), directly after `waitRetry_answers`. Use
   `Waiter.Typed` if it serves. If the answer form needs another premise, give it as a
   premise of the rule, and say why in the docstring. Do not write a second structure
   without a reason that the receipt states.
2. **Prove `take_types` by `waitRetry_answers`, and `offer_types` by `waitAnswer_answers`.**
   Each proof then holds the Queue's part alone: its instance of `Waiter.Typed`.
3. **The two statements do not change**, byte for byte. No battery of the Queue changes.

## Part B. Two general statements move to the lift module

`src/Effect4/Laws/Machine/MaskRuns.lean` holds two statements that do not read the mask
(seat LIFT's receipt, proposal P2): `admittedReplay_true`, and the lift of `flushRootState`,
which is written there for the mask alone (`flushRootState_maskRuns`).

1. **Move `admittedReplay_true`** to `src/Effect4/Laws/Machine/Lift.lean`, with its
   statement unchanged.
2. **State the lift of `flushRootState` in general**, in the form of
   `FoldLift.flushAllState_lift`, in `Lift.lean`. Then `flushRootState_maskRuns` is its
   instance, with its statement unchanged.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `waitAnswer_answers` | `store-typing`; R4, a step of the claim `waiting-wrapper-typed` | the checker's judgment at every typed scope, where the module's part is typed | any run; no law of the mask; no delivery | `Queue.offer_types` |
| `take_types`, `offer_types`, proved again | `store-typing`; R4 | unchanged | unchanged | a client's admission |
| The lift of `flushRootState` | `reactive-scheduling`; R11, a step of the claim `saved-mask-chain-runs` | every invariant that `FoldLift` carries, at every budget | no invariant of its own; an invariant is not progress | `flushRootState_maskRuns`, then `Machine.runSyncExit_maskRuns`; next, each invariant of a whole run at the sync entry |
| `admittedReplay_true`, moved | the same | unchanged | unchanged | the mask's replay law |

## The files, and the rules

- Edit: `src/Effect4/Laws/Modules/Waiting.lean` (one rule, in the section of the wrapper's
  forms), `src/Effect4/Laws/Modules/Queue/Ops.lean`, `src/Effect4/Laws/Machine/Lift.lean`
  and `src/Effect4/Laws/Machine/MaskRuns.lean`. A battery that pins a moved name's axioms or
  plan status changes with it; name each one in the step's message.
- Seats POOLOPS and WORKQ are running. Do not edit a file of Pool's or Semaphore's folders,
  a file under `Test/Dogfood/`, `harness/` or `ocaml/`, or a file under
  `src/Effect4/Machine/`. In `Waiting.lean` add nothing at the file's end: seat POOLOPS adds
  there.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Propose their text in the receipt.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an
  error. No planned goal is allowed in this slice.

**Not in this slice:** the move of the scenario driver's laws into the law graph (seat
CUTS's receipt, proposal 5). It waits for seat WORKQ's merge, because that seat edits the
same files. Also not here: one rule for every stem, a shared definition of the wrapper's
scopes, and a shared builder for a release (row 279, point 5).

## Order, acceptance and the receipt

Two steps, each green and committed: part A, then part B. Send one short message for each.
If a part does not close in its step, stop it, leave the tree as it was for that part, and
say what is missing.

Acceptance:

1. `git diff` shows no change of the statements of `take_types`, `offer_types`,
   `flushRootState_maskRuns` and `admittedReplay_true`.
2. Each touched statement is a theorem at `[propext, Quot.sound]`.
3. Narrow builds after each step; the default `lake build` once at the end, with the gate
   lines; `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

The receipt is `docs/research/2026-10-06-seat-REPAIR-receipt.md`, in the handoff form of
`AGENTS.md`, one page: the one thing to know before merging; base, head and commits; changed
files; commands with results; the axioms; the lines of each proof before and after; and the
sentence that the required property `waiting-wrapper-typed` gains for the answer form. One
paragraph accounts for R1 to R13. Your last message gives the head, the receipt's path and
its first item.
