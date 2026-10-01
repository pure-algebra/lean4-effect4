# H1 halted-code amendment draft

The two-fiber queue-discard example is resolved by treating saved current code as inert once the machine is halted, and by stating each command obligation at the exact running-machine dispatch boundary already used by `Machine.Lift.StepKeeps`. This draft changes no runtime code, does not require an empty halted queue, and adds no reachability or whole-transition premise. Root owns all Lean checking and integration; this seat has performed static review only.

The source overlay starts from the four checked H1 files in `after-addendum-6/H1/checked-source`. The integration base observed was `57c93ba45ec9fccb728a440cf6d1705a246a3d59`. `source-map.json` pins the old checked candidate and new source hashes. The `source.patch` was made against the restored live source before root applied it. Do not regenerate that patch against a partially integrated tree.

## Exact amendment

`Assembly.lean:84`: `CodeInert m commands position := m.stuck.isSome = true ∨ TerminalPosition m commands position`.

`Assembly.lean:91`: only the `TypedProg` requirement becomes conditional on `¬ CodeInert`. The existential intermediate type, actual saved stack, `StackAccepts`, and `InterruptProvenance` remain mandatory. `WorldValid`, generated data clauses, `ActiveDelivery`, `SchedulerState`, `ObserverState`, `RegistrationState`, and all nine `QueueOk` fields are unchanged. The original queued/published-exit definition remains unchanged.

`Assembly.lean:181`: `StepPreserves` takes `m.stuck = none` before the complete state and queue judgments. This is the same operational dispatch condition as the existing `Lift.StepKeeps` (`Laws/Machine/Lift.lean:46–78`). It is neither a reachability restriction nor a new postcondition supplied by the caller.

`stepKeeps_of_stepPreserves` and `driveState_typed_of_stepPreserves` assemble the existing generic lift. Both require the entire command family as hypotheses. None of the eighteen command obligations, the decision obligation, or the capstone is discharged.

One source comment can be made more precise during integration: replace “Only dispatch through the command loop reads this code” with “The executable command loop checks halt before dispatch”. Raw `driveStep` remains callable and does read code; its omission is independently attacked below.

## Native boundary and decision review

- `Machine/Fibers.lean:1826` drops the queue on `Outcome.stuck`. The stored halt, rather than the lost queued finish, must then justify the inactive current-code slot.
- `driveStep` at 1846 does not check machine halt. The actual `driveState` at 1998–2008 checks it before dispatch and retains `(machine, commands)` for any pending queue.
- `link` at 1980–1982 and `observe` at 1964–1966 can retain a suffix on a halting path. Requiring an empty queue for halted states would reject these real paths.
- `fireState` at 2035 can drain/disarm dispatcher bookkeeping; `fireStep` at 2026 can emit `ranTask` while halted, but invokes guarded `driveState` for execution. Global identity of all decisions is not claimed.
- `flushAllState` at 2047, `advanceState` at 2065, and `flushRootState` at 2083 check halt before further work.
- `prepareAsyncAnswer` at 2100 skips current-code inspection on halt. `stepDecisionState` at 2111 routes evaluate/answer/interrupt execution through `driveState`.
- `yieldVerdict`, `installMiddleware`, and `interruptFrom` can change non-code data while halted. `interruptRecord` at 803–824 can record an interrupt, clear a park and pending callbacks, or replace current code. Their data, observer, registration and provenance preservation remain explicit M6 work. The amendment does not exempt those fields.
- `replayEval` at 2188 stops on a halt before taking another decision.

This change proves no progress/no-halt result. The halted result still records `unknownScope 0`. It only assigns a faithful typed-state meaning to the code slot that the actual runner will no longer execute. The existing H1 direct code-site scan remains OPEN; no arbitrary-continuation quantification or scanner is introduced.

## Controls

`TerminalPositive.lean` refreshes the checked normal-terminal control for `CodeInert`: complete input/output state and queue after delivery, the stale code retained before finish, the published-exit saved position after finish, and the original pre-row-133 negative statement retained under local historical definitions.

`QueueHaltPositive.lean` contains:

- The original two-fiber input, callback typing, full state and queue admission.
- Local `OldSavedPosition`, `oldStatePreds`, `OldTypedState`, `OldStepPreserves` matching the checked row-133-only definitions. `output_not_typed` and `step_deliver_false` preserve that historical counterexample.
- The actual halted output fiber shape; complete `WorldValid`, generated saved/data predicates, scheduler/observer/registration checks; `result_typed commands` for an arbitrary pending queue. Queue validity remains separate.
- `deliver_preserves_this_state`, with the actual non-halted input, later world, full output typed state, and output queue.
- `halted_loop_retains_any_queue`, a finite-machine control universally quantified over fuel and queue.
- `raw_input_queue` admits a direct root delivery on the halted output. Raw `driveStep` reads the stale Nat current code and enqueues a Nat finish at a Unit root. `raw_output_untyped` and `unguarded_step_false` show that omitting the dispatch condition would be false. This is why the condition is needed; the real loop never dispatches that raw call.

Every theorem in each control has an axiom print. `LiftAxioms.lean` prints both new production adapter theorems. These are drafts until root's serialized command results are recorded.

## Root-only serial commands

Run in `/Users/pooks/Dev/lean4-effect4-slice6` after applying the four-source overlay, one command at a time:

```sh
lake build Effect4.Laws.Program.Typed.Assembly
lake env lean -DwarningAsError=true /private/tmp/h1-halt-resolution/TerminalPositive.lean
lake env lean -DwarningAsError=true /private/tmp/h1-halt-resolution/QueueHaltPositive.lean
lake env lean -DwarningAsError=true /private/tmp/h1-halt-resolution/LiftAxioms.lean
```

Root owns migration into M6Capstone/ValueMembership, status wording, retained evidence and final source/test checks. This seat made no worktree changes and ran no Lean, lake, make, generator or test command.
