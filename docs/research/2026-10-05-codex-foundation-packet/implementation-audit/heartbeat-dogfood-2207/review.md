# Dogfood connector review

Reviewed main c3ac5f9c and the new `seat-dogfood-brief.md` during drafting.
Main then reached 944897ed, which commits the brief and changes STATE only.
The inspected implementation files remain unchanged; the final checkout is clean.
The brief appeared during this review and was read once.
This is source evidence, not execution or a claim that the proposed connector compiles.

## Two corrections before dispatch

1. Slice 1 names `Rows.receive` and `Rows.answer` as separate receipt and application.
   `Rows.answer` actually binds, submits and applies the completion.
   After a receipt, use `Run.step (.apply key)` or `Run.play [.apply key]`.
   Otherwise the journal includes duplicate receipt refusals before application.
   The existing P3 driver already uses `.submit` followed by `.apply`.
   Sources: `Run.Rows.receive`, `Run.Rows.answer`, `Runner.Command.apply`, `Runner.result`, and `P3WorkerQueue.step`.

2. Slice 4 sends scripted scenarios through the ordinary truth corpus.
   `Truth.fixtureRun` ordinarily calls `Api.run` with a completion list.
   It does not preserve the scenario's separate keyed receipt and application commands.
   The existing keyed lane already exercises this distinction on actual printed programs.
   Use `harness/truth/session/Keyed.lean`, `run-keyed.ts`, `keyed-recorder.ts` and `check-keyed.ts` as the first host route.
   Do not add a second host runner.

## Smallest engine connection

The production `E4_engine.INSTANCE` interface takes a program but no row table.
Both `api_engine_inst.ml` and `api_engine_ref.ml` fix the table to `[]` in `interp_of`, `step` and `run_api`.
This prevents their existing wrapper from running the proposed host rows as supplied.
The `[]` in `load` is an answer list, not a table. Compilation itself does not take the table.

The generated `api_replay` already takes the program, command fuel, decision tape, answers, row table and compile fuel.
A test-local adapter calling this function is smaller than changing the production engine interface.
It can operate on both generated instances and keep `answers=[]`.
The existing `Eff_wire.decode_row` provides the row's wire reader.
The remaining transport work is the checked conversion from decoded wire rows into the generated instance's row type.
`E4_program` currently converts programs, not this row table.
Bind the real table bytes to the admitted Lean fixture; do not silently use a hand-invented table.

Project machine transitions from accepted HostSession steps, never from receipt records alone.
A positive scenario with sufficient budgets can compare after each progressed control and applied answer.
A refused receipt leaves the machine unchanged and remains visible in the session observation.
A zero-budget application leaves its reply pending.
A frontier can require a separate treatment: `applyReply` may change the machine while not consuming the selected reply.
Do not flatten a frontier into a successful application or discard its remainder.

## Observation boundary

The full worker observation includes pending replies, consumed calls, retirement and cleanup identities.
The current generated engine has no HostSession pending/retired/consumed storage.
Raw `api_replay` therefore checks only the named machine projection.
Copying Lean's session metadata into the OCaml result would not test an OCaml session implementation.

The smallest honest landing has two placed clauses:

- the existing session protocol observation, checked in Lean and the keyed printed host lane;
- the explicit machine projection, checked by the table-aware generated replay.

The OCaml session clause stays waiting unless a later bounded session adapter or lowering carries those transitions itself.
This follows the brief's rule that a lane unable to carry the script is a finding.
It does not silently weaken row 254's requested whole observation.

## Existing host controls worth reusing

`KeyedTool.two` creates two parked calls.
`KeyedTool.shared` resumes calls that write shared state.
`run-keyed.ts` receives answers in AB and BA order, and separately tests reversed application for `shared`.
`check-keyed.ts` compares ordered exits, exact application order, pending calls and replies, and zero oracle answers.
`KeyedRecorder.external` checks actual row/request starts and a bijective runtime/semantic fiber association.
`arrive` runs the real host work and stores its exit. `apply` resumes the selected Effect callback.
These are live host controls, not merely replaying prefilled Lean answers.

The binding plan remains supplied from one finite Lean schedule.
These runs do not establish all host schedules or general host adequacy.
The recorder currently rejects an operation that completes after cancellation.
Late-completion cleanup therefore needs a separately scoped control; it is not already covered by this route.

## Placement and immediate prerequisite

- Session clauses reuse `host-session-protocol` claims `reply-commute` and the admission claims, under R6.
- The projected replay clause belongs under `translation-simulation`, serving R8/R13.
- Identity-sensitive cleanup remains a `scope-lifetime-finalization` clause under R11.
- State the projection, actual table, budgets, value profile and accepted-phase premises before assigning a goal.
- Keep receipt/application, safety/progress, and finite execution/proof distinct.

Before dispatch, correct the receive/apply spelling and name the keyed host route.
Then let DOGFOOD report the table and session connector limits without changing production APIs outside its fence.
No new generic infrastructure is needed for the first two-call control.
