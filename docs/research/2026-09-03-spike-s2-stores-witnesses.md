# Spike S2: the stores, the `RunInterp`, and the executable witnesses

Status: spike report, 2026-09-03, **third pass** (the nine findings of the first pass and the
two residuals of the second are all applied in the carrier; this pass is the port onto it, and
leaves no finding open). Base commit `6d83533` (`main`). Row S2 of
`docs/research/2026-09-03-deep-plan.md`. Inputs read in full: `workshop/Deep/Fibers.lean` (third
pass), the new `Prim` parking constructors and `PrimInterp.cancelThenFail` in
`Effect4/Runtime/Runtime.lean` (spike S1),
`docs/research/2026-09-03-fiber-machine-pass-a.md`,
`docs/research/2026-09-03-deep-state-models.md` §2 and §3, `docs/RUNTIME-COVERAGE.md`,
`generated/effect-runtime-census.tsv`, the four `generated/traces/fiber/race*.tsv` goldens, and
the pinned `vendor/effect-4.0.0-rc.112/src/{Ref,MutableRef,Deferred,Scope}.ts` and
`internal/effect.ts` spans cited below.

Files, both under `workshop/` and therefore outside every `lean_lib` the trust tokenizer and the
module-closure gate see, exactly as ruling 1 of the plan requires:

| File | Module | Lines | Theorems |
| --- | --- | ---: | ---: |
| `workshop/Deep/Stores.lean` | `Deep.Stores` | 1425 | 61 (+9 `example` separation gates) |
| `workshop/Deep/Witnesses.lean` | `Deep.Witnesses` | 835 | 53 |

## Summary

1. **Both modules build on the revised carrier.** `lake build Deep.Stores Deep.Witnesses` is
   green on Lean 4.33.1. No bare `lake build`, no sweep, no trust gate, no `Deep.ForkFlow`.
   **There is no `sorry`, no `native_decide` and no custom axiom in the spike**; the axiom
   receipt of every witness is `propext, Quot.sound` (and `propext` alone for the `rfl`-proved
   ones), which is what `docs/RUNTIME-COVERAGE.md:52-55` requires of a witness.
2. **`St := Stores`** is the Ref heap, the Deferred store, the keyed `Effect4.Scope` store and
   one fresh-name counter; `stores : RunInterp Name Thunk Val Err Defect FiberId Ann Ctx Stores`
   fills every field of the revised interp — including `cancelThenFail`, `cancelName`,
   `abortName`, `exitsValue`, and the three `Option`-valued scope hooks — at concrete
   first-order alphabets, and `DecidableEq` derives for every one of them, so the four
   separation gates of `Deep.Fibers` still hold at this instantiation.
3. **All 22 `ref.*` and `deferred.*` census clauses are stated.** With M2 and M3 applied,
   `deferred.into-uninterruptible`'s mask clause and `deferred.await`'s cleanup clause are no
   longer blocked, so the two rows this spike previously called partial are now fully stated;
   `deferred.complete-runs-once`'s "memoized" half is the only clause still unstated, and it is
   a statement about running a stored effect twice, not a carrier gap.
4. **All four positive Pass A examples run to the expected exit**, on explicit tapes, checked by
   `decide`/`rfl`, and all five forbidden examples are shown unreachable or refused — two of them
   as facts about the step function rather than about one tape, which is the stronger form.
5. **Every finding of this spike is closed** — the nine of the first pass and the two residuals
   the first port turned up (M1's exit-path half, and M10, `linkScope`'s annotations for
   `fiberRunIn`). §5 records what each now looks like and which witness assertion moved. Six new
   witness groups exercise the mechanisms the changes created; **nothing in §5 is open**.
6. **DB-07 is stated beside the interp** in the `Deep.Stores` header and witnessed by
   `db07_store_survives_failure`: a program that writes a Ref and then fails leaves the write in
   the machine's store.

Nothing in this report is a coverage number. No census row is claimed green; the spike makes
clauses *statable*, and the landing is where a row's state may move, under the
`runtime-coverage` procedure.

## 1. What was built

### 1.1 The alphabets (`Deep.Stores`)

All at `Type 0`, so `u = v = 0` and `St : Type 0`. Declaration order is forced by the
dependency chain and is the one place the design had to bend (see §1.5):

```
RefKey, DeferredKey, Err, Defect, Ann(=Unit), FnName, FinName, Ctx
  → Val → CauseV/ExitV/VoidExitV → Completion → SyncOp → RaceName → ProgName
  → Name → ActionName → Thunk → Program := Prim Name Thunk Val Err Defect FiberId Ann
```

* `Val` — `unit`, `nat`, `bool`, `fiber`, `fibers`, `cell` (the `MutableRef` that `Ref.set`
  answers, `Ref.ts:307`), `promise`, `scopeHandle`, `context`, and `exitOk`/`exitErr`, which are
  `reifyExit`'s image. `exitErr` carries a `Cause Err Defect FiberId Ann`, which does not mention
  `Val`, so the recursion is direct and `DecidableEq` derives.
* `Name` (ν) — one alphabet for all three of rc.112's function slots: continuations
  (`restore (exit)`, `merge (exit)`, `seq (next)`, `joinOn (mode)`, `interruptWith (cell)`,
  `doneInto (cell)`, `constant`, `exitOfValue`, `awaitNew (snapshot)`, `snapshotThen (body)`),
  async registrations (`registerAwait (cell)`, `cancelAwait (cell)`, `externalRegister (slot)`),
  finalizers (`finalizerName (fin)`), the cancel names M3 needs
  (`withWaiter (base) (waiter) (token)`, `abortController`, `reFail (cause)`), and the two close
  chains (`closeSeq (remaining) (exit) (captured)` and
  `closePar (remaining) (exit) (forked) (closerInterruptible)`, ending in `mergeAwaitedExits`).
  The close-chain names carry the accumulated `Reason` list and the forked ids, which is why
  "failures captured, not thrown" is data and not a closure.
* `Thunk` (σ) — `park (kind : ParkKind)`, `act (action : ActionName)`,
  `op (operation : SyncOp)`, `body (program : ProgName)`. Since S1 landed the three parking
  constructors, `ParkKind` is only `join`, so `parkOf` classifies exactly
  `Prim.suspend (Thunk.park (ParkKind.join …))`; `yieldNowWith` and `async` are `Prim`
  constructors the loop matches directly. `withFiberOf` recognises exactly `Thunk.act`;
  `syncState` exactly `Thunk.op`.
* `SyncOp` — 26 arms, one per rc.112 store operation, each cited by `path:line`.
* `ProgName` — the declared programs; `progOf` is the interpretation. `ActionName.fork` and
  `raceAll` carry a `ProgName`, never a `Prim`, so the thunk alphabet stays first-order.
* `Ctx` — `ambientScope : Option Nat`, `maxOpsBeforeYield`, `preventYield`: exactly what rc.112
  reads off the context (`internal/effect.ts:726-727`, `:5400-5406`).

### 1.2 `RefHeap`

`abbrev RefHeap := List Val`, with `refPeek`/`refPoke` and one `refStep : SyncOp → RefHeap →
Option (Val × RefHeap)`. `none` is a frontier — a key no allocation of this heap minted — never a
typed error (`AGENTS.md`). Every arm is one `Effect.sync` thunk, so a read-modify-write's read
and write happen with no intervening runtime step.

### 1.3 `DeferredStore`

```lean
structure DeferredCell where completion : Option Program; waiters : List (FiberId × Nat)
structure DeferredStore where cells : List DeferredCell; due : List (FiberId × Nat × Program)
```

`complete` (`Deferred.ts:1648-1662`) answers `false` and changes nothing on a second attempt,
otherwise stores the primitive, **clears the waiter list in the same state the owed-resume list
is read from**, and appends one resume per waiter in registration order. `due` is the queue
`RunInterp.dueResumes` drains, and `register` is the store half of `registerAsync`
(`Deferred.ts:173-177`): resume at once with the stored effect when done, else park.

`interrupt` is spelled `Prim.onSuccess (Prim.withFiber (Thunk.act ActionName.getId))
(Name.interruptWith cell)`, whose `contA` on `Val.fiber id` is
`Prim.sync (Thunk.op (SyncOp.deferredInterruptWith cell id))` — `WithFiberAction.getId` then a
completion, exactly as the task asked; W4 shows the recorded interruptor is the *completing*
fiber (`Deferred.ts:1231-1232`).

### 1.4 `ScopeStore`

Keyed `Effect4.Scope Nat FinName Val Err Defect FiberId Ann`, reusing `Scope.make`, `addExit`,
`removeUnsafe`, `closeState`, `closeResult`, `closeOrder` and `fork` unchanged. The finalizer
name alphabet is

```lean
FinName := interruptFiber (fiber) (skipSelf) | closeChildScope (scope)
         | detachFromParent (parent) (key) | release (label) (fails) | parkThen (slot)
```

so `scopeStatus`, `scopeLinkFiber`, `dropFinalizer` and `closeScope` are store operations, and
the open half of `SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`) is closed: a finalizer
name *means* `scopeClose(child, exit)` or `scopeRemoveFinalizerUnsafe(parent, key)`
(`scopeStore_forkChild_names`). A fiber finalizer compiles to
`WithFiberAction.interruptScoped f` (`interruptFiber_compiles_to_interruptScoped`).

`storesCloseScope` writes the state first (`internal/effect.ts:3784`) and then builds the close
program by strategy:

* **sequential** (`:3813-3818`) — the `closeOrder` finalizers as an `onSuccessAndFailure` chain;
  `contA` continues with the rest, `contE` continues with the rest and the failing cause's
  reasons appended, so a failure is captured and never thrown; the empty remainder answers
  `Prim.ofExit (voidAllOf captured)`, the `exitAsVoidAll` shape.
* **parallel** (`:3819-3826`) — each finalizer is forked as `⟨startImmediately := true,
  daemon := true, mask := the closer's⟩`, the ids are threaded through the chain name, then
  `WithFiberAction.awaitAll` and, since M6, the merge of the exits the countdown *answered*
  (`Name.mergeAwaitedExits` over `Resume.exitsValue`), not of a store side-channel. The
  `ScopeEntry.collected` field and the two `SyncOp` arms that fed it are gone.

`RunInterp.closeScope`, `scopeLinkFiber` and `dropFinalizer` are `Option`-valued now, so an
unknown key is a frontier the machine turns into `Stuck.unknownScope`; `storesCloseScope_unknown`
and `scopeLinkFiber_unknown` state that, and W13 runs it.

### 1.5 The one place the design bent

`ActionName` must carry a program for `fork`/`raceAll`, and `Thunk` must carry an `ActionName`;
if `ProgName` carried an `ActionName` back the two would be mutually recursive. It does not:
`ProgName` is a plain recursive alphabet and `progOf` builds the `Prim.withFiber (Thunk.act …)`
term directly. For the same reason `raceAll` carries a `RaceName`, not a `List ProgName`: a
`List ProgName` field would make `ProgName` a *nested* inductive whose `DecidableEq` handler
refuses, which the state note already recorded at §3.5 for `LayerDesc.mergeAll`.

## 2. Every witness, with its tape and its result

Fuel is 400 for every witness. All values below are the ones the modules assert; each was first
read off an `#eval` probe and then frozen as a `decide`/`rfl` theorem, so expected and computed
are equal by construction of the build.

Ids: the root is `⟨0⟩`; children are minted in fork order.

| Witness | Tape | Expected = computed | Theorem |
| --- | --- | --- | --- |
| **W1a** fork deferred + join | `evaluate 0; fire 0` | parent `success (nat 42)`, child `success (nat 42)`, 2 fibers | `w1_deferred_join_parent`, `w1_deferred_join_child` |
| **W1a′** the start is a task | `evaluate 0` only | child exit `none`, parent's dispatcher `armed = true` | `w1_deferred_start_is_a_task` |
| **W1b** immediate start | `evaluate 0` | both `success (nat 42)` | `w1_immediate_join` |
| **W1c** `await` a failing child | `evaluate 0` | parent **succeeds** with `Val.exitErr (fail (tag 7))` | `w1_await_is_a_value` |
| **W1d** `join` a failing child | `evaluate 0` | parent **fails** with `fail (tag 7)` | `w1_join_is_an_effect` |
| **W2** masked interrupt | `evaluate 0; interruptFrom (some 0) 1; answerAsync 1 0 unit` | child exits `failure (interrupt (some ⟨0⟩))` delivered at the unmask frame; one `interruptRecorded` row `(some 0, 1)`; `finalizerRuns = 1` | `w2_delivered_at_unmask`, `w2_recorded_once`, `w2_finalizer_runs_once` |
| **W2′** not applied while masked | `evaluate 0; interruptFrom (some 0) 1` | child exit `none` — recorded, deferred, not applied | `w2_masked_interrupt_does_not_apply` |
| **W3a** empty race | `evaluate 0` | host exit `none`, `Parked.withGuard 0`, 1 fiber — a live frontier | `w3_empty_is_a_frontier` |
| **W3b** empty race interrupted | `evaluate 0; interruptFrom (some 0) 0` | host `failure (interrupt (some ⟨0⟩))` | `w3_empty_until_interrupted` |
| **W3c** immediate success stops launch | `evaluate 0` | host `success (nat 1)`; race rows `launched 1, settled, skipped 2`; **3** fibers, the unlaunched entrant interrupted with the host's id (`interruptRecorded (some 0, 2)`, entrant 2 exits `interrupt (some ⟨0⟩)`) — M8 | `w3_immediate_success_stops_launch` |
| **W3d** failure allows next launch | `evaluate 0` | host `success (nat 9)`; rows `launched 1, launched 2, settled` | `w3_failure_allows_next_launch` |
| **W3e** all failed, order retained | `evaluate 0` | host `failure [fail (tag 1), fail (tag 2)]` | `w3_all_failures_retain_order` |
| **W4a** sibling completes a Deferred | `evaluate 0` | A `success (nat 7)`, B `success (bool true)`, parent `success (fiber ⟨2⟩)` | `w4_sibling_resumes` |
| **W4a′** the completion resumes on the spot (M1) | `evaluate 0` | `resumedWith 1, exited 1, exited 2, exited 0` — A resumes *inside* B''s `sync`, on B''s stack, both when the completion is B''s last primitive and when it is not | `w4_completion_resumes_on_the_spot` |
| **W4b** complete twice | `evaluate 0` | root `success (bool false)` | `w4_complete_twice_answers_false` |
| **W4c** `interruptWith` reaches the waiter | `evaluate 0` | A `failure (interrupt (some ⟨2⟩))` — the *completing* fiber; B `success (bool true)` | `w4_interrupt_reaches_the_waiter` |
| **W5a** middleware installed | `installMiddleware; evaluate 0` | child `failure (interrupt (some ⟨0⟩))`, `childrenInterrupted = [(0,[1])]`, **`interruptRecorded = [(some 0, 1)]`** (the row the exit path now emits per child), parent `success unit` | `w5_middleware_interrupts_children` |
| **W5b** middleware not installed | `evaluate 0` | child exit `none`, no `childrenInterrupted` and no `interruptRecorded` row, parent `success unit` | `w5_no_middleware_leaves_children` |
| **W5c** `awaitAllChildren` | `evaluate 0; fire 0` | new child `success (nat 5)`, pre-existing child exit `none`, parent `success unit` | `w5_await_all_children_awaits_only_new` |
| **W6a** `forkIn` open scope + close | `evaluate 0` | `scopeLinked forkIn 0 100 ⟨1⟩` (the row carries the mode since M4); child `failure (interrupt (some ⟨0⟩))`; scope keys `[]`; scope closed; root `success unit` | `w6_link_then_close` |
| **W6b** `forkIn` closed scope | `evaluate 0` | `scopeClosedOnLink 1 ⟨1⟩`; child `failure (interrupt (some ⟨0⟩))` — the *parent''s* id — annotated from the child''s own frame *and* the parent''s: `causeKeys = [["stack1", "stack0"]]` (M10) | `w6_closed_scope_interrupts_now` |
| **W6b′** `fiberRunIn` closed scope (M10) | `evaluate 0` | `scopeClosedOnLink 1 ⟨1⟩`; the existing fiber exits `failure (interrupt (some ⟨1⟩))` — its **own** id — with no caller annotations: `causeKeys = [["stack1"]]`; root `success unit` | `w6_runIn_closed_scope_uses_no_caller_annotations` |
| **W6c** exit drops the key | `evaluate 0` | child `success (nat 3)`, scope keys `[]` | `w6_child_exit_drops_key` |
| **W6d** self-interruptor skipped | `evaluate 0` | no `interruptRecorded` row, root `success unit` | `w6_self_interruptor_skipped` |
| **W6e** sequential close | `evaluate 0` | root `failure [fail (tag 2)]` (LIFO, capture-not-throw, merge); **1** fiber; scope closed | `w6_sequential_captures_and_merges` |
| **W6f** parallel close | `evaluate 0` | **3** fibers; daemon 1 `failure [fail (tag 4)]`, daemon 2 `success unit`; root `failure [fail (tag 4)]` — the merge of *both* awaited exits, now through `Resume.exitsValue` (M6); scope closed | `w6_parallel_forks_and_merges` |
| **W10a** a program masks its own fiber (M2) | `evaluate 0; interruptFrom (some 0) ∅ 1; answerAsync 1 0 unit` | while masked the interrupt is recorded once and *not* applied (child exit `none` after the second decision); the cause is delivered by the restoring frame when the park is answered: `failure (interrupt (some ⟨0⟩))` | `w10_program_masks_its_own_fiber` |
| **W10b** `into` on a failing body | `evaluate 0` | root `success (bool true)`; the Deferred's stored completion is `Prim.failure (fail boom)` — an interrupted or failed body still completes it, under the mask `into` now spells | `w10_into_completes_on_failure` |
| **W11** an interrupted `Async` runs its cancel (M3) | `evaluate 0` / `evaluate 0; interruptFrom (some 0) ∅ 1` | parked: the Deferred's waiters are `[(⟨1⟩, 0)]`; interrupted: the `AsyncFinalizer` frame's `contE` runs `cancelThenFail`, the waiter list becomes `[]`, and the fiber re-fails with the very cause that was passing | `w11_cancel_splices_the_waiter` |
| **W12** `awaitAll` answers the exits (M6) | `evaluate 0; fire 0` | parent `success (exitsValue [success (nat 4), failure (fail (tag 5))])` — the two children's exits, in collection order | `w12_awaitAll_answers_the_exits` |
| **W13a** unknown scope key, close (M7) | `evaluate 0` | `stuck = Stuck.unknownScope 99`, root exit `none`, `replayEval` lands on the `stuck` arm — the machine halted, it did not invent a cause | `w13_unknown_scope_is_stuck` |
| **W13b** unknown scope key, `forkIn` | `evaluate 0` | the same halt from `linkScope` | `w13_unknown_link_is_stuck` |
| **W7a** `Ref.set` | `evaluate 0` | root `success (Val.cell ⟨0⟩)`, heap `[nat 5]` | `w7_set_answers_the_cell` |
| **W7b** `Ref.update` | `evaluate 0` | root `success unit`, heap `[nat 2]` | `w7_update_answers_void` |
| **W7c** `modifySome` on `None` | `evaluate 0` | root `success (nat 1)`, heap unchanged `[nat 1]` | `w7_modify_some_writes_back_the_read` |
| **W7d** `updateSomeAndGet` vs `getAndUpdateSome` | `evaluate 0` | `success (nat 0)` vs `success (nat 3)` | `w7_update_some_and_get_rereads` |
| **W8a** `runSyncExit` on a parked program | — | `failure (die asyncFiber)` | `w8_sync_exit_async_fiber_error` |
| **W8b** `runSyncExit` on a finishing one | — | `success (nat 3)` | `w8_sync_exit_value` |
| **W8c** `runCallback` | — | callback rows `[(77, success (nat 3))]` | `w8_callback_fires` |
| **W8d** `promiseOutcome` | — | `Except.error (Squashed.error (Err.tag 4))` | `w8_promise_squashes` |
| **W9** task enqueued during a drain | `evaluate 0; fire 0` | root exit `none`, dispatcher armed, **1** task still queued; a second `fire` finishes it `success (nat 1)` | `forbidden_task_enqueued_during_drain`, `w9_next_fire_runs_it` |
| **DB-07** write then fail | `evaluate 0` | root `failure (fail boom)`, store `refs = [nat 5]` | `db07_store_survives_failure` |

The three race witnesses match the host goldens they are named after:
`raceImmediateSuccessStopsLaunch.tsv` (a success stops the launch loop),
`raceFailureAllowsNextLaunch.tsv` (a failure does not), `raceAllFailuresRetainOrder.tsv` (the
causes are retained in launch order), `emptyRacePendingUntilInterrupted.tsv` (the empty race is
pending until interrupted) — with one divergence, M8 below.

### The five forbidden examples

1. **An observer firing before the exit is stored** (`:619` precedes `:621`) — `traceWellFormed`
   is a decidable pass over a `RunEvent` trace that requires every `observerFired f` to be
   preceded by an `exited f`. Checked `true` on ten witness traces
   (`forbidden_observers_and_double_exit`).
2. **An interrupt applied while `running = true`** — stated as a fact about the step function,
   not one tape: for any fiber with `exit = none`, `running = true`, `interruptible = true`,
   `interruptRecord` answers "do not evaluate now" **and** sets `deferredInterrupt`
   (`forbidden_interrupt_while_running`, `internal/effect.ts:589-590`).
3. **A `SetInterruptible` frame evaluated as `current`** — `forbidden_setInterruptible_as_current`
   shows the step is `defaultEvaluate`'s defect (`Effect4/Runtime/Runtime.lean:1706-1708`), and
   `forbidden_no_notImplemented_defect` shows no witness fiber exits with that defect, so no
   witness reached the forbidden step.
4. **A task enqueued during a drain running in the same drain** (`Scheduler.ts:225-233`) — W9.
5. **A second exit for a fiber that has one** — the same `traceWellFormed` pass rejects a repeated
   `exited` row for one fiber.

### The two projections compute

`toSched_computes` (`rfl`): `RunMachine.toSched w1DeferredJoin` has trace
`[Event.scheduled ⟨1⟩, Event.completed ⟨1⟩ (success (nat 42)), Event.completed ⟨0⟩ (success (nat
42))]`. `toSup_computes` and `toSup_records_the_interrupt` (`decide`): W1's child projects to
`FiberStatus.done` with its exit as `core.terminal`, no children, no subscriptions and
`interrupted = none`; W2's child projects with the recorded interrupt cause on `Supervision.Fiber.interrupted`.

### The five forbidden examples, on the revised carrier

Unchanged in shape, extended in coverage: `traceWellFormed` now runs over thirteen witness
traces including W10–W12, `noNotImplementedDefect` over ten machines,
`forbidden_interrupt_while_running` takes `interruptRecord`'s new annotations argument, and
`forbidden_task_enqueued_during_drain` / `w9_next_fire_runs_it` are untouched by the carrier
revision (`Prim.yieldNowWith` replaced the old `ParkKind.yield` spelling with no behavioural
change).

## 3. `sorry`s

**None.** Nothing in either module is admitted. Where a clause could not be expressed, no
declaration was written and §5 records why.

## 4. Census rows each store makes statable

Statable, not green. Green is clause-by-clause against the census summary and is decided at the
landing under `docs/RUNTIME-COVERAGE.md`.

### `ref.*` — all ten rows, every clause

| Row | Theorem(s) in `Deep.Stores` |
| --- | --- |
| `ref.make` | `refStep_make`, `refMake_twice_distinct`, `refMake_is_sync` |
| `ref.get` | `refStep_get`, `refPeek_poke_self`, `refStep_get_after_set` |
| `ref.set-void-returns-cell` | `refStep_set`, `set_answer_ne_update_answer` |
| `ref.cell-set-returns-self` | `refStep_set_answers_self` |
| `ref.get-and-set` | `refStep_getAndSet` |
| `ref.set-and-get-assignment` | `refStep_setAndGet` |
| `ref.update` | `refStep_update`, `refStep_update_applies_once` |
| `ref.modify` | `refStep_modify` |
| `ref.modify-some-no-reread` | `refStep_modifySome_none`, `refStep_modifySome_eq_modify` |
| `ref.update-some-and-get-reread` | `refStep_updateSomeAndGet_some`, `_none`, `updateSomeAndGet_ne_getAndUpdateSome` |

One caveat, already recorded by the state note §3.1: `ref.set-void-returns-cell`'s "declared
`Effect<void>`" half is a *lowering-side* receipt about the declared answer spelling, not a step
fact, and no store can carry it.

### `deferred.*` — all twelve rows; ten fully, two partial

| Row | Statable here | Theorem(s) |
| --- | --- | --- |
| `deferred.make` | yes | `deferredStore_make`, `deferredCell_cases_receipt` |
| `deferred.is-done` | yes | `deferredStore_isDone`, `deferredCell_completion_cases` |
| `deferred.await` | **yes, all four clauses.** The "callback effect" clause the state note listed as blocked on `op.Async` is `Prim.async` (S1) plus `RunInterp.registerAsync`; the cleanup clause — "returns a cleanup that splices that resume out and does nothing once completion has cleared the array" — is reachable from an interrupt since M3, through the `AsyncFinalizer` frame's `contE` | `awaitDeferred_is_a_park`, `cancelAwait_splices_the_waiter`, `cancelThenFail_runs_then_refails`, `deferredStore_register_done`, `_pending`, `deferredStore_cancel_removes`, run by `w11_cancel_splices_the_waiter` |
| `deferred.single-completion` | yes | `deferredStore_complete_done` |
| `deferred.completion-order` | yes — clear-before-resume is an equation, not a promise | `deferredStore_complete_pending` |
| `deferred.complete-with-stores-effect` | yes | `deferredStore_complete_stores_argument`, `completeWith_non_exit`, `deferredStore_waiter_receives_stored` |
| `deferred.done-is-complete-with` | yes; the "an arbitrary effect completion is not shared" half becomes statable too (the waiter is resumed with the *primitive*, which each waiter then runs) but is **not stated** here — no witness runs two waiters on a non-exit completion | `completionPrim_ofExit`, `doneWith_shared` |
| `deferred.complete-runs-once` | **partial** — "answers false without running" is statable, and `into` is now spellable (M2); "so its result is memoized" is a statement about running a stored effect twice, which no witness here does | — |
| `deferred.into-uninterruptible` | **yes since M2** — "runs the body under an uninterruptible mask with interruptibility restored only inside" is `WithFiberAction.setInterruptible … false` around `… true`, and "takes the body's `Exit`", "an interrupted body still completes the Deferred" are the other two | `intoDeferred_spelling`, `intoDeferred_masks`, `intoDeferred_takes_exit`, run by `w10_into_completes_on_failure` |
| `deferred.interrupt` | **yes** — the state note listed this blocked on the missing fiber id; `WithFiberAction.getId` closes it, and W4c shows the interruptor is the completing fiber | `interruptDeferred_spelling`, `interruptDeferred_delegates` |
| `deferred.interrupt-with` | yes | `interruptWith_is_completion` |
| `deferred.poll` | yes | `deferredPoll_no_write` |

### `scope.*` — the clauses this store adds

| Row | Missing clause per `Effect4Test/Audit/RuntimeCoverage.lean` | Now statable? |
| --- | --- | --- |
| `scope.fork-linkage` | "the linked names are `scopeClose(child, exit)` and `scopeRemoveFinalizerUnsafe(parent, key)` needs a scope store" (`:3096`) | **yes** — `scopeStore_forkChild_names`; and the fiber-side linkage is `scopeLinkFiber_name` + `interruptFiber_compiles_to_interruptScoped` + W6a/W6b/W6c |
| `scope.close-sequential` | "awaits each finalizer through `exit()`" is temporal sequencing (`:3072`) | **as a program shape**: `closeSeqChain_order`, `closeSeqChain_captures`, `closeSeqChain_merges`, run by W6e. The *temporal* half — that finalizer `i+1`'s first step follows finalizer `i`'s exit in `drive` — is a run-order theorem this spike does not state |
| `scope.close-parallel` | "immediate daemon forks that inherit the closing fiber mask" | **yes** — `closeParChain_forks_immediate_daemon`, `closeParChain_inherits_mask`, run by W6f |
| `scope.close-merge` | "parallel finalizer fibers are awaited together and every exit is merged" | **yes since M6**: "awaited together" is `closeParChain_awaits_all`, "every exit merged" is `mergeAwaitedExits_is_asVoidAll` over the exits the countdown answered, with `reasonsOfVal_exitsVal` showing the value channel loses no reason; run by `w6_parallel_forks_and_merges` and `w12_awaitAll_answers_the_exits` |
| `scope.close-state-first` | (green) | reinforced: `storesCloseScope_state_first` |
| `scope.exit-as-void-all` | (green) | `mergeExits_reasons` relates the value-alphabet merge to `Exit.asVoidAll` |
| `scope.scoped` | "installs a fresh scope in the fiber context" and "restoring the previous context first" | **expressible, not stated**: `RunFiber.context : χ`, `Ctx.ambientScope` and `WithFiberAction.setContext` exist, and `finalizerProgram` can emit the restore inside the `OnExit` finalizer; the compile of `scoped` was out of this spike's scope |
| `scope.acquire-release` | "with the captured context" | **expressible, not stated**: the release's captured context has to be carried in the finalizer *name* (a `FinName.releaseWith (ctx : Ctx)` arm); not added |

## 5. The findings, all closed

All nine findings of the first pass, plus the two residuals the port turned up (M1's exit-path
half and M10), are applied in `workshop/Deep/Fibers.lean` and in `Effect4/Runtime/Runtime.lean`
(spike S1's three parking constructors and `PrimInterp.cancelThenFail`). **No finding of this
spike is open.** This section records, per finding, what the carrier now does, how this spike
spells it, and which witness assertion moved.

### M1 — a stateful `sync` drains the resumes it owes, on both paths

**Closed.** `iteration`'s `Prim.sync` arm returns `nested := [Cmd.drainDue]`
(`Fibers.lean:750-755`); `drive`'s `Outcome.continue_` branch runs the nested commands before
`Cmd.loop`, and — since the second pass — its `Outcome.finished` branch runs them before
`exitFiber`, re-reading the fiber afterwards because a nested command may have recorded an
interrupt on it (`Fibers.lean:1045-1056`). So a completion's waiters resume inside the completing
`sync`, on the completing fiber's own stack, as `Deferred.ts:1655-1659` does, whether or not the
completion is that fiber's last primitive.

`w4_completion_resumes_on_the_spot` pins both shapes: with `B = complete d; unit` and with
`B = complete d`, the order is `resumedWith 1, exited 1, exited 2, exited 0` — `resumedWith 1`
precedes `exited 2` in each. The residual this report carried after the first port is gone.

### M2 — a program can mask its own fiber

**Closed.** `WithFiberAction.setInterruptible body flag` (`Fibers.lean:282-284`, arms at
`:874-880`) is rc.112's `uninterruptible` (`internal/effect.ts:4302-4310`) and `interruptible`
(`:4331-4337`), with `uninterruptibleMask` (`:4340-4352`) as the pair. This spike spells:

* `ActionName.setInterruptible (body : ProgName) (flag : Bool)`;
* `ProgName.maskedPark slot` = `withFiber (setInterruptible (park slot) false)`;
* `ProgName.intoDeferred body cell` =
  `withFiber (setInterruptible (intoBody body cell) false)`, and
  `ProgName.intoBody body cell` =
  `onSuccess (exitFrame (withFiber (setInterruptible body true))) (doneInto cell)` — the exact
  shape of `Deferred.ts:1778-1783`, `restore` included.

`deferred.into-uninterruptible`'s mask clause is therefore statable and stated
(`intoDeferred_spelling`, `intoDeferred_masks`), and W10 runs both halves: the masked fiber
records an interrupt without applying it and takes it at the restoring frame
(`w10_program_masks_its_own_fiber`), and `into` on a failing body still completes the Deferred
(`w10_into_completes_on_failure`).

### M3 — a cancel name knows the waiter it splices out

**Closed.** `RunInterp.cancelName : ν → FiberId → Nat → ν` (`Fibers.lean:399`), and the run loop
pushes `Prim.asyncFinalizer (cancelName (cancel.getD abortName) f.id token)` at park time exactly
when there is a controller or a cancel (`:718-724`, rc.112 `:1128-1141`). The frame's `contE`
then runs `PrimInterp.cancelThenFail` when the cause carries an interrupt
(`Runtime.lean:877-882`, rc.112 `:1155-1159`).

This spike spells `Name.withWaiter (base) (waiter) (token)` as what `cancelName` mints,
`Name.abortController` as `abortName`, `cancelProgram` as the cancel effect
(`withWaiter (cancelAwait cell) w t ↦ sync (deferredAwaitCleanup cell w t)`), and
`cancelThenFail name cause = onSuccess (cancelProgram name) (Name.reFail cause)`.
`ProgName.awaitDeferred cell` is now
`Prim.async (registerAwait cell) true (some (cancelAwait cell))`, so the whole path is live:
`w11_cancel_splices_the_waiter` shows the waiter list going from `[(⟨1⟩, 0)]` to `[]` on the
interrupt, with the fiber re-failing with the very cause that was passing.

Note the frame does the masking that makes this work: `asyncFinalizer`'s `ensure`
(`Runtime.lean:639-648`) clears `interruptible` before the pop's skip test, so the frame is *not*
skipped by `popFrom`'s interrupted-skip (`:1457`) and its `contE` actually answers.

### M4 — scope linking knows its mode

**Closed.** `RunInterp.scopeLinkFiber : Supervision.ScopeMode → Nat → Nat → FiberId → St →
Option St` (`Fibers.lean:414`), `linkScope` takes the mode (`:650-674`), `forkIn`/`forkScoped`
pass `.forkIn` and `runIn` passes `.fiberRunIn`, and `RunEvent.scopeLinked` carries it
(`:315`). The store registers `FinName.interruptFiber fiber true` for `forkIn` (`:5370`) and
`… false` for `fiberRunIn` (`:5458`); `scopeLinkFiber_name` and `scopeLinkFiber_runIn_name` state
both. W6a's `scopeRows` assertion gained the mode column.

### M5 — an interrupt carries the caller's annotations

**Closed.** `RunDecision.interruptFrom (interruptor) (annotations) (target)` (`Fibers.lean:372`)
and `interruptRecord interp interruptor extra f` (`:544-565`), which annotates the cause from the
target's own stack frame *and* from the caller (`:549-552`), the two sources of
`internal/effect.ts:578-584`. `linkScope`'s closed arm supplies `interp.stackAnnotations who`
(`:660-663`), which is `fiberStackAnnotations(parent)` at `:5374`. Every witness tape now passes
`ReasonAnnotations.empty`, and `forbidden_interrupt_while_running` takes the extra argument.

### M6 — a countdown collects the exits it awaited

**Closed.** `Pending` is `⟨token, waitingOn, remaining, collected, resumeWith⟩` with
`Resume.exitsValue | void | continueWith name` (`Fibers.lean:64-83`), `Observer.countdown`
appends the exiting fiber's exit (`:927-944`), and `RunInterp.exitsValue` turns the list into a
value (`:438`). `WithFiberAction.awaitAll` parks with `Resume.exitsValue` (`:845-847`).

This spike spells `exitsValue` as `exitsVal`, a `Val.exitNil`/`Val.exitCons` chain — a
`List ExitV` field would make `Val` a nested inductive whose `DecidableEq` handler refuses — with
`reasonsOfVal` reading the reasons back and `reasonsOfVal_exitsVal` /
`mergeAwaited_eq_mergeExits` proving the channel loses nothing, so the parallel close's merge is
`exitAsVoidAll` of exactly the awaited exits (`mergeAwaitedExits_is_asVoidAll`). The store
side-channel (`ScopeEntry.collected`, `SyncOp.scopeRecordExit`, `scopeCollectedExits`,
`ProgName.recordingFinalizer`, `Name.recordCloseExit`) is deleted. `w12_awaitAll_answers_the_exits`
runs `awaitAll` directly; `w6_parallel_forks_and_merges` runs it through the close.

`scope.close-merge`'s "every exit is merged by `exitAsVoidAll`" is therefore statable now, and
stated.

### M7 — the scope hooks can say "unknown"

**Closed.** `scopeLinkFiber` and `dropFinalizer` answer `Option St`, `closeScope` answers
`Option (St × Prim)` (`Fibers.lean:414-421`), and `none` becomes `Stuck.unknownScope`
(`:655`, `:669`, `:892`, `:925`), observable as `RunMachine.stuck` and `ReplayResult.stuck`. The
store's arms are `storesCloseScope`, and `scopeLinkFiber`/`dropFinalizer` guarded by
`entryAt`; `storesCloseScope_unknown` and `scopeLinkFiber_unknown` state it, and W13 runs both
paths to a halt with the root neither failing nor exiting. The `Defect.badName` cause the first
pass had to invent is gone from those arms.

### M8 — a settled race interrupts its unlaunched entrants

**Closed.** `Cmd.launch`'s settled arm records an interrupt with the host's id and emits both
`raceSkipped` and `interruptRecorded` instead of deleting the fiber (`Fibers.lean:1070-1077`),
which is what the golden's `op interrupt 1` row and `Supervision.RaceAllState`'s
`requests`/`cleanup` have. `w3_immediate_success_stops_launch` moved from `fiberCount = 2` to
`fiberCount = 3` and gained `interruptRows = [(some 0, 2)]` and the entrant's interrupted exit.
`RunMachine.toSched` no longer loses a `FiberState` that existed.

### M9 — the projection loss is recorded

**Closed as a recorded refusal.** `RunFiber.status`'s docstring (`Fibers.lean:175-176`) and the
module header say that the old `FiberStatus` has no "suspended" phase, so an async or countdown
park projects to `runnable`. Nothing to change in the store; the landing carries the refusal row
or re-freezes the scheduler alphabet.

### M10 — the caller decides which stack an interrupt is annotated from

**Closed.** `linkScope` takes `extra : ReasonAnnotations α` (`Fibers.lean:650-653`);
`forkIn`/`forkScoped` pass `interp.stackAnnotations f.id`, the *parent's*
(`:809-810`, `:817-818`, rc.112 `:5374` = `fiber.interruptUnsafe(parent.id,
fiberStackAnnotations(parent))`), and `runIn` passes `ReasonAnnotations.empty` (`:826-827`,
rc.112 `:5454` = `self.interruptUnsafe(self.id)`, no annotations argument).

To make that observable this pass replaced the constant `stackAnnotations` with
`stackAnnotationsOf`, which gives each fiber its own annotation *key* (`stack0`, `stack1`, …)
over the `Unit` annotation value — the key has to carry the identity, because
`Cause.annotate … false` drops an extra entry whose key the base already holds, so a shared key
would hide exactly the difference M10 is about. `causeKeys` reads the keys back, and two
witnesses now separate the modes on a closed scope:

* `w6_closed_scope_interrupts_now` — `forkIn`: the child exits
  `interruptedWith ⟨0⟩ ⟨1⟩ (stackAnnotations ⟨0⟩)`, keys `[["stack1", "stack0"]]` — its own
  frame's, then the parent's.
* `w6_runIn_closed_scope_uses_no_caller_annotations` — `fiberRunIn`: the existing fiber exits
  `interruptedBy ⟨1⟩ ⟨1⟩`, keys `[["stack1"]]` — its own only, and the interruptor is itself.

Every other witness that names an interrupt cause goes through `interruptRecord … empty`, so
`interruptedBy` (now `interruptedWith … ReasonAnnotations.empty`) still describes them exactly.

### Smaller notes, not defects

* `RunInterp.closeScope`'s `closer : FiberId` argument is still unused by this store: the only
  thing the parallel strategy takes from the closer is its mask, which arrives separately as
  `closerInterruptible`. The store binds it `_closer`. Either drop the field or use it for the
  `interruptScoped` self-guard at the store level.
* `Resume.continueWith name` applies the name to the *exits* value
  (`countdownPark.resumePrim`, `Fibers.lean:588-594`), so the exit path's
  `restoreName exit` continuation receives the children's exits rather than the exit it
  restores. `contA (Name.restore exit) _` ignores its argument, so this is harmless today; a
  name that wanted both would need the pair.
* `Race` and `RunMachine` still derive no `DecidableEq` (they contain
  `Supervision.RaceAllState`, which contains `WaitState`), so a witness compares projections,
  never whole machines. Every assertion in `Deep.Witnesses` does.

## 6. DB-07, as stated

Written beside the interp in `workshop/Deep/Stores.lean` (module header, and again on the
`stores` definition):

> Every store operation of this file is a *forward* map: `refStep`, `DeferredStore.complete`,
> `ScopeStore.*` and `storesCloseScope` return the store they reached, and no arm of the interp,
> and no arm of `Deep.Fibers`, reads a store snapshot taken before a step. Consequently the store
> the machine carries after a fiber has failed is the store that fiber had reached when it
> failed: state produced before failure remains available to finalization. The landing proves
> that as `state (stepDecision interp fuel m d) = state (the last store operation the trace
> records)`, whose falsifier is one reachable decision after which the store is an earlier one;
> the executable instance is `Deep.Witnesses.db07_store_survives_failure`.

The instance: a root that runs `Ref.set cell 5` and then `failCause boom` exits
`failure (fail boom)` with the machine's store at `refs = [nat 5]`.

## 7. Commands run

```
lake build Deep.Stores Deep.Witnesses     # green, second pass
```

No bare `lake build`, no `scripts/sweep`, no trust gate, no census gate, no `Deep.ForkFlow`. One
Lean process at a time. No file outside `workshop/Deep/{Stores,Witnesses}.lean` and this report
was written; `workshop/Deep/Fibers.lean`, `Effect4/`, `Effect4Test/`, `lakefile.toml` and
`.lake/` are untouched by this spike.

`COORDINATION.md` was **not** edited, to avoid a concurrent-write collision with the other agents
building in this worktree. The claim row this spike owes is:

| File or tree | Claimed by | State |
| --- | --- | --- |
| `workshop/Deep/Stores.lean`, `workshop/Deep/Witnesses.lean`, `docs/research/2026-09-03-spike-s2-stores-witnesses.md` | Claude (deep plan spike S2, 2026-09-03) | second pass on the revised carrier, green, uncommitted |

## 8. What a follow-up should do first

No carrier change is owed. What is left is witness and clause work inside this spike's own
files, none of it blocked:

1. `deferred.complete-runs-once`'s memoization clause needs a witness in which two waiters *run*
   a stored non-exit completion; the carrier supports it (`Completion.ofRefGet` is already such a
   completion), no machine change is needed.
2. `scope.scoped` and `scope.acquire-release` are the two `scope.*` rows still only *expressible*
   here: the first needs `scoped` compiled as `Prim.scopedFrame` between two
   `ActionName.setContext` actions with the restore inside the finalizer program, the second a
   `FinName.releaseWith (ctx : Ctx)` arm so the release carries its captured context.
3. The three smaller notes at the end of §5 (the unused `closer` argument, `Resume.continueWith`
   receiving the exits value, `RunMachine` deriving no `DecidableEq`) are dispositions for the
   landing, not defects; each needs a ruling, not an edit.
