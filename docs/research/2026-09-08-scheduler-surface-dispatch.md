# Scheduler surface — dispatch (grill ruling 4)

Seat: Claude Fable implementer (seat A, Mac), 2026-09-08, after join commit 5 (`57dbb8c`).
Routed by `2026-09-08-build-path.md` §3 row 1 and `2026-09-07-plan-review-after-join3.md`
§4.2; rulings from `2026-09-07-grill-agenda.md` §3 (3, 4) and §1 (Q5, Q3, Q12); requirements
from `2026-09-04-effect-internals-proof-map.md` §1.6/§4.3, `2026-09-07-lit-siblings.md` §Q5,
`2026-09-07-ocaml-ecosystem-survey.md` #1/#17/#23, `2026-09-07-direction-scout.md` D9.
Entry point for the seat: `2026-09-05-dispatch-brief.md` (rules of the tree). One Lean process
under `.lake/LANE.lock`, `LEAN_NUM_THREADS=3`.

## 0. What lands, and what it leaves

The core change every family after Deferred needs (grill 4: "short, before Queue"): one
allocation-and-wake protocol on the store, a task alphabet that covers rc.112's seven
`scheduleTask` shapes, a dispatcher with an identity, and the reply a row needs when a
resource is not ready. No family lands here: Deferred is the protocol's first instance
(broadcast, inline wake); Latch, Queue, Semaphore, Pool and the timer are its consumers
(build-path rows 2 and 6). No `RunDecision` changes; the tape stays the seven decisions.

| # | Commit | Lands | Retires / re-spells |
| --- | --- | --- | --- |
| 1 | the protocol and the drain | `WakePhase`, `WakeMode`, `WakeList` (`Machine/Wake.lean`); `DeferredCell` on a `WakeList`; `Owed` entries with a mode on `due`; `Task.wake`; `Cmd.wake`; `RunInterp.wakeList` (the one new field); the cancelled-waiter clause; fixtures F1–F4, F6, F7, F11 | the three `deferredStore_*` ascriptions re-spell (count unchanged) |
| 2 | the address and the reply | **re-scoped while cutting:** the machine never removes a fiber record (`spawn` appends, `update` maps in place), so a dispatcher already outlives its fiber's run and `postTask` by fiber id is the address — no table, no `RunFiber` change; the `Delay` reply is `WakeList.delay`: registration with the row as the waiter's payload, re-presented at the wake (signal-then-repoll) — no `syncState` change; fixtures: a post to an exited fiber's dispatcher, F5 | nothing re-spells |
| 3 | records | census rows unchanged in count; register rows; receipt; `DESIGN-BASIS` DB-13 (one wake protocol) | — |

## 1. Rulings applied, and the two spellings (owner call O1 settled here)

- **`WakeMode`** is how an owed resume is delivered: `now` — inline, inside the completing
  `sync` (rc.112 Deferred, `Deferred.ts:1655-1659`, M1); `scheduled (owner : FiberId)
  (priority : Nat)` — posted as a task on the dispatcher addressed by `owner` (sites 3–7 of
  `effect-internals-proof-map.md` §1.6: `Latch.flushScheduled`, `releaseTakers`, the permit
  sweep, `wakeWaiters`, the STM pending wake). The scout's D9 named this `WakeMode`; kept.
- **`WakePhase : Nat`** is the counter on a waiter list (Eio `sem_state.ml`'s
  `In_transition`, survey #17): advanced by every wake-owing step; a waiter carries the phase it
  registered at. The grill's spelling; it is not the mode.
- **The cancelled-waiter clause** (survey :1149-1151, verbatim): *if a waiter is cancelled while
  its phase has already advanced (the resumer won), the cancelling step must itself perform one
  wake, because the resumer's wake was consumed by a waiter that is no longer there.*
  `WakeList.cancel` answers whether a wake is owed; a `signal` list re-owes it to its next
  waiter, a `broadcast` list (Deferred) lost nothing (theorem). The machine side stays the token
  guard: a resume for a waiter no longer parked is inert (`drive_resume_wrong_token`, lit Q5 :155).
- **Coalescing guard** (proof map :937-940): `WakeList.batch : Option (List (Waiter π))`;
  `schedule` on a list with a pending batch joins it and posts nothing; the batch runs as one
  `Task.wake list phase`.
- **`Delay`** (survey #1): a row's third answer — not ready, register on this list, re-present
  the same row when woken, consume no frame. Queue's signal-then-repoll shape; spurious wakes
  are permitted by the protocol, and the family's law says so (survey :1153-1156).
- **Per-family payload discipline stays** (grill Q5): the protocol fixes *when* a waiter is
  woken and how a cancel is accounted; *which* waiters and *with what* is the family's policy
  (`WakePolicy | broadcast | signal`; Semaphore's no-FIFO sweep and Pool's count are later
  policies on the same list). `TxRef` is out (its own subcalculus).
- **No off-tape choice** (lit Q5 :222): the host's `flush`/`fire` decisions stay the only
  scheduler choices; posting a task never chooses.

## 2. Representation

```lean
abbrev WakePhase := Nat
inductive WakeMode | now | scheduled (owner : FiberId) (priority : Nat)
inductive WakePolicy | broadcast | signal
structure WakeList where
  waiters : List (FiberId × Nat × WakePhase)   -- registration order; the phase at registration
  phase : WakePhase                           -- advanced by every wake-owing step
  scheduled : Bool                            -- a batch wake is pending (the coalescing guard)
structure Owed (κ) where waiter : FiberId; token : Nat; code : κ; mode : WakeMode
-- Deferred: `DeferredCell := ⟨completion, list : WakeList⟩`, mode `now`, policy `broadcast`
-- Task += | wake (list : WakeKey) (phase : WakePhase)   -- WakeKey := | deferred (cell : DeferredKey) (families add)
-- Cmd  += | wake (list : WakeKey) (phase : WakePhase)   -- `taskCmds (.wake l p) = [Cmd.wake l p, Cmd.drainDue]`
-- RunInterp += wakeList : WakeKey → WakePhase → St → St   -- move the list's waiters owed at that phase into `due`
-- dueResumes : St → List (Owed κ) × St
-- Cmd.drainDue: `.now` ⇒ Cmd.resume inline; `.scheduled owner p` ⇒ post `Task.resume` on owner's dispatcher, arm owner
-- the address is the fiber id (`postTask`); a fiber record is never removed, so its dispatcher outlives its run
-- the Delay reply: `WakeList.delay l fiber token row` — the row is the payload, the wake re-presents it
```

What does not change: `RunDecision` (seven), `armed : List FiberId` (the dispatcher's
address is its making fiber's id), `Parked` (the guard), the truth corpus (Deferred wakes
`now`; no rc.112 program reaches `Task.wake` or `Delay` before Latch/Queue), the census row
count (137/135), `Stores.empty` (a fresh `WakeList` is the bottom).

## 3. Fixtures (executed `#guard`s; provenance per case)

F1 immediate vs scheduled wake (lit Q5 :162) — the same completion drained `now` resumes
inline; `scheduled` posts a task and the fiber resumes only at `fire`. F2 stale and duplicate
tokens (`drive_resume_wrong_token`, idempotent repeat). F3 cancel before and after the phase
advance (the clause; `broadcast` loses nothing, `signal` re-owes). F4 coalescing: a second
`schedule` while one batch is pending is a no-op; one `Task.wake` runs. F6/F7 the two WHATWG
capture rules (lit Q5 :163): a waiter's `(fiber, token, phase)` is captured at registration and
a later list replacement cannot retarget it; registration on an already-completed cell answers
now. F11 a cancelled task still queued dispatches inert (lit Q5 :155). Commit 2: F5 a signal
followed by an unsuccessful repoll (the fixture store's take finds no permit twice: two parks
on fresh tokens at phases 0 and 1, one frame; a permit and a second signal take), and
`rootExited`: a `scheduled` wake addressed to an exited fiber lands on its dispatcher and the
host's flush fires it. Timer cases (F12) are A4's.

## 4. Acceptance

`lake build Effect4 Test OCaml5 Tools`; `Test/All.lean -M4096` (absolute path); the batteries
`SchedulerCoreContract`, `SchedulingContract`, `Fuzz` (invariant 9 holds: a `scheduled` entry
leaves `due` at the drain), `SimulationContract`; forced census (137/135; re-spelled
ascriptions listed in the receipt); forced truth (14/14, byte-identical); `git diff --check`.

## 5. Refusal rows (register)

- `SCHED-FB-PRODUCER`: `Task.wake` and `WakeList.delay` have no rc.112 producer in this tree
  until Latch/Queue land; their meaning is fixed here and pinned by fixtures, not by the truth
  harness.
- `SCHED-FB-UNKNOWN-OWNER`: a `scheduled` wake addressed to a fiber id the machine never
  minted is a frontier (`Stuck.unknownFiber`). An *exited* fiber's dispatcher is reachable: the
  machine keeps every fiber record, so it outlives the run as rc.112's object does
  (`Queue.ts:455`); the fixture `rootExited` pins it.
- `SCHED-FB-NO-FIFO`: a Semaphore's waiter list is not a queue (lit-lineage :148); the list
  is FIFO, the sweep policy is the family's.

## 6. Owner calls carried (not decided here)

O2 A4 may land on this surface (timers are `now` entries with a phase). O3 Queue's owner
calculus, before Queue. O5 the naming fixes (design language §5.2) — the new names follow
§5.1 (`wake` is a verb on a list; events stay past participles); no rename of `fire` here.
O7 admission-before-pop is the daemon's (H1). O8 the second seat's acceptance packet may be
written against commit 2's API.
