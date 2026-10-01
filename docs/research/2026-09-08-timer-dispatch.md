# The timer (A4) — dispatch and cut record (2026-09-08, seat A, Mac)

Build path row 2 (`2026-09-08-build-path.md` §3), grill Q6 (`2026-09-07-grill-agenda.md`:
`sleep`, `clockNow`, `advance (by : Nat)`, staged fires, one new `RunInterp` field, no
`clockAdjust`), the review's finding 3 (`2026-09-08-build-path-parallel-review.md`: settle
the dependency boundary before a `Psq` carrier) and the timer note
(`2026-09-04-timer-semantics-and-proofs.md`: the transcription, the four findings, the owed
seam). Composed while cutting, after the scheduler surface (DB-13).

## 0. Commits

| # | what | files | re-spells |
| --- | --- | --- | --- |
| 1 | the store and the machine | `Machine/Timer.lean` (new); `Wake.lean` `wakeBy`; `Stores.lean` (`timers`, `Name.registerSleep`/`cancelSleep`, `SyncOp.clockNow`/`sleepCancel`, `stores.clockStep`); `StoresLaws.lean` (`Stores.WF` gains `timers.WF`, `syncOpStep_timers_wf`); `Fibers.lean` (`RunDecision.advance`, `RunInterp.clockStep`, `advanceState`); the laws (Approximation, Handles, Book, Clauses, the simulation); fixtures T1–T9; the avatar's derived descriptions; the fuzz corpus | seven `Stores` literals in the frozen block gain `timers := s.timers` (count unchanged) |
| 2 | the two rows on the compile route | `NativeOp.sleep`, `NativeOp.clockNow`; `Compile`'s callback arm (`sleep 0` → `Prim.yieldNowWith 0`, else `Prim.async (EffName.store (Name.registerSleep …))` — the machine's names embedded, no new `EffName`); the term route's `denoteSleep`; `CodeMeans.asyncSleep` and its evaluation agreement; typing by the row table; printer/reader spellings generic; `Program/Derived.lean`, ts/eff, ocaml/eff and the Lean hex goldens regenerated; the OCaml typed surface; the staged-read and finding-4 fixtures on the program route | the `NativeOp` pins (20 → 22 ops; 53 → 55 op values; the goldens corpus 38 → 39) |
| 3 | records | DB-14; register rows `E4-RUN-CE-043..045`; the receipt | — |

## 1. Rulings applied

- **The decision is a duration.** `advance (millis)`; the clock never moves backwards
  (`TIMER-FB-SET-TIME`). `TestClock.setTime` (`:383-385`) is refused (R1 of the note).
- **Staged fires are the machine's loop**, not the store's: `advanceState` fires one, drains,
  drives, flushes, and asks again, so a sleep registered by a woken fiber fires in the same
  advance when due (finding 4). The store keeps the end of the advance in progress (`target`)
  as `TestClock.run` keeps `endTimestamp` under its semaphore.
- **One interpreter field**, `clockStep : Nat → St → Option (Owed κ) × St`: `some` an owed
  resume (the least due sleep fired, the clock staged at its deadline), `none` the end
  reached. Its key-bounded obligation, its book conjunct on `HooksAgree` and its Program-route
  agreement (`clockStep_rel`) follow the shape of `dueResumes`.
- **The fire is `now`.** A fired sleep resumes inline, as a Deferred's completion does. rc.112
  opens a latch (`:365`) whose `flushScheduled` posts the resume; that posted spelling waits
  for Latch, because the store-level key obligations cannot see the sleeper's fiber handle at
  registration. The same fibers run in the same order before the next fire.
- **No `Psq`.** The pending sleeps are the wake list with the deadline as payload; the earliest
  deadline is the family's choice on it (`WakeList.wakeBy`, `dueMin`: least deadline, first
  registered among equals — `SleepOrder`). The engine seat measured `psq` as not worth it;
  the architecture forbids the core importing `OCaml5`; a keyed carrier is a later change.
- **`sleep 0` and `sleep ∞` never reach the store** (`:6054-6055`): `yieldNow` and `never`,
  decided at the row (commit 2). A deadline is a `Nat` (`TIMER-FB-INFINITE`).
- **A cancelled sleep is removed** (`clearTimeout`, `:6063`; `TIMER-FB-KEPT-CANCEL`), never
  kept as `TestClock` keeps it (finding 2).

## 2. Fixtures (executed `#guard`s, `SchedulerCoreContract` §Timer)

T1 registration parks at the deadline, the clock still; T2 an advance short of the deadline
moves the clock and fires nothing, the rest fires it, the clock ends at the deadline; T3 an
advance past the deadline fires it and ends at the target; T4 deadline order across fibers,
the later registration first when earlier; T5 equal deadlines in registration order; T6 an
advance reaching one of two deadlines; T7 the cancel removes the sleep; T8 `clockNow` reads
the clock, `advance 0` moves nothing; T9 the store law along the way. Commit 2 adds, on the
program route: a woken fiber reads the staged clock, and a woken fiber's sleep fires in the
same advance (finding 4).

## 3. Owed

- Truth fixtures under rc.112's `TestClock` (the note's §4 witness table): the harness runs
  the live clock and records no timer firing; a `TestClock`-driven recorder is a harness
  change, not a Lean one.
- `Latch`: the posted fire (`WakeMode.scheduled` on the sleeper's dispatcher).
- The `Delay` budget and the family order the engine seat defaulted (A3-1, A3-9) are the
  engine's; the Lean store fires by deadline and registration only.
