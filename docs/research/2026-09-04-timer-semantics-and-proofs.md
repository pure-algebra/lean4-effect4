# Timing: what rc.112's clocks actually do, the logical timer store, and what the proofs found

Status: 2026-09-04, from the owner's "can we actually prove that we can handle some timing, or
is that impossible? let's just try the proofs and see what comes up", and the earlier ruling Q4
(`2026-09-04-effectful-streams-mechanization.md` §8: no physical clock; a logical timer store).
Artefact: `workshop/Timer/Timer.lean` (650 lines, 41 theorems, 10 executed `#guard`s, no
`sorry`/`axiom`/`native_decide`; `lake env lean -M4096 workshop/Timer/Timer.lean` exits 0 with
no diagnostics; self-contained, no imports). `workshop/` is outside git like `docs/research/`.
Sources read: `vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts`, `internal/effect.ts`
(`ClockImpl`, `sleep`, `delay`, `timeout*`, `raceFirst`), `Duration.ts`, `Scheduler.ts`;
`src/Effect4/Machine/{Fibers,Stores}.lean` for the Deferred shape the store mirrors.

## 0. The answer

Physical timing is not provable and the estate does not try: wall-clock, drift, the browser's
4 ms floor, the `2^31 − 1` ms `setTimeout` ceiling are host facts (DB-04 already forbids
fuel-as-time). **Logical** timing is provable, and it is exactly what rc.112's own `TestClock`
implements: a clock that only moves when the host says so, a table of sleeps ordered by
deadline then registration, and an `adjust` that fires every due sleep in that order, staging
the clock at each fired deadline and letting fibers run between fires. The spike is that
carrier with its laws proved. Four things came up that a "should be true" model would have got
wrong (§2).

## 1. What rc.112 does (the transcription, with lines)

| behaviour | `TestClock` (`testing/TestClock.ts`) | live `ClockImpl` (`internal/effect.ts`) |
| --- | --- | --- |
| `sleep d`, `d ≤ 0` | `end <= currentTimestamp` → return at once, nothing registered, no yield (`:325-326`) | `millis <= 0` → `yieldNow` (`:6054`) |
| `sleep ∞` | registers `timestamp = Infinity`; fires only on an infinite `adjust`/`setTime` (`:369` guards `isFinite`) | `never` (`:6055`) |
| `sleep d`, `0 < d < ∞` | push `{sequence++, timestamp: now + d, latch}`, sort by `(timestamp, sequence)` (`:201-204`, `:332-337`), await the latch | `setTimeout(resume, min(millis, 2^31−1))`, chained for the remainder (`:6057-6062`) |
| interruption of a sleeper | the latch await is interrupted; **the entry stays in `sleeps`** | `clearTimeout` (`:6063`) |
| `adjust k` | first `Fiber.await(forkChild(yieldNow))` (`:347`); then pop the least entry while `timestamp ≤ end`: set `now := timestamp`, open its latch, `yieldNow` (`:361-367`); finally `now := end` (`:368`) | — |
| `setTime t` | same loop with `end := t`; **`t` may be earlier than `now`** (`:384-386`) | — |
| `delay`, `timeout`, `timeoutOption`, `timeoutOrElse` | `andThen(sleep d, self)`; `raceFirst(self, sleep d ▷ …)` = `raceAllFirst([self, that])` (`:3660-3745`, `:1650`) — programs over `sleep` and the race the machine already has | same |
| `Duration` | `Millis`, `Nanos` (sub-ms rounds, `Duration.ts:410`), `Infinity`, **negative values exist** (`negativeInfinity`, `isNegative`, `:503`), `NaN` is zero (`:405`) | same |

## 2. What came up (the findings)

1. **rc.112's two clocks disagree on `sleep 0`.** The test clock returns synchronously without
   registering; the live clock yields (`yieldNow`). A program that relies on `sleep(0)` as a
   yield behaves differently under `TestClock`. The Lean row must pick one and record the
   other as a host-profile refusal; the store picks the test clock's shape (`sleep_zero`),
   because the machine's `yieldNow` is a primitive the row can prepend.
2. **The test clock never forgets a cancelled sleep.** After a `timeout` whose body wins, the
   loser's sleep entry stays in `sleeps`; a later `adjust` pops it, **stages `now` at the dead
   deadline**, opens a latch nobody awaits, and yields. The final clock value is unaffected,
   but a fiber that reads the clock between fires observes the staging. The live clock clears
   the timer. The store models the live clock (`cancel_removes`, `cancel_never_fires`) and
   records the divergence as refusal row R2 — a witness program for the tape-adequacy table.
3. **`now` is not monotone in rc.112.** `setTime` accepts an earlier timestamp. The ruling's
   law "`now` monotone" holds for `adjust` with a non-negative duration only (`advance_now`,
   `fireNext_now_mono`, `advance_now_mono`); `setTime` backwards is refusal row R1, not a
   decision of the store.
4. **Fires are staged, not batched.** A fiber woken at deadline `d` reads `d`, not the
   advance's target, and a sleep it registers during the advance fires in the same advance if
   due. The store has both forms: `fireNext` (staged, `now := fired deadline`) and `advance`
   (batched, the same fire list, `now := target`), with `iterate_eq_advance` proving they agree
   on *which* timers fire, in *what order*, and the final clock. What interleaving changes is
   what a woken fiber does before the next fire — the host loop's business, which is exactly
   rc.112's `yieldNow` between fires.

Smaller rows: negative durations fold to zero at the row (both clocks treat them as `≤ 0`);
`Nanos` round at the row (`now` is milliseconds); `Infinity` never fires under a finite
advance (`inf_never_fires`) on both clocks.

## 3. What is proved (`workshop/Timer/Timer.lean`)

Carrier: `Time = fin ms | inf`; `Timer W = ⟨deadline, seq, waiter⟩`; `Store W = ⟨now, nextSeq,
table, due⟩` with `WF` = table ascending under `before` (deadline, then seq), every `seq` below
the counter, no deadline in the past. Operations: `sleep`, `fireNext`, `finish`, `advance`,
`cancel`, `drainDue` (the Deferred shape: `due` is what the machine's `dueResumes` drains).

| law (ruling Q4) | theorem | status |
| --- | --- | --- |
| `now` monotone | `advance_now`, `advance_now_mono`, `fireNext_now_mono` | proved (for `adjust`; `setTime` refused) |
| a timer fires only when `now ≥ deadline` | `mem_fired_due`, `fireNext_due` | proved |
| every due timer fires | `not_due_of_mem_rest`, `fired_exact` | proved |
| fire order is deadline then registration | `fired_sorted`, `equal_deadline_registration_order`, `fireNext_earliest` | proved |
| cancellation removes the entry | `cancel_removes`, `cancel_keeps`, `cancel_never_fires` | proved (live clock) |
| the table stays well-formed | `sleep_wf`, `fireNext_wf`, `advance_wf`, `cancel_wf`, `empty_wf` | proved |
| staged = batched on the fire list | `iterate_eq_advance` | proved |
| infinity never fires; zero registers nothing | `inf_never_fires`, `sleep_zero`, `sleep_registers` | proved |
| determinism | by construction (functions; no clock read inside `advance`) | — |

Executed witnesses (`#guard`, `W := Nat`): equal deadlines fire in registration order; the
first fire stages `now` at 10 while the target is 25; a sleep registered after the first fire
is due in the same advance (`[1, 2, 4, 3]`); `cancel 1` removes registration 1, which is
waiter 2 (the token is the handle, not the waiter); infinity and zero as stated; the
registration number is the park token.

## 4. The machine seam (owed, not built)

* `W := FiberId × Nat`; `Store.due` feeds `RunInterp.dueResumes` (`Fibers.lean:373`, `:1380`)
  with `Prim.success Val.unit` — `sleep` resumes exactly as `deferredAwait` does; the machine
  changes nowhere.
* Two rows: `clock.sleep : Time → unit` (`async`, parks on the token `sleep` answers, `none` =
  answers at once) and `clock.now : unit → nat` (`sync`). `timeout`/`delay` are programs.
* One decision: `RunDecision.advance k` = `adjust`; meaning = the staged loop `fireNext`,
  `flush`, … , `finish`, spelled by the host loop (`Lib/HostLoop.lean`, host-frontier L3).
* The tape-adequacy row (substrate Q2's discipline): a witness table under rc.112's
  `TestClock` for `sleep`/`delay`/`timeout`/`raceFirst`, equal deadlines, a sleep inside a
  woken fiber, a cancelled sleep (finding 2 will show the divergence), `sleep 0` (finding 1).

## 5. Refusal rows

R1 `setTime` backwards. R2 `TestClock` keeps cancelled sleeps. R3 `sleep d ≤ 0` yields on the
live clock only. R4 the live clock's ceiling, chaining, drift, the browser floor. R5 `Nanos`
durations round at the row. R6 negative durations fold to zero at the row.

## 6. Not claimed

No theorem relates this store to rc.112's `TestClock` (that is the witness table of §4). No
theorem about the machine with the rows installed (the seam is stated, not compiled). Nothing
about wall-clock time, ever.
