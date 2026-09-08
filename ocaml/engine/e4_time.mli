(* e4_time.mli — the logical clock: ticks, deadlines, and the only motion the clock has.

   What it is: the tick unit and the clock of the timer store (lane Q2 of
   docs/research/2026-09-08-engine-a3-queue-query.md §3; the type `time` of §1.1.3 lives
   here so that `E4_timers` and any later user of a deadline share one algebra). The
   owner's logical-timer ruling (2026-09-04-effectful-streams-mechanization.md §8 "no
   physical clock", carried into 2026-09-07-grill-agenda.md §3 row Q6): there is NO physical
   clock; `now` is a tick counter; timers are deadline-ordered; `advance (by : Nat)` is the
   only motion of the clock and it is a decision on the tape. There is no `clockAdjust` and
   no `set_time`.

   The transcription source is workshop/Timer/Timer.lean:72-126 (`Effect4.Timer.Time`:
   `fin`/`inf`, `le`, `lt`, `add`) — this module is that carrier in OCaml, with the two
   host-profile bounds Lean's `Nat` does not need.
   Depends on: nothing (Stdlib only).

   Properties:
     C1  The tick unit is the millisecond (workshop Timer.lean:59-61, R5: sub-millisecond
         `Nanos` round at the row) and the domain of a tick is [0, max_deadline_ms].
         Every tick this module returns is in that domain.
         [by construction; tested: timers-edges]
     C2  `now` moves only through {!advance_to} / {!advance_by}, and never backwards: a
         target below `now` raises Invalid_argument, never a silent clamp. This is refusal
         R1 (workshop Timer.lean:31-32, "`setTime` is not a decision of this store") and it
         is what makes `advance_now_mono` / `fireNext_now_mono` true of the carrier.
         [by construction; tested: timers-now-monotone, timers-mutation-advance-backwards]
     C3  `advance_by c ~by` = `advance_to c ~target:(now c + by)`. `by` is the shape the
         decision alphabet has (`RunDecision.advance (by : Nat)`, grill agenda §3 call 3),
         so a negative `by` is the same refusal as a backwards target.
         [by construction; tested: timers-now-monotone]
     C4  No physical clock: `Unix.gettimeofday`, `Sys.time` and every other host clock are
         absent from this file and from `e4_timers.ml` (survey trap #8 — the only place a
         host clock may appear in the engine is a HOST deadline, and neither file has one).
         [by construction; tested: grep, recorded in the lane receipt]
     C5  `Inf` is above every finite time; `add now Inf = Inf`; a finite `add` that would
         leave the domain is refused AT THE ROW, never wrapped or clamped. The bound is the
         named constant below and never `max_int` (trap #17: a bound read off `max_int`
         makes the same program refuse different tables on a 63-bit and a 31-bit host).
         [by construction; tested: timers-edges]
     C6  Persistence: `clock` is an immediate integer (`private int`), so a saved machine
         holding one holds no mutable structure (brief rule 3).
         [by construction; tested: timers-persistent]

   Refused: `set_time` / `clockAdjust` (R1). Refused: a negative duration folded silently to
   zero — workshop R6 says the fold happens AT THE ROW, so the store refuses one.
   Refused: any bound taken from `max_int` (C5). *)

type t =
  | Fin of int  (** milliseconds; in [0, {!max_deadline_ms}] *)
  | Inf         (** `Duration.infinity` (`Duration.ts:788-794`) *)

val max_deadline_ms : int
(** The largest admissible finite deadline and the largest admissible tick: 1_000_000_000 ms
    (11 days 13 h 46 min). Chosen so that it, and `max_deadline_ms + 1` (the internal
    representation of {!Inf} inside `E4_timers`), are representable on a 31-bit host
    (`max_int = 2^30 - 1 = 1_073_741_823`), which is what C5 asks of the constant. *)

val is_tick : int -> bool
(** [0, {!max_deadline_ms}]. C1. *)

val wf : t -> bool
(** {!Inf}, or a finite time whose milliseconds are a tick. C1. *)

val le : t -> t -> bool
(** `Time.le` (Timer.lean:80-84): {!Inf} is above everything. *)

val lt : t -> t -> bool
(** `Time.lt` (Timer.lean:86-90). *)

val compare : t -> t -> int
(** The total order {!le} induces; {!Inf} last. No polymorphic compare (STANDARDS §4). *)

val add : int -> t -> t
(** [add now d] is the deadline of a sleep of duration [d] started at tick [now].
    `Time.add` (Timer.lean:97-101). C5.
    @raise Invalid_argument if [now] is not a tick, if [d] is a negative finite duration
    (workshop R6: the fold to zero happens at the row, not here), or if [now + d] would
    exceed {!max_deadline_ms}. *)

val to_string : t -> string
(** For test transcripts and bench tables only; never an identity (brief rule 2). *)

type clock = private int
(** The logical clock: the tick `now`. Immediate, so persistent for free (C6). Read it with
    {!now}; build it only with {!start} / {!of_tick}; move it only with {!advance_to} /
    {!advance_by} (C2). *)

val start : clock
(** Tick 0. `TestClock.make`: `currentTimestamp = 0` (Timer.lean:239-240). *)

val of_tick : int -> clock
(** @raise Invalid_argument unless {!is_tick}. *)

val now : clock -> int
(** The current tick. A free row: no fuel, no tape, no state change. *)

val advance_to : clock -> target:int -> clock
(** The clock at [target]. C2.
    @raise Invalid_argument if [target] is below [now c] (R1) or above {!max_deadline_ms}. *)

val advance_by : clock -> by:int -> clock
(** [advance_to c ~target:(now c + by)]. The decision `advance (by : Nat)`. C3.
    @raise Invalid_argument if [by] is negative or carries the clock past
    {!max_deadline_ms}. *)

val reaches : clock -> int -> bool
(** Whether {!advance_to} would accept this target: [target >= now c && target <=
    max_deadline_ms]. A free row; the caller that needs a rejection instead of an exception
    checks first (the `Map.wf` discipline of `e4_buckets.mli`'s {!of_list}). *)
