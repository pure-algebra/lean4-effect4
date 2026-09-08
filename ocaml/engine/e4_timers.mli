(* e4_timers.mli — the timer store as a persistent priority search queue.

   What it is: the carrier of workshop/Timer/Timer.lean's `Store`, keyed by the registration
   number and prioritised by (deadline, seq). `Psq`'s shape (a finite map and a priority queue
   in one: O(log n) by key, O(1) min, O(log n) removal) implemented on two stdlib maps:

       by_prio : (deadline, seq) -> key      -- the priority side; `min` is `min_binding`
       by_key  : key -> (deadline, seq)      -- the map side; `cancel` is two removals

   `psq 0.2.1` is installed and was measured against this (design doc §6.1). It is refused:
   at the realistic table size (n = 1e3) the hand carrier is faster on three of four
   workloads, and the win at n = 1e5 (insert 1.95x, cancel 3.5x, memory 1.25x, against a
   1.53x loss on `pop_due`) does not buy the estate's first third-party edge. Re-open
   condition, stated so it can be met: a timer census showing > 1e4 live timers on one machine
   with a cancel-dominated mix. The swap is one file behind this unchanged .mli.
   Refusal row A3-TIMERS-PSQ.
   Depends on: E4_time (the tick unit and the clock; lane-internal) and Stdlib.Map only;
   polymorphic in the waiter.

   THE INVARIANTS (`wf`):
     TIM-SORT   the priority side is ascending under (deadline, then seq)
     TIM-FRESH  every registration number is below `next_seq`
     TIM-PAST   no registered deadline is before `now`
     TIM-UNIQ   registration numbers are unique, so no two timers share a priority --
                this is what makes the fire order a property of OUR carrier and not of a
                library's documented tie-break
     TIM-BIJ    by_prio and by_key are mutual inverses

   TIM-UNIQ is by construction and not by luck: a registration number is `next_seq` at the
   moment of the `sleep` that took it, `next_seq` only ever increases, and no operation of
   this module ever puts a number back. So the priority `(deadline, seq)` is unique, and
   `min` is a total function of the table rather than of a tie-break rule.

   Properties (the workshop theorem each becomes is in the design doc §2.3):
     T1  now moves only under `advance`/`pop_due`, and never backwards.
         [by construction; = Timer.advance_now, advance_now_mono, fireNext_now_mono;
         tested: timers-now-monotone]
     T2  A timer fires only when now >= deadline, and every due timer fires.
         [= mem_fired_due, not_due_of_mem_rest, fired_exact; tested: timers-due-exact]
     T3  Fire order is deadline, then registration.
         [= fired_sorted, equal_deadline_registration_order, fireNext_earliest;
         tested: timers-fire-order]
     T4  `cancel` removes the entry and it never fires again (the LIVE clock's clearTimeout).
         [= cancel_removes, cancel_keeps, cancel_never_fires; tested: timers-cancel]
     T5  `sleep 0` registers nothing; `sleep Inf` never fires under a finite advance.
         [= sleep_zero, sleep_registers, inf_never_fires; tested: timers-edges]
     T6  Staged = batched: iterating `pop_due` to exhaustion and then `finish` agrees with
         `advance_to` on the fired list, its order, and the final clock.
         [= iterate_eq_advance; tested: timers-staged-eq-batched]
     T7  Persistence, as B7. [by construction; tested: timers-persistent]

   Refused: `clockAdjust` / `set_time` (refusal R1, timer-semantics §5) -- the store models the
   live clock and `now` is monotone; a backwards clock is not a decision of this store.
   Refused: keeping a cancelled sleep in the table (rc.112's TestClock does; refusal R2).
   Refused: any physical clock. `Unix.gettimeofday` never appears in this file, and the only
   place it may appear in the engine is a HOST deadline (survey trap #8).
   Refused: R3 `sleep d <= 0` yields on the live clock only -- this store takes the test
   clock's shape and answers `None`, and the row prepends the yield.
   Refused: R4 the live clock's 2^31-1 ms ceiling, chaining, drift and browser floor (a host
   profile, not semantics). R5 `Nanos` round at the row. R6 negative durations fold to zero
   at the row -- a negative duration reaching this store is an Invalid_argument, not a
   silent zero.

   DEVIATIONS from the design document's text of this .mli, both additive (lane receipt
   docs/research/2026-09-08-engine-lane-q2-delivery.md):
     D1  `type time` carries the equation `= E4_time.t`, so that the lane's clock module and
         this one name ONE type. The constructors and every signature below are unchanged.
     D2  `length` is added beside `size` (the build brief names it); they are the same
         function, O(1). *)

type time = E4_time.t =
  | Fin of int   (** milliseconds; the bound is [max_deadline_ms] below, never [max_int] *)
  | Inf          (** `Duration.infinity` *)

val max_deadline_ms : int
(** The largest admissible finite deadline, a constant in the file (trap #17: a bound taken
    from [max_int] makes the same program refuse different tables on a 63-bit and a 31-bit
    host). Deadlines above it are refused at the row, not clamped. *)

val time_le : time -> time -> bool
val time_lt : time -> time -> bool

val time_add : int -> time -> time
(** [time_add now d] is the deadline of a sleep of [d] started at [now]. `Time.add`.
    @raise Invalid_argument if [d] is a negative finite duration (R6) or if the deadline
    would exceed [max_deadline_ms]. *)

type key = int
(** The registration number. It is also the park token the waiter is parked on
    (workshop #guard: "the registration number is the park token"). *)

type 'w t
(** The timer store: the clock, the counter, the queue. Persistent. *)

val empty : 'w t
(** now = 0, next_seq = 0, no timer. `TestClock.make`. *)

val now : 'w t -> int
val size : 'w t -> int
val length : 'w t -> int
(** D2: the same as {!size}. Both O(1). *)

val is_empty : 'w t -> bool
val next_seq : 'w t -> int

val wf : 'w t -> bool
(** TIM-SORT and TIM-FRESH and TIM-PAST and TIM-UNIQ and TIM-BIJ. Checked in tests, asserted
    nowhere on the hot path. *)

val sleep : 'w t -> time -> 'w -> 'w t * key option
(** `TestClock.sleep`: a zero duration registers nothing and answers [None] (the row resumes
    at once); otherwise the deadline is [now + d], the entry takes the next registration
    number, and that number is the token the waiter parks on. T5.
    @raise Invalid_argument if a finite deadline would exceed [max_deadline_ms], or if the
    duration is negative (R6). *)

val cancel : 'w t -> key -> 'w t
(** `clearTimeout`. A no-op on a key that is not registered. T4. *)

val remove_by_key : 'w t -> key -> 'w t
(** The `Psq` name for {!cancel}; the same function. *)

val mem : 'w t -> key -> bool
val deadline_of : 'w t -> key -> time option
val waiter_of : 'w t -> key -> 'w option

val min : 'w t -> (key * time * 'w) option
(** The earliest timer under (deadline, seq). O(log n) here; O(1) in `Psq`. By TIM-UNIQ there
    is never a tie, so this is a total function of the table and not of a tie-break rule. *)

val pop_due : 'w t -> upto:int -> ((key * int * 'w) * 'w t) option
(** ONE STAGED FIRE (`Timer.fireNext`, TestClock.ts:361-367): if the earliest timer's deadline
    is finite and <= [upto], remove it and return it with the store whose clock has been
    STAGED AT THAT DEADLINE -- not at [upto]. A fiber woken at deadline d that reads the clock
    reads d. T1, T2, T3. *)

val advance : 'w t -> by:int -> 'w t * (key * int * 'w) list
(** The decision `advance (by : Nat)`: [advance_to t ~target:(now t + by)]. The only motion of
    the clock. There is no `advance_to_absolute` and no `clockAdjust`.
    @raise Invalid_argument if [by] is negative (R1) or carries the clock past
    [max_deadline_ms]. *)

val advance_to : 'w t -> target:int -> 'w t * (key * int * 'w) list
(** THE BATCHED FORM (`Timer.advance`): every due timer fired in (deadline, seq) order, and
    the clock at [target] at the end. T6 says this agrees with iterating {!pop_due} on WHICH
    timers fire, in WHAT order, and on the final clock; what differs is what a woken fiber
    does between fires, which is the host loop's business. The host loop uses {!pop_due}.
    @raise Invalid_argument if [target < now t] (refusal R1). *)

val fired : 'w t -> upto:int -> (key * int * 'w) list
(** What an advance to [upto] WOULD fire, without moving anything. A free row (§1.3.4):
    no fuel, no tape, no state change. Total: an [upto] below [now t] answers [[]] rather
    than raising, because a free row never refuses. *)

val to_list : 'w t -> (key * time * 'w) list
(** Priority-ascending: the canonical snapshot order. Two stores with the same [now],
    [next_seq] and [to_list] are equal. Priority-ascending and not key-ascending, because the
    snapshot must not depend on the allocation history of the keys (trap #16). *)

val of_list : now:int -> next_seq:int -> (key * time * 'w) list -> 'w t
(** @raise Invalid_argument if the result would not satisfy {!wf}. *)
