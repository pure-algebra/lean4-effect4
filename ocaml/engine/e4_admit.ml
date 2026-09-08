(* e4_admit.ml — the admission predicate, consulted before popping.

   What it is: the rule the host applies BEFORE `pop_batch`, so a refusal is a decision the
   host took from state it already had, not a failure discovered after a push (design
   2026-09-08-engine-a3-queue-query.md §1.2.3, S2, borrow #23 — Hack's serverMain computes
   the admissible client kind from server state before selecting). Today the estate accepts
   every decision until a mailbox is full; this is the missing rule.
   Depends on: nothing (three ints in, one of three constructors out).

   THE RULE. `room` is what the mailbox can still take once the work already accepted for it
   is counted:

       room = mailbox_bound - mailbox_len - in_flight        (clamped at zero)

   and the answer is the band `room` falls in:

       room <= 0                     None_now        nothing is admitted
       0 < room <= priority_reserve  Priority_only   the last `priority_reserve` slots are
                                                     kept for priority traffic
       room > priority_reserve       Any

   `priority_reserve` is a NAMED CONSTANT in this file, never `max_int` and never a fraction
   of a bound a caller could vary at run time (trap #17: a bound taken from `max_int` makes
   the same program admit differently on a 63-bit and a 31-bit host). Negative or oversized
   arguments are clamped, not refused: `of_state` is total, so the admission rule can never
   itself raise on the path that decides whether to accept work.

   Properties:
     A1  A pure function of the saved host state. No clock, no randomness, no atomic hint.
         The rejection of an atomic length hint is explicit (survey §4.6): a refusal is a
         decision, so it must not be timing-dependent.
         [by construction (this file names neither `Unix`, `Random`, `Atomic` nor `Mutex`);
         tested: admit-pure]
     A2  Monotone in room: more room never admits less. Under the total order
         None_now < Priority_only < Any, `of_state` is non-decreasing as `room` grows, and
         `admits _ ~priority` is non-decreasing in that order for each priority.
         [by construction (the bands are an ascending partition of `room`);
         tested: admit-monotone] *)

type t = Any | Priority_only | None_now

(* The slots kept back for priority traffic. A named constant, as every integer bound in the
   engine is (design §1, "every integer bound is a named constant in the file"). *)
let priority_reserve = 4

let of_state ~mailbox_len ~mailbox_bound ~in_flight =
  let room = mailbox_bound - mailbox_len - in_flight in
  if room <= 0 then None_now else if room <= priority_reserve then Priority_only else Any

let admits t ~priority =
  match t with Any -> true | Priority_only -> priority | None_now -> false
