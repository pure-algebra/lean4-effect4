(* e4_trigger.ml — the one-shot cross-domain wake, as a three-state CAS.

   What it is: Picos' `Trigger` with the closure replaced by a mailbox address (design
   2026-09-08-engine-a3-queue-query.md §1.2.3, borrow #9). Signalling is "enqueue a Resume
   row", never "run user code". The CAS decides only WHO posts, never WHAT happens: the
   resume is a row on the tape, so this adds no off-tape choice. Without it, a foreign
   domain signalling twice posts a duplicate row and the tape diverges on replay (S4).
   Depends on: nothing (one `Atomic.t` over a three-constructor state).

   THE THREE STATES, and the only transitions there are:

       Initial --await addr-->  Awaiting addr --signal--> Signaled   (posts addr, once)
       Initial --signal------>  Signaled                             (posts nothing)

   No transition leaves `Signaled` (TR1) and none carries an address out of it (TR3).

   Properties (Picos states these as ERRORS, not best practice -- adopted verbatim):
     TR1 Once signaled it never changes state (signal is idempotent-or-error). A second
         `signal` is a no-op that posts nothing, and an `await` after a signal answers
         `Already_signaled` and stores no address.
         [by construction (every transition is a `compare_and_set` whose expected value was
         just read, and the `Signaled` arm has no successor); tested: trigger-once,
         trigger-double-signal]
     TR2 Only the owner may await, and twice is an error. A second `await` on a trigger
         already in `Awaiting` raises `Invalid_argument`: a violated precondition is an
         exception, not a `result` (Mirage's rule, design §1.2.2 S5).
         [by construction; tested: trigger-once]
     TR3 A signaled trigger holds no value: signaled triggers must not accumulate. The
         address is handed to `post` by the winning `signal` and is dropped from the state
         in the same transition, so a retained signaled trigger keeps nothing alive.
         [by construction (`Signaled` is a constant constructor); tested: trigger-once]
     TR4 The post runs with NEITHER effect NOR exception handlers installed and must return
         fast; `post` is `E4_mailbox.push`, which is bounded and refuses. This module
         installs no handler and does not catch: an exception from `post` propagates to the
         signaller, on a trigger that is already `Signaled`, so no second post can happen.
         [stated; `post` is the caller's, so this is a duty on the caller]

   EXACTLY ONE POST. `signal` posts iff it is the `compare_and_set` that moved the trigger
   out of `Awaiting`. Two domains signalling the same awaited trigger therefore make exactly
   one post between them (S4), and a trigger signalled before it was awaited makes none --
   the awaiter learns it by the `Already_signaled` answer instead. *)

type addr = { machine : int; fiber : int; token : int }
type state = Initial | Awaiting of addr | Signaled
type t = { st : state Atomic.t }

let create () = { st = Atomic.make Initial }
let state t = Atomic.get t.st
let is_signaled t = match Atomic.get t.st with Signaled -> true | Initial | Awaiting _ -> false

let rec await t addr =
  match Atomic.get t.st with
  | Signaled -> `Already_signaled
  | Awaiting _ -> invalid_arg "E4_trigger.await: already awaited (TR2)"
  | Initial as current -> if Atomic.compare_and_set t.st current (Awaiting addr) then `Awaiting else await t addr

let rec signal t ~post =
  match Atomic.get t.st with
  | Signaled -> () (* TR1 *)
  | Initial as current -> if Atomic.compare_and_set t.st current Signaled then () else signal t ~post
  | Awaiting addr as current ->
      (* Only the CAS winner posts, so a double signal posts one row (S4), and the address
         is gone from the state before `post` runs (TR3). *)
      if Atomic.compare_and_set t.st current Signaled then post addr else signal t ~post
