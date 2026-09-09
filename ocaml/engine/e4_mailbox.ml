(* e4_mailbox.ml — a bounded FIFO of decisions, one per machine.

   What it is: the queue between the senders (router, sessions, other machines, the
   machine's own event-loop rule) and the one worker that owns the machine. Many
   producers, one consumer, `Mutex` + `Condition` from the OCaml 5 standard library.
   Depends on: nothing in the library (polymorphic in the element).

   Copied from git:14e6835:ocaml/link/e4_mailbox.ml (as it stood at 7d53312); changes: broadcast moved outside the
   critical section (Q-A3-8), and a `Mutex.try_lock`-failure counter on the push path
   (bench cell B-Q4a, 2026-09-08-engine-a3-queue-query.md §4.3) reported as
   `stats.contended`. Both are additive: M1-M5 hold with the same witnesses.

   Properties:
     M1  FIFO. `pop_batch` returns elements in push order and in no other.
         [by construction (one `Queue` under one mutex); tested: mailbox-fifo]
     M2  Bounded, refuse never drop. A push at `bound` elements returns `Error `Full` and
         leaves the queue unchanged; no element is ever discarded.
         [by construction; tested: mailbox-bounded-refuse, mailbox-refuse-never-drop]
     M3  Exactly once. Every accepted element is returned by exactly one `pop_batch`.
         [by construction (`pop_batch` is the only reader); tested: mailbox-exactly-once,
         four producer domains against one consumer]
     M4  The wake is one-shot per drain cycle. A push when no wake is outstanding calls
         `wake` exactly once, under the lock; further pushes do not; a `pop_batch` that
         leaves the mailbox non-empty re-wakes (the machine goes to the back of the run
         queue: round-robin fairness); one that drains it re-arms the wake.
         [by construction; tested: mailbox-wake]
     M5  `push_with`'s thunk runs under the lock, after the bound check, so a sequence
         number taken inside it is strictly increasing in queue order, and a refused push
         takes no number. [by construction; tested: mailbox-stamp-monotone]

   Q-A3-8, the one behaviour change, and why it is still correct. In `link/` the
   `Condition.broadcast t.nonempty` of an accepted push runs INSIDE the critical section
   (link/e4_mailbox.ml:68); here it runs after the mutex is released, so a woken `wait`
   does not immediately block again on the lock the waker still holds (survey §4.6,
   borrow #28). No wake is lost: a `wait`er holds `t.mu` from its `Queue.is_empty` test
   until `Condition.wait` atomically releases it, and an `enqueue` needs that same mutex,
   so a push cannot slip between a waiter's test and its wait. The `wake` callback of M4
   stays under the lock, where M4 states it.

   B-Q4a, the counter. `contention` counts the pushes whose `Mutex.try_lock` failed and
   which therefore blocked in `Mutex.lock`; the denominator is `pushed + refused` (every
   push attempt takes the lock, accepted or refused). The fast path is one `try_lock`,
   which is what `Mutex.lock` does first anyway, so the counter costs an atomic increment
   on the contended path only. `pop_batch`, `wait`, `length` and `stats` are unchanged and
   are not counted: B-Q4a names the push path. *)

type 'a t = {
  mu : Mutex.t;
  nonempty : Condition.t;
  q : 'a Queue.t;
  bound : int;
  wake : (unit -> unit) option;
  mutable wake_outstanding : bool;
  mutable pushed : int;
  mutable popped : int;
  mutable refused : int;
  mutable wakes : int;
  contention : int Atomic.t;
}

type stats = { pushed : int; popped : int; refused : int; wakes : int; contended : int; length : int }

let create ?wake ~bound () =
  if bound < 1 then invalid_arg "E4_mailbox.create: bound must be at least 1";
  {
    mu = Mutex.create ();
    nonempty = Condition.create ();
    q = Queue.create ();
    bound;
    wake;
    wake_outstanding = false;
    pushed = 0;
    popped = 0;
    refused = 0;
    wakes = 0;
    contention = Atomic.make 0;
  }

let bound t = t.bound

(* The push path's lock: `Mutex.protect` with the contended acquisitions counted (B-Q4a).
   The counter is an `Atomic` because the increment happens before the lock is held. *)
let protect_counting t f =
  if not (Mutex.try_lock t.mu) then begin
    Atomic.incr t.contention;
    Mutex.lock t.mu
  end;
  Fun.protect ~finally:(fun () -> Mutex.unlock t.mu) f

let push_with t make =
  let answer =
    protect_counting t (fun () ->
        if Queue.length t.q >= t.bound then begin
          t.refused <- t.refused + 1;
          Error `Full
        end
        else begin
          let x = make () in
          Queue.push x t.q;
          t.pushed <- t.pushed + 1;
          (match t.wake with
          | Some wake when not t.wake_outstanding ->
              t.wake_outstanding <- true;
              t.wakes <- t.wakes + 1;
              wake ()
          | _ -> ());
          Ok ()
        end)
  in
  (* Q-A3-8: outside the critical section. *)
  (match answer with Ok () -> Condition.broadcast t.nonempty | Error `Full -> ());
  answer

let push t x = push_with t (fun () -> x)

let pop_batch t ~max =
  if max < 1 then invalid_arg "E4_mailbox.pop_batch: max must be at least 1";
  Mutex.protect t.mu (fun () ->
      let rec take n acc =
        if n = 0 || Queue.is_empty t.q then List.rev acc else take (n - 1) (Queue.pop t.q :: acc)
      in
      let batch = take max [] in
      t.popped <- t.popped + List.length batch;
      (match t.wake with
      | Some wake when not (Queue.is_empty t.q) ->
          (* still work here: stay outstanding, and go to the back of the run queue *)
          t.wakes <- t.wakes + 1;
          wake ()
      | _ -> t.wake_outstanding <- false);
      batch)

(* Block until the mailbox is non-empty (the single-consumer case without a run queue). *)
let wait t =
  Mutex.protect t.mu (fun () ->
      while Queue.is_empty t.q do
        Condition.wait t.nonempty t.mu
      done)

let length t = Mutex.protect t.mu (fun () -> Queue.length t.q)
let is_empty t = length t = 0

let stats t =
  Mutex.protect t.mu (fun () ->
      {
        pushed = t.pushed;
        popped = t.popped;
        refused = t.refused;
        wakes = t.wakes;
        contended = Atomic.get t.contention;
        length = Queue.length t.q;
      })
