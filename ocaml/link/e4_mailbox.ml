(* e4_mailbox.ml — a bounded FIFO of decisions, one per machine.

   What it is: the queue between the senders (router, sessions, other machines, the
   machine's own event-loop rule) and the one worker that owns the machine. Many
   producers, one consumer, `Mutex` + `Condition` from the OCaml 5 standard library.
   Depends on: nothing in the library (polymorphic in the element).

   Properties:
     M1  FIFO. `pop_batch` returns elements in push order and in no other.
         [by construction (one `Queue` under one mutex); tested: mailbox-fifo]
     M2  Bounded, refuse never drop. A push at `bound` elements returns `Error `Full` and
         leaves the queue unchanged; no element is ever discarded.
         [by construction; tested: mailbox-bounded-refuse]
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
         takes no number. [by construction; tested: mailbox-stamp-monotone] *)

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
}

type stats = { pushed : int; popped : int; refused : int; wakes : int; length : int }

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
  }

let bound t = t.bound

let push_with t make =
  Mutex.protect t.mu (fun () ->
      if Queue.length t.q >= t.bound then begin
        t.refused <- t.refused + 1;
        Error `Full
      end
      else begin
        let x = make () in
        Queue.push x t.q;
        t.pushed <- t.pushed + 1;
        Condition.broadcast t.nonempty;
        (match t.wake with
        | Some wake when not t.wake_outstanding ->
            t.wake_outstanding <- true;
            t.wakes <- t.wakes + 1;
            wake ()
        | _ -> ());
        Ok ()
      end)

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
      { pushed = t.pushed; popped = t.popped; refused = t.refused; wakes = t.wakes; length = Queue.length t.q })
