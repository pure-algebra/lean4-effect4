(* e4_quiescence.ml — the count of accepted-but-not-yet-applied work, and the wait for zero.

   What it is: a counter every accepted decision or control message enters (under the
   mailbox lock, so a refused push never counts) and every applied one leaves; the host's
   `run_until_quiescent` waits for it to reach zero. Quiescent means: every mailbox and
   inbox is empty and no step is in flight — nothing anywhere is pending.
   Depends on: nothing in the library (Unix for the timed wait).

   Properties:
     Q1  `outstanding` = enters - leaves, and `leave` below zero raises: a leave without
         an enter is a bug, not a silent underflow. [by construction; tested:
         quiescence-counter]
     Q2  `wait_zero` returns only when outstanding = 0 at some instant after the call,
         and is woken by the `leave` that gets there (no lost wake-up: the check and the
         wait share the mutex). [by construction; tested: quiescence-counter]
     Q3  `wait_zero_for ~seconds` returns `true` under the same condition, `false` at the
         deadline. It polls (the standard library's `Condition` has no timed wait).
         [by construction] *)

type t = {
  mu : Mutex.t;
  cv : Condition.t;
  mutable outstanding : int;
  mutable entered : int;
  mutable left : int;
}

let create () = { mu = Mutex.create (); cv = Condition.create (); outstanding = 0; entered = 0; left = 0 }

let enter t =
  Mutex.protect t.mu (fun () ->
      t.outstanding <- t.outstanding + 1;
      t.entered <- t.entered + 1)

let leave t =
  Mutex.protect t.mu (fun () ->
      if t.outstanding <= 0 then invalid_arg "E4_quiescence.leave: nothing outstanding";
      t.outstanding <- t.outstanding - 1;
      t.left <- t.left + 1;
      if t.outstanding = 0 then Condition.broadcast t.cv)

let outstanding t = Mutex.protect t.mu (fun () -> t.outstanding)
let totals t = Mutex.protect t.mu (fun () -> (t.entered, t.left))

let wait_zero t =
  Mutex.protect t.mu (fun () ->
      while t.outstanding > 0 do
        Condition.wait t.cv t.mu
      done)

let wait_zero_for t ~seconds =
  let deadline = Unix.gettimeofday () +. seconds in
  let rec poll () =
    if outstanding t = 0 then true
    else if Unix.gettimeofday () >= deadline then false
    else begin
      Unix.sleepf 0.0002;
      poll ()
    end
  in
  poll ()
