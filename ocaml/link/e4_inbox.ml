(* e4_inbox.ml — a domain's run queue: the wake-ups and control messages of one worker.

   What it is: an unbounded FIFO with a blocking `pop`, `Mutex` + `Condition`. Every
   element is small (a machine id, or a control record holding only ints, strings and
   OCaml queues); a Lean value never travels through it. Unbounded on purpose: a wake
   that could be refused would strand a decision that was already accepted into a
   mailbox; the length is bounded anyway by the mailboxes (M4: at most one outstanding
   wake per mailbox) plus the control messages in flight.
   Depends on: nothing in the library.

   Properties:
     I1  FIFO, and `push` never refuses while the inbox is open. [by construction;
         tested: inbox-fifo]
     I2  `pop` blocks until an element is present or the inbox is closed, and returns
         each element exactly once. [by construction; tested: inbox-fifo]
     I3  After `close`, `push` returns false (the element is not queued) and `pop` drains
         what is left, then returns `None`. [by construction; tested: inbox-close] *)

type 'a t = {
  mu : Mutex.t;
  cv : Condition.t;
  q : 'a Queue.t;
  mutable closed : bool;
  mutable pushed : int;
  mutable popped : int;
}

let create () =
  { mu = Mutex.create (); cv = Condition.create (); q = Queue.create (); closed = false; pushed = 0; popped = 0 }

let push t x =
  Mutex.protect t.mu (fun () ->
      if t.closed then false
      else begin
        Queue.push x t.q;
        t.pushed <- t.pushed + 1;
        Condition.broadcast t.cv;
        true
      end)

let pop t =
  Mutex.protect t.mu (fun () ->
      while Queue.is_empty t.q && not t.closed do
        Condition.wait t.cv t.mu
      done;
      if Queue.is_empty t.q then None
      else begin
        t.popped <- t.popped + 1;
        Some (Queue.pop t.q)
      end)

let pop_opt t =
  Mutex.protect t.mu (fun () ->
      if Queue.is_empty t.q then None
      else begin
        t.popped <- t.popped + 1;
        Some (Queue.pop t.q)
      end)

let close t =
  Mutex.protect t.mu (fun () ->
      t.closed <- true;
      Condition.broadcast t.cv)

let length t = Mutex.protect t.mu (fun () -> Queue.length t.q)
let is_closed t = Mutex.protect t.mu (fun () -> t.closed)
let stats t = Mutex.protect t.mu (fun () -> (t.pushed, t.popped))
