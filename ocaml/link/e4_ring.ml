(* e4_ring.ml — the per-domain event ring: seq-tagged rows, single writer, bounded.

   What it is: where a worker domain puts the event rows each step produced, tagged with
   the domain, the machine, the global sequence number of the decision and the decision
   itself; any domain may read it by cursor. Rows are strings: this is how events leave
   the owning domain (the memory rule).
   Depends on: nothing in the library.

   Properties:
     G1  Single writer, checked. The first domain to `append` owns the write side; an
         `append` from any other domain raises `Invalid_argument`. [by construction
         (the check is in `append`); tested: ring-single-writer]
     G2  Bounded at `capacity`; overflow drops the oldest entries and marks the gap for a
         reader whose cursor is behind them (`gap = true`); it never reorders or
         renumbers. [by construction; tested: ring-bounded-gap]
     G3  A read at cursor `c` returns the entries with index >= max(c, oldest retained),
         in index order, and `next` is the cursor for the next read; a read at `next`
         is empty until the next append. [by construction; tested: ring-bounded-gap] *)

type entry = { domain : int; machine : int; seq : int; decision : string; row : string }
type read = { entries : entry list; next : int; gap : bool }

type t = {
  domain : int;
  capacity : int;
  mu : Mutex.t;
  buf : entry option array;
  mutable written : int;
  mutable writer : int option; (* the writer's Domain.id *)
}

let create ~domain ~capacity =
  if capacity < 1 then invalid_arg "E4_ring.create: capacity must be at least 1";
  { domain; capacity; mu = Mutex.create (); buf = Array.make capacity None; written = 0; writer = None }

let domain t = t.domain
let capacity t = t.capacity

let append t e =
  Mutex.protect t.mu (fun () ->
      let me = (Domain.self () :> int) in
      (match t.writer with
      | None -> t.writer <- Some me
      | Some w -> if w <> me then invalid_arg "E4_ring.append: a second writer domain");
      t.buf.(t.written mod t.capacity) <- Some e;
      t.written <- t.written + 1)

let read t ~cursor =
  Mutex.protect t.mu (fun () ->
      let oldest = max 0 (t.written - t.capacity) in
      let from = max (max cursor 0) oldest in
      let entries =
        List.init (max 0 (t.written - from)) (fun i -> Option.get t.buf.((from + i) mod t.capacity))
      in
      { entries; next = t.written; gap = cursor < oldest })

let written t = Mutex.protect t.mu (fun () -> t.written)
