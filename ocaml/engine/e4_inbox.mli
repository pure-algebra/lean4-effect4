(* e4_inbox.mli — a domain's run queue: the wake-ups and control messages of one worker.

   The design (§1.2.1) says "verbatim + a new .mli" and gives no text for it, so THIS
   INTERFACE IS DERIVED from the module's public face as `git:14e6835:ocaml/link/e4_inbox.ml` exposes it
   at 7d53312 (every top-level value of that file). The laws I1-I3 are at the head of
   e4_inbox.ml. *)

type 'a t
(** A worker's run queue. Host-level and mutable: never reachable from a saved machine. *)

val create : unit -> 'a t
(** An open, empty inbox. *)

val push : 'a t -> 'a -> bool
(** [push t x] appends [x] and returns [true]; on a closed inbox it queues nothing and
    returns [false]. Unbounded while open: I1 says a wake is never refused. I1, I3. *)

val pop : 'a t -> 'a option
(** The next element in push order, blocking until one arrives or the inbox is closed;
    [None] only when the inbox is closed and drained. I2, I3. *)

val pop_opt : 'a t -> 'a option
(** As {!pop} without blocking: [None] when the inbox is empty, closed or not. *)

val close : 'a t -> unit
(** Refuse further pushes and wake every blocked {!pop}. Idempotent. I3. *)

val length : 'a t -> int
val is_closed : 'a t -> bool

val stats : 'a t -> int * int
(** [(pushed, popped)], taken under the lock. *)
