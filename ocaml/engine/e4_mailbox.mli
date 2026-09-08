(* e4_mailbox.mli — the bounded FIFO of decisions, one per machine.

   The design (2026-09-08-engine-a3-queue-query.md §1.2.1) says "verbatim + a new .mli" and
   gives no text for it, so THIS INTERFACE IS DERIVED from the module's public face as
   `ocaml/link/e4_mailbox.ml` exposes it at 7d53312 (every top-level value of that file),
   with `stats` widened by the B-Q4a counter. Nothing is hidden that `link/` used and
   nothing is added that it did not have.

   The laws M1-M5 and the two changes (Q-A3-8's broadcast placement, B-Q4a's counter) are
   stated at the head of e4_mailbox.ml. *)

type 'a t
(** A mailbox. Host-level and mutable: never reachable from a saved machine (brief rule 3). *)

type stats = {
  pushed : int;        (** accepted pushes *)
  popped : int;        (** elements handed to a `pop_batch` *)
  refused : int;       (** M2: pushes refused at the bound; no element was dropped *)
  wakes : int;         (** M4: calls of the `wake` callback *)
  contended : int;     (** B-Q4a: pushes whose `Mutex.try_lock` failed, of `pushed + refused` *)
  length : int;        (** elements waiting now *)
}

val create : ?wake:(unit -> unit) -> bound:int -> unit -> 'a t
(** [create ?wake ~bound ()] is an empty mailbox holding at most [bound] elements. [wake] is
    the host's run-queue callback, called under the lock as M4 says.
    @raise Invalid_argument if [bound < 1]. *)

val bound : 'a t -> int
(** M2's bound. A constant of the mailbox, never [max_int]. *)

val push : 'a t -> 'a -> (unit, [ `Full ]) result
(** [push t x] appends [x], or refuses with [Error `Full] at the bound and changes nothing.
    M1, M2. A refusal is a `result` a caller can act on, never a drop and never an
    exception. *)

val push_with : 'a t -> (unit -> 'a) -> (unit, [ `Full ]) result
(** As {!push}, with the element built by the thunk UNDER THE LOCK and after the bound
    check, so a sequence number taken inside it is strictly increasing in queue order and a
    refused push takes no number. M5. *)

val pop_batch : 'a t -> max:int -> 'a list
(** The next [max] elements in push order, or fewer; the empty list when the mailbox is
    empty. The single consumer's only reader. M1, M3, M4.
    @raise Invalid_argument if [max < 1]. *)

val wait : 'a t -> unit
(** Block until the mailbox is non-empty (the single-consumer case with no run queue). *)

val length : 'a t -> int
val is_empty : 'a t -> bool

val stats : 'a t -> stats
(** A snapshot of the counters, taken under the lock. *)
