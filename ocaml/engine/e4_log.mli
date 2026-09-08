(* e4_log.mli — the append-only log: a persistent chunked vector.

   What it is: the public log as a projection with its own codec (direction v2 item 9;
   `RunEvent` stays internal).  Its key is the TRACE INDEX -- dense, monotone, and the
   reading axis of the whole design language ("a viewer may imply 'before in the reading'
   from position and may imply nothing else", 2026-09-08-design-language.md §4.1).  A dense
   monotone key does not want a balanced tree: the carrier is `chunk_size` frozen arrays
   under a `Map` from chunk number, plus an open tail list.
   Measured (2026-09-08-engine-a3-queue-query.md §6.3): append 76 M rows/s and random get
   4.3 M/s at 1e6 rows, against `Map.Make(Int)` at 6.5 M/s and 1.6 M/s.  The Lean shape
   `trace ++ events` (src/Effect4/Machine/Fibers.lean:585-587) needs 141 ms for TEN THOUSAND
   rows.
   Depends on: nothing (Stdlib.Map only).

   Properties:
     L1  Append-only: `get t i` never changes for an i already written, and `length` only
         grows.  [by construction (frozen chunks); licensed by the fuel-laws "the trace only
         grows"; tested: log-append-only]
     L2  Dense: `get t i` is `Some` for every 0 <= i < length t and `None` otherwise.
         [tested: log-dense]
     L3  Order: `to_list` is `slice ~from:0 ~upto:(length t)` and is emission order.
         [tested: log-order]
     L4  Persistence, as B7: an old `t` still answers the old length.  This is what makes
         `replay_steps` cheap -- an intermediate machine's log is a prefix that shares every
         frozen chunk with the final one.                        [tested: log-persistent]
     L5  Frozen: no array in a `t` is written after the `append` that created it, so a saved
         value holds no mutable structure that anything can observe (brief rule 3).
         [by construction; tested: log-frozen]

   THE CARRIER IS POLYMORPHIC and it is exposed as {!Vec}.  `t` is `row Vec.t` and nothing
   else.  It is exposed for one named reason: `E4_trace` (the machine's own trace carrier,
   e4_trace.mli:57-61) is a reversed accumulator whose `nth_opt` is O(length - i), so a
   viewer walking the reading axis costs O(T^2) on a T-row trace, and `E4_trace` says in so
   many words that "A3 may substitute a finger tree behind this signature".  {!Vec} IS that
   substitution, at O(log (T/256)) per row and O(1) amortised per emit.  Lane Q3 did not edit
   `e4_trace.ml`; lane W did (proposal N2, 2026-09-08-engine-lane-w-delivery.md item 2), so
   `E4_trace.t` IS `'e Vec.t` today and this module has two clients. *)

type row = string
(** One canonical event row.  Bytes are the identity; the sexp face is beside them, never an
    address (2026-09-07-ocaml-proposals.md §0.2). *)

(** {1 The carrier} *)

module Vec : sig
  (** The persistent chunked vector, polymorphic in the element.  {!E4_log.t} is
      [row Vec.t]; `E4_logindex` holds its entries in an [entry Vec.t]; a follow-up may put
      `E4_trace` behind it.  Every array is filled once, at the [append] that promotes a
      full tail, and never written again (L5). *)

  type 'a t

  val empty : 'a t
  val length : 'a t -> int
  val is_empty : 'a t -> bool

  val append : 'a t -> 'a -> 'a t
  (** O(1) amortised: a cons on the open tail, and once every {!E4_log.chunk_size} rows one
      array fill plus one `Map` insertion at depth log(length / chunk_size). *)

  val get : 'a t -> int -> 'a option
  (** O(log (length / chunk_size)) in a frozen chunk, O(chunk_size) in the open tail. *)

  val get_exn : 'a t -> int -> 'a
  (** @raise Invalid_argument outside [0, length). *)

  val slice : 'a t -> from:int -> upto:int -> 'a list
  (** The half-open range, in index order.  Clamped to [0, length]; empty when
      [upto <= from]. *)

  val fold : 'a t -> init:'b -> f:(int -> 'a -> 'b -> 'b) -> 'b
  (** In index order, ascending. *)

  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
end

(** {1 The log} *)

type t

val chunk_size : int
(** 256, a named constant in the file (trap #17: no bound is ever taken from [max_int]). *)

val empty : t
val length : t -> int
val append : t -> row -> t
val append_all : t -> row list -> t
(** Appends in list order; this is the shape `RunMachine.emit` has
    (src/Effect4/Machine/Fibers.lean:585-587), so that the index (`E4_logindex`) can be fed
    by the SAME call and never by a rescan (A3 §1.4d). *)

val get : t -> int -> row option
val slice : t -> from:int -> upto:int -> row list
val fold : t -> init:'a -> f:(int -> row -> 'a -> 'a) -> 'a
val to_list : t -> row list
val of_list : row list -> t
