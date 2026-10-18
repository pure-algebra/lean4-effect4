(* e4_log.mli — the append-only log: a persistent chunked vector.

   What it is: the public log as a projection with its own codec (direction v2 item 9;
   `RunEvent` stays internal).  Its key is the TRACE INDEX -- dense, monotone, and the
   reading axis of the whole design language ("a viewer may imply 'before in the reading'
   from position and may imply nothing else", 2026-09-08-design-language.md §4.1).  A dense
   monotone key does not want a balanced tree: the carrier is `chunk_size` frozen arrays
   under a `Map` from chunk number, plus an open tail list.
   Measured (2026-09-08-engine-a3-queue-query.md §6.3): append 76 M rows/s and random get
   4.3 M/s at 1e6 rows, against `Map.Make(Int)` at 6.5 M/s and 1.6 M/s.  The Lean shape
   `trace ++ events` (RunMachine.emit (src/Effect4/Machine/Fibers.lean)) needs 141 ms for TEN THOUSAND
   rows.
   Depends on: effect4_lcnf (Lcnf_array, the carrier).

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
         [by construction (lcnf_array.mli V4); tested: log-frozen]

   The carrier is `Lcnf_array` (ocaml/lcnf/lcnf_array.mli).
   The log and the machine trace share that persistent vector. *)

(** One canonical event row.  Bytes are the identity; the sexp face is beside them, never an
    address (2026-09-07-ocaml-proposals.md §0.2). *)
type row = string

(** {1 The log} *)

type t

(** 256, a named constant in the file (trap #17: no bound is ever taken from [max_int]). *)
val chunk_size : int

val empty : t
val length : t -> int
val append : t -> row -> t

(** Appends in list order; this is the shape `RunMachine.emit` has
    (RunMachine.emit (src/Effect4/Machine/Fibers.lean)), so that the index (`E4_logindex`) can be fed
    by the SAME call and never by a rescan (A3 §1.4d). *)
val append_all : t -> row list -> t

val get : t -> int -> row option
val slice : t -> from:int -> upto:int -> row list
val fold : t -> init:'a -> f:(int -> row -> 'a -> 'a) -> 'a
val to_list : t -> row list
val of_list : row list -> t
