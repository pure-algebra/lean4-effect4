(* Lcnf_array -- Lean's `Array` as the route spells it: a persistent chunked vector, and the one
   owner of that structure in the estate (decision D-3).

   The carrier has frozen chunks under a Map and an open tail, most recent first.
   E4_log and E4_trace both use this owner. The builtin rows of OCaml5.Lcnf.Builtins
   spell Lean's Array and ByteArray through it.

   Depends on: the standard library (Map, Array, List).

   Properties:
   V1  Append-only reads: `get t i` never changes for a value `t`, and `push` and `set_exn` answer
       a new value; every value a caller keeps answers as it did, whatever is built from it
       later.                                                           tested (test_lcnf)
   V2  Dense: `get t i` is `Some` exactly for `0 <= i < length t`.     tested (test_lcnf)
   V3  Order: `to_list` is the elements in index order, and `fold` visits them ascending.
                                                                        tested (test_lcnf, test_array_conversion)
   V4  Frozen: no array a value can reach is written after the operation that created it. `push`
       fills a fresh chunk, `set_exn` writes a copy of the one chunk it changes, and `replicate`
       shares one chunk that nothing writes. So a retained value and its siblings keep their
       observations after later updates (the refactor plan's rule 8, R3-C-5).
                                                                        by construction; tested
   V5  `get_exn` and `set_exn` take an index the caller has proved in range, as Lean's `uget`,
       `getInternal` and `uset` do; outside it they raise `Invalid_argument`.
                                                                        tested (test_lcnf)
   V6  Costs: `push` amortised O(1) (one cons, and every `chunk_size` pushes one array fill and
       one `Map` insertion); `get`, `get_exn` and `set_exn` O(log (n / chunk_size)) in a frozen
       chunk and O(chunk_size) in the open one; `length` O(1); `fold`, `to_list`, `of_list` and
       `append_list` O(n); `replicate n` O(n / chunk_size + chunk_size).  by construction *)

type 'a t

val chunk_size : int
(** 256, a named constant (no bound is taken from [max_int]). *)

val empty : 'a t

val with_capacity : int -> 'a t
(** Lean's [Array.mkEmpty] and [Array.emptyWithCapacity]: the capacity is a hint, and the answer
    is [empty]. *)

val length : 'a t -> int
val is_empty : 'a t -> bool

val push : 'a t -> 'a -> 'a t
(** The vector with the element appended: Lean's [Array.push]. *)

val get : 'a t -> int -> 'a option

val get_exn : 'a t -> int -> 'a
(** Lean's [Array.uget] and [Array.getInternal], whose index is proved in range.
    @raise Invalid_argument outside [0, length). *)

val set_exn : 'a t -> int -> 'a -> 'a t
(** The vector with the element at the index replaced: Lean's [Array.uset], whose index is proved
    in range. The answer is a new value; the argument is unchanged (V1, V4).
    @raise Invalid_argument outside [0, length). *)

val slice : 'a t -> from:int -> upto:int -> 'a list
(** The half-open range, in index order. Clamped to [0, length]; empty when [upto <= from]. *)

val fold : 'a t -> init:'b -> f:(int -> 'a -> 'b -> 'b) -> 'b
(** In index order, ascending, with each element's index. *)

val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
(** [fold] in the argument order of [List.fold_left]. *)

val to_list : 'a t -> 'a list
(** Lean's [Array.toList]. Uses a temporary array within host capacity and a list fold above it. *)

val to_list_with_capacity : capacity:int -> 'a t -> 'a list
(** The same conversion with a smaller temporary-array capacity, for the allocation controls.
    The capacity never exceeds either host array bound. It does not bound the returned list. *)

val of_list : 'a list -> 'a t
(** Lean's [Array.mk] and [List.toArray]. *)

val append_list : 'a t -> 'a list -> 'a t
(** The vector with the list's elements appended in order: Lean's [Array.appendList]. *)

val replicate : int -> 'a -> 'a t
(** [n] copies of the element, [empty] when [n <= 0]: Lean's [Array.replicate]. *)
