(* E4_env — a point's environment: a snoc-shared spine with a cached length
   (docs/research/2026-09-08-engine-prof-chain.md §5.1, finding P-6).

   What it is: the carrier behind `Effect4.Program.Point.env` and
   `Effect4.Machine.Capture.env` (src/Effect4/Program/Compile.lean:127-165).  Lean's field is
   a `List Val` extended at the TAIL — `p.env ++ [v]` in `Point.childWith`, `Point.capture`
   and five inline sites — so every child copies its parent's environment: the second
   n(n-1)/2 of lane PROF's 98.5 % (P-2).  Reversed, the extension is a cons and every prefix
   is physically shared.

   The environment is READ positionally (`env[i]?` in `Program.evalTerm`, `List.length` and
   `List.take` in `blockExit`/`loopExit`), and Lean indexes from the FRONT, so a reversed
   spine must know its length to answer: `len` is maintained incrementally and `get` walks
   `len - 1 - i` cells — the same order of work as `List.get?` on the un-reversed list, from
   the other end.

   This module satisfies the generated functor's `PENV` signature (src/OCaml5/Lcnf/
   Externs.lean `carrierSignatures`) verbatim; `e4_env_list.ml` is its list twin and
   satisfies the same signature.  Both ascriptions are checked in test/prop_point.ml.

   Depends on: the OCaml standard library only (List).

   Representation: { rev : the values, LAST BOUND FIRST; len : the length }.

   Behaviours (each is a named PASS/FAIL line in test/prop_point.ml):
   PE1 to_list empty = [] and to_list (snoc e v) = to_list e @ [v]            tested
   PE2 snoc is O(1) and allocates one cons + one record; every prefix of the result is
       physically the parent's spine                              by construction; benched
   PE3 get e i = List.nth_opt (to_list e) i for every i, and None outside the range —
       Lean's `env[i]?` (List.get?)                                           tested
   PE4 length e = List.length (to_list e), maintained incrementally, O(1)     tested
   PE5 to_list (take e k) = List.take k (to_list e), including k >= length e (Lean's
       `List.take` clamps), and the result SHARES the tail of the spine       tested
   PE6 persistence: `e` is unchanged by any snoc/take on it                   tested
   PE7 agreement with the list twin on random operation sequences             tested
   Bound: the environment is unbounded in Lean; on this host it is bounded by the heap. *)

type 'a t

val empty : 'a t

val snoc : 'a t -> 'a -> 'a t
(** Bind one more value: [to_list (snoc e v) = to_list e @ [v]], O(1) (PE1, PE2). *)

val append : 'a t -> 'a list -> 'a t
(** [snoc] folded over the list. *)

val get : 'a t -> int -> 'a option
(** Lean's [env[i]?] — index from the front (PE3). *)

val length : 'a t -> int
(** O(1) (PE4). *)

val take : 'a t -> int -> 'a t
(** Lean's [List.take k], clamped at both ends; shares the tail of the spine (PE5). *)

val to_list : 'a t -> 'a list
(** The Lean `Point.env` value.  One reversal, O(length). *)

val of_list : 'a list -> 'a t
(** The inverse of [to_list]; for the tests and for a caller that holds a Lean list. *)
