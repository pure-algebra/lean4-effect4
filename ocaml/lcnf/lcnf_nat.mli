(* Lcnf_nat -- the natural-number helpers of the rows `Nat.mul`, `Nat.pow` and `Nat.shiftLeft`
   while `Nat` is spelled as OCaml's 63-bit `int`: each stops at `max_int`.

   What it is: a wrapping product or power would make `Effect4.Store.Val.wf`'s `… < 2 ^ 64` read
   as `… < 0`, and answer `false` for every value. Stopping at `max_int` keeps such a bound's
   meaning, since every list OCaml can hold is shorter than `max_int` (`ocaml/gen/NOTES.md` §5).
   The three are exact only below `max_int`, which the rows' contracts state
   (`OCaml5.Lcnf.builtins`); slice 2.2b of the refactor plan replaces them with exact arithmetic.
   The target evaluator runs each from its reference definition in `OCaml5.Lcnf.support`.

   Depends on: the standard library only.

   Properties, for naturals `a` and `b`:
   N1  `mul a b` is `a * b` when that product is at most `max_int`, and `max_int` above it. The
       test `b > max_int / a` divides, so no intermediate product overflows.
                                                                        tested (test_lcnf)
   N2  `pow a b` is `a ^ b` when that power is at most `max_int`, and `max_int` above it;
       `pow 0 0` is `1`, as Lean's `Nat.pow` answers.                   tested (test_lcnf)
   N3  `shift_left a b` is `a * 2 ^ b` when that is at most `max_int`, and `max_int` above it:
       the power and the product are both stopped.                      tested (test_lcnf)
   N4  `pow` recurses once for each unit of `b`, so its depth is `b`, and a negative `b` never
       reaches its base case.                                           by construction *)

val mul : int -> int -> int
(** The product of two naturals, stopped at [max_int]. *)

val pow : int -> int -> int
(** The power of two naturals, stopped at [max_int]. *)

val shift_left : int -> int -> int
(** [a * 2 ^ b] for two naturals, stopped at [max_int]. *)
