(* Lcnf_nat -- the natural-number helpers of the rows of `OCaml5.Lcnf.builtins` whose form binds
   a name or checks a domain. A Lean `Nat` is Zarith's `Z.t` (`OCaml5.Lcnf.typeRows`, M4).

   What it is: Lean's total arithmetic where Zarith's differs, and the two narrowings of a natural
   to the target's `int`. Lean's `Nat.sub` and `Nat.pred` stop at zero, and its division and
   remainder are total at a zero divisor. `Z.pow` and the shifts take an `int`, and `Lcnf_array`
   indexes by `int`, so a natural past `max_int` is refused there at a named crossing
   (`Lcnf_crossing`): Lean would compute a number no memory holds, or index past any array. The
   index helpers are the arithmetic of `USize`, the target's `int`. The implementation,
   lcnf_nat.ml, is GENERATED from the reference definitions in `OCaml5.Lcnf.support`
   (`lake exe lcnfgen --support`), which the target evaluator runs too. Until M4 a natural was the
   target's 63-bit `int`, and the product, the power and the left shift stopped at `max_int`.

   Depends on: Zarith (Z), Lcnf_crossing.

   Properties, for naturals `a` and `b` (values of `Z.t` at least zero):
   N1  `sub a b` is `a - b` when `b <= a`, and zero below it; `pred a` is `sub a 1`.
                                                                        tested (test_lcnf)
   N2  `div a b` and `rem a b` are the quotient and the remainder, and `0` and `a` at `b = 0`, as
       Lean's `Nat.div` and `Nat.mod` answer.                           tested (test_lcnf)
   N3  `pow`, `shift_left` and `shift_right` are exact for an exponent or a shift up to
       `max_int`, and refuse a larger one at the arithmetic crossing.   tested (test_lcnf)
   N4  `to_index_exn a` and `to_shift_exn a` are `a` as an `int` when it fits, and refuse at the
       index and the arithmetic crossing otherwise; neither truncates.  tested (test_lcnf)
   N5  `index_add` and `index_sub` are the target's `int` sum and difference of two indices when
       it is an index, and refuse at the index crossing where Lean's `USize` wraps.
                                                                        tested (test_lcnf) *)

(** [a - b], or zero when [b > a]: Lean's [Nat.sub]. *)
val sub : Z.t -> Z.t -> Z.t

(** [a - 1], or zero at zero: Lean's [Nat.pred]. *)
val pred : Z.t -> Z.t

(** The quotient, and zero at a zero divisor: Lean's [Nat.div]. *)
val div : Z.t -> Z.t -> Z.t

(** The remainder, and [a] at a zero divisor: Lean's [Nat.mod]. *)
val rem : Z.t -> Z.t -> Z.t

(** The natural as the target's index type, refused past [max_int] at the index crossing. *)
val to_index_exn : Z.t -> int

(** The natural as an exponent or a shift, refused past [max_int] at the arithmetic crossing. *)
val to_shift_exn : Z.t -> int

(** [a ^ b], exact; [b] past [max_int] is refused at the arithmetic crossing. *)
val pow : Z.t -> Z.t -> Z.t

(** [a * 2 ^ b], exact; [b] past [max_int] is refused at the arithmetic crossing. *)
val shift_left : Z.t -> Z.t -> Z.t

(** [a / 2 ^ b], exact; [b] past [max_int] is refused at the arithmetic crossing. *)
val shift_right : Z.t -> Z.t -> Z.t

(** The sum of two indices, refused past [max_int] at the index crossing. *)
val index_add : int -> int -> int

(** The difference of two indices, refused below zero at the index crossing. *)
val index_sub : int -> int -> int
